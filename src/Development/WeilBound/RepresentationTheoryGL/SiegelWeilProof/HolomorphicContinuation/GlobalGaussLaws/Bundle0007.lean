import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FourierZeroN
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0225
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0005

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.HasTemperateGrowthEvalPoly
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

theorem trace_frame {m : ℕ} {M fr : Matrix (Fin m) (Fin m) ℂ} (h1 : IsUnit fr.det) (h2 : frᴴ * M * fr = 1)
    (z : Matrix (Fin m) (Fin n) ℂ) :
    Matrix.trace (zᴴ * M * z) = ((∑ a, ∑ i, ‖(fr⁻¹ * z) a i‖ ^ 2 : ℝ) : ℂ) := by
  set y := fr⁻¹ * z with hy
  have hz : z = fr * y := by rw [hy, Matrix.mul_nonsing_inv_cancel_left _ _ h1]
  have e : zᴴ * M * z = yᴴ * y := by
    rw [hz, Matrix.conjTranspose_mul]
    calc yᴴ * frᴴ * M * (fr * y) = yᴴ * (frᴴ * M * fr) * y := by simp only [Matrix.mul_assoc]
      _ = yᴴ * y := by rw [h2, Matrix.mul_one]
  rw [e, Matrix.trace]
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.conjTranspose_apply, ← Complex.conj_mul']
  rfl

theorem gauss_split {V : HSp D} {τ : D.what₂.Tau} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} (l : D.what₂.Tau → ℝ)
    (hfr : IsTauFrame V τ s ε fr) (z : D.what₂.Tau → Matrix (Fin V.rank) (Fin n) ℂ) :
    gauss V l s z = gs (cLoc l τ) (fr⁻¹ * z τ) * gAway V l s τ z := by
  classical
  unfold gauss gAway gs cLoc
  rw [← Complex.exp_add]
  congr 1
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ τ), trace_frame hfr.1 hfr.2.2 (z τ)]
  have hf : (Finset.univ.filter fun τ' => τ' ≠ τ) = Finset.univ.erase τ := by
    ext x; simp
  rw [hf]
  push_cast
  ring

theorem evalPoly_add {m : ℕ} (p q : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ)
    (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) : evalPoly (p + q) z = evalPoly p z + evalPoly q z := by
  simp [evalPoly]

theorem evalPoly_mul {m : ℕ} (p q : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ)
    (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) : evalPoly (p * q) z = evalPoly p z * evalPoly q z := by
  simp [evalPoly]

theorem evalPoly_C {m : ℕ} (a : ℂ) (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) :
    evalPoly (MvPolynomial.C a : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ) z = a := by
  simp [evalPoly]

theorem evalPoly_X {m : ℕ} (v : D.what₂.Tau × Fin m × Fin n × Bool) (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) :
    evalPoly (MvPolynomial.X v : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ) z =
      if v.2.2.2 then conj (z v.1 v.2.1 v.2.2.1) else z v.1 v.2.1 v.2.2.1 := by
  simp [evalPoly]

theorem eval_bind₁' {σ ι : Type*} (f : σ → ℂ) (g : ι → MvPolynomial σ ℂ) (p : MvPolynomial ι ℂ) :
    MvPolynomial.eval f (MvPolynomial.bind₁ g p) = MvPolynomial.eval (fun i => MvPolynomial.eval f (g i)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

def polyAt {m : ℕ} (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) (P : PX m n) :
    MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ :=
  MvPolynomial.bind₁ (fun k : Fin m × Fin n × Bool => if k.2.2 then
      ∑ a, MvPolynomial.C (star ((fr⁻¹) k.1 a)) * MvPolynomial.X (τ, a, k.2.1, true)
    else ∑ a, MvPolynomial.C ((fr⁻¹) k.1 a) * MvPolynomial.X (τ, a, k.2.1, false)) P

theorem evalPoly_polyAt {m : ℕ} (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) (P : PX m n)
    (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) : evalPoly (polyAt τ fr P) z = evX P (fr⁻¹ * z τ) := by
  unfold evalPoly polyAt evX
  refine (eval_bind₁' _ _ _).trans (congrArg (fun f => MvPolynomial.eval f P) (funext fun k => ?_))
  obtain ⟨c, i, b⟩ := k
  cases b <;> simp [Matrix.mul_apply, star_sum]

theorem poly_split {m : ℕ} (τ : D.what₂.Tau) {fr : Matrix (Fin m) (Fin m) ℂ} (hfr : IsUnit fr.det)
    (p : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ) :
    ∃ (k : ℕ) (Pi : Fin k → PX m n) (pi : Fin k → MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ),
      (∀ i, ∀ v ∈ (pi i).vars, v.1 ≠ τ) ∧
      ∀ z, evalPoly p z = ∑ i, evX (Pi i) (fr⁻¹ * z τ) * evalPoly (pi i) z := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a =>
    refine ⟨1, fun _ => MvPolynomial.C a, fun _ => 1, by simp, fun z => ?_⟩
    simp [evalPoly, evX]
  | add p q hp hq =>
    obtain ⟨k1, P1, p1, h1, e1⟩ := hp
    obtain ⟨k2, P2, p2, h2, e2⟩ := hq
    refine ⟨k1 + k2, Fin.append P1 P2, Fin.append p1 p2, ?_, fun z => ?_⟩
    · intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa using h1 j
      · simpa using h2 j
    · rw [Fin.sum_univ_add, evalPoly_add, e1, e2]
      simp
  | mul_X p v hp =>
    obtain ⟨k, Pi, pi, h, e⟩ := hp
    by_cases hv : v.1 = τ
    · refine ⟨k, fun i => Pi i * (if v.2.2.2 then ∑ c, MvPolynomial.C (star (fr v.2.1 c)) * MvPolynomial.X (c, v.2.2.1, true)
          else ∑ c, MvPolynomial.C (fr v.2.1 c) * MvPolynomial.X (c, v.2.2.1, false)), pi, h, fun z => ?_⟩
      have hz : z τ = fr * (fr⁻¹ * z τ) := (Matrix.mul_nonsing_inv_cancel_left _ _ hfr).symm
      have hw : (if v.2.2.2 then conj (z v.1 v.2.1 v.2.2.1) else z v.1 v.2.1 v.2.2.1) =
          evX (if v.2.2.2 then ∑ c, MvPolynomial.C (star (fr v.2.1 c)) * MvPolynomial.X (c, v.2.2.1, true)
            else ∑ c, MvPolynomial.C (fr v.2.1 c) * MvPolynomial.X (c, v.2.2.1, false)) (fr⁻¹ * z τ) := by
        rw [hv]
        conv_lhs => rw [hz]
        split_ifs <;> simp [evX, Matrix.mul_apply, map_sum]
      rw [evalPoly_mul, e, evalPoly_X, hw, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [evX, map_mul]
      ring
    · refine ⟨k, Pi, fun i => pi i * MvPolynomial.X v, fun i w hw => ?_, fun z => ?_⟩
      · have := MvPolynomial.vars_mul (pi i) (MvPolynomial.X v) hw
        rw [Finset.mem_union, MvPolynomial.vars_X] at this
        rcases this with h' | h'
        · exact h i w h'
        · rw [Finset.mem_singleton] at h'
          rw [h']
          exact hv
      · rw [evalPoly_mul, e, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [evalPoly_mul]
        ring

theorem splitFock : SplitFock := by
  intro D n V θ l s τ ε fr _ hfr Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨p, g, hg, rfl⟩ := hφ
    obtain ⟨k, Pi, pi, hpi, e⟩ := poly_split τ hfr.1 p
    refine ⟨k, Pi, fun i x => evalPoly (pi i) (fun τ => compAt θ τ x) * gAway V l s τ (fun τ => compAt θ τ x) *
      g (fun i j => finPart D (x i j)), fun i => Submodule.subset_span ⟨pi i, g, hg, hpi i, rfl⟩, ?_⟩
    funext x
    rw [Finset.sum_apply, e, gauss_split l hfr, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [tens, fP]
    ring
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨k1, P1, Ψ1, h1, e1⟩ := hx
    obtain ⟨k2, P2, Ψ2, h2, e2⟩ := hy
    refine ⟨k1 + k2, Fin.append P1 P2, Fin.append Ψ1 Ψ2,
      fun i => Fin.addCases (fun j => by simpa using h1 j) (fun j => by simpa using h2 j) i, ?_⟩
    rw [Fin.sum_univ_add, e1, e2]
    simp
  | smul a x _ hx =>
    obtain ⟨k, Qs, Ψi, h, e⟩ := hx
    refine ⟨k, Qs, fun i => a • Ψi i, fun i => Submodule.smul_mem _ a (h i), ?_⟩
    rw [e, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    funext x
    simp only [tens, Pi.smul_apply, smul_eq_mul]
    ring

theorem tens_zero {m : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ)
    (f : (Fin m → Fin n → ℂ) → ℂ) : tens θ τ fr f (0 : Mx D m n → ℂ) = 0 := by
  funext x; simp [tens]

theorem tens_add {m : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ)
    (f : (Fin m → Fin n → ℂ) → ℂ) (Ψ Ψ' : Mx D m n → ℂ) : tens θ τ fr f (Ψ + Ψ') = tens θ τ fr f Ψ + tens θ τ fr f Ψ' := by
  funext x; simp [tens, mul_add]

theorem tens_smul {m : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ)
    (f : (Fin m → Fin n → ℂ) → ℂ) (a : ℂ) (Ψ : Mx D m n → ℂ) : tens θ τ fr f (a • Ψ) = a • tens θ τ fr f Ψ := by
  funext x; simp only [tens, Pi.smul_apply, smul_eq_mul]; ring

theorem tensMem_fock {V : HSp D} {θ : InfFam D} {l : D.what₂.Tau → ℝ} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    {τ : D.what₂.Tau} {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hfr : IsTauFrame V τ s ε fr)
    {Ψ : Mx D V.rank n → ℂ} (hΨ : Ψ ∈ awayA θ V n l s τ) (P : PX V.rank n) :
    tens θ τ fr (fP (cLoc l τ) P) Ψ ∈ fockA θ V n l s := by
  induction hΨ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨p, g, hg, -, rfl⟩ := hφ
    refine Submodule.subset_span ⟨polyAt τ fr P * p, g, hg, ?_⟩
    funext x
    simp only [tens, fP, evalPoly_mul, evalPoly_polyAt, gauss_split l hfr]
    ring
  | zero => rw [tens_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [tens_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [tens_smul]; exact Submodule.smul_mem _ a hx

def coordCLM {m : ℕ} (v : D.what₂.Tau × Fin m × Fin n × Bool) : (D.what₂.Tau → Fin m → Fin n → ℂ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) v.2.2.1).comp
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) v.2.1).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : D.what₂.Tau => Fin m → Fin n → ℂ) v.1))

theorem hasTemperateGrowth_evalPoly {m : ℕ} (p : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ) :
    Function.HasTemperateGrowth (fun w : D.what₂.Tau → Fin m → Fin n → ℂ => evalPoly p (fun τ => Matrix.of (w τ))) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    have e : (fun w : D.what₂.Tau → Fin m → Fin n → ℂ => evalPoly (MvPolynomial.C a) (fun τ => Matrix.of (w τ))) =
        fun _ => a := funext fun w => evalPoly_C a _
    rw [e]
    exact Function.HasTemperateGrowth.const a
  | add p q hp hq =>
    have e : (fun w : D.what₂.Tau → Fin m → Fin n → ℂ => evalPoly (p + q) (fun τ => Matrix.of (w τ))) =
        (fun w => evalPoly p (fun τ => Matrix.of (w τ))) + fun w => evalPoly q (fun τ => Matrix.of (w τ)) :=
      funext fun w => evalPoly_add p q _
    rw [e]
    exact hp.add hq
  | mul_X p v hp =>
    have hc : Function.HasTemperateGrowth (fun w : D.what₂.Tau → Fin m → Fin n → ℂ =>
        if v.2.2.2 then conj (w v.1 v.2.1 v.2.2.1) else w v.1 v.2.1 v.2.2.1) := by
      split_ifs
      · exact (Complex.conjCLE.toContinuousLinearMap.comp (coordCLM v)).hasTemperateGrowth
      · exact (coordCLM v).hasTemperateGrowth
    have e : (fun w : D.what₂.Tau → Fin m → Fin n → ℂ => evalPoly (p * MvPolynomial.X v) (fun τ => Matrix.of (w τ))) =
        (fun w => evalPoly p (fun τ => Matrix.of (w τ))) *
          fun w => if v.2.2.2 then conj (w v.1 v.2.1 v.2.2.1) else w v.1 v.2.1 v.2.2.1 :=
      funext fun w => by rw [evalPoly_mul, evalPoly_X]; rfl
    rw [e]
    exact hp.mul hc

theorem fockA_le_schwartzA {V : HSp D} {θ : InfFam D} {l : D.what₂.Tau → ℝ} (hl : ∀ τ, l τ ≠ 0)
    {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} (hs : ∀ τ, IsCartanInv (gramAt D V τ) (s τ)) :
    fockA θ V n l s ≤ schwartzA θ V.rank n := by
  refine Submodule.span_le.2 ?_
  rintro φ ⟨p, g, hg, rfl⟩
  obtain ⟨f, hf⟩ := GlobalTheory.GaussSchwartz.exists_schwartz_gauss D n V l hl s hs
  refine Submodule.subset_span ⟨SchwartzMap.smulLeftCLM ℂ (fun w => evalPoly p (fun τ => Matrix.of (w τ))) f, g, hg, ?_⟩
  funext x
  rw [SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_evalPoly p), hf, smul_eq_mul]
  rfl

theorem tensMem : TensMem := by
  intro D n V θ l s τ ε fr _ hl hs hfr Ψ hΨ P
  have h := tensMem_fock hfr hΨ P
  exact ⟨fockA_le_schwartzA hl hs h, h⟩

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocInst
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.LocInstH

open MvPolynomial

def toRe (m n : ℕ) : PX m n →ₐ[ℂ] PX m n :=
  aeval fun k => if k.2.2 then X (k.1, k.2.1, false) - C Complex.I * X (k.1, k.2.1, true)
    else X (k.1, k.2.1, false) + C Complex.I * X (k.1, k.2.1, true)

def ofRe (m n : ℕ) : PX m n →ₐ[ℂ] PX m n :=
  aeval fun k => if k.2.2 then C (1 / (2 * Complex.I)) * (X (k.1, k.2.1, false) - X (k.1, k.2.1, true))
    else C (1 / 2) * (X (k.1, k.2.1, false) + X (k.1, k.2.1, true))

theorem ofRe_toRe {m n : ℕ} (P : PX m n) : ofRe m n (toRe m n P) = P := by
  have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have hC : (C Complex.I : PX m n) * C (1 / (2 * Complex.I)) = C (1 / 2) := by
    rw [← C_mul]; congr 1; field_simp
  have hC2 : (C (1 / 2) : PX m n) + C (1 / 2) = 1 := by
    rw [← C_add, ← C_1]; congr 1; norm_num
  have : (ofRe m n).comp (toRe m n) = AlgHom.id ℂ (PX m n) := by
    apply MvPolynomial.algHom_ext
    intro k
    obtain ⟨a, i, b⟩ := k
    cases b
    · simp only [AlgHom.comp_apply, AlgHom.id_apply, toRe, ofRe, aeval_X, map_add, map_mul, aeval_C, algebraMap_eq,
        Bool.false_eq_true, if_false, if_true]
      linear_combination (X (a, i, false) - X (a, i, true)) * hC + X (a, i, false) * hC2
    · simp only [AlgHom.comp_apply, AlgHom.id_apply, toRe, ofRe, aeval_X, map_sub, map_mul, aeval_C, algebraMap_eq,
        Bool.false_eq_true, if_false, if_true]
      linear_combination -(X (a, i, false) - X (a, i, true)) * hC + X (a, i, true) * hC2
  exact congrArg (fun f => f P) this

theorem evX_eq_eval_toRe {m n : ℕ} (P : PX m n) (y : Fin m × Fin n × Bool → ℝ) :
    evX P (fun a i => (y (a, i, false) : ℂ) + Complex.I * (y (a, i, true) : ℂ)) =
      eval (fun k => (y k : ℂ)) (toRe m n P) := by
  have key : (aeval fun k : Fin m × Fin n × Bool => if k.2.2 then star ((y (k.1, k.2.1, false) : ℂ) + Complex.I * (y (k.1, k.2.1, true) : ℂ))
      else (y (k.1, k.2.1, false) : ℂ) + Complex.I * (y (k.1, k.2.1, true) : ℂ)) = (aeval fun k => (y k : ℂ)).comp (toRe m n) := by
    apply MvPolynomial.algHom_ext
    intro k
    obtain ⟨a, i, b⟩ := k
    cases b
    · simp [toRe]
    · simp [toRe, Complex.conj_ofReal, sub_eq_add_neg]
  unfold evX
  rw [← coe_aeval_eq_eval, ← coe_aeval_eq_eval]
  exact congrArg (fun f => f P) key

theorem evX_injective {m n : ℕ} {P Q : PX m n} (h : ∀ u, evX P u = evX Q u) : P = Q := by
  have h0 : toRe m n (P - Q) = 0 := by
    apply eq_zero_of_eval_real
    intro y
    rw [← evX_eq_eval_toRe]
    have := h (fun a i => (y (a, i, false) : ℂ) + Complex.I * (y (a, i, true) : ℂ))
    unfold evX at this ⊢
    rw [map_sub, this, sub_self]
  rw [← sub_eq_zero, ← ofRe_toRe (P - Q), h0, map_zero]

theorem fP_injective {m n : ℕ} {c : ℝ} {P Q : PX m n} (h : fP c P = fP c Q) : P = Q := by
  apply evX_injective
  intro u
  have := congrFun h u
  simp only [fP] at this
  have hg : gs c u ≠ 0 := Complex.exp_ne_zero _
  exact mul_right_cancel₀ hg this

theorem fP_smul_add {m n : ℕ} (c : ℝ) (a : ℂ) (P Q : PX m n) : fP c (a • P + Q) = a • fP c P + fP c Q := by
  funext u
  simp only [fP, evX, map_add, smul_eq_C_mul, map_mul, eval_C, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

end PositivityTheory.Rg.Sw.Glob.LocInstH

namespace PositivityTheory.Rg.Sw.Glob

open LocInstH

theorem locInst_of (hT : TensMem) (hl : LIl) (hlin : LIlin) (hlaw : LIlaw) (hcell : LIcell) (hcont : LIcont)
    (hrho : LIrho) (hk : LIkact) (hvac : LIvac) (hkv : LIkvac) : LocInst := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC L hL
  have hl0 := hl D n V ψ χ θ μ ω H l s ν τ ε fr ι hC
  obtain ⟨hlinL, hid⟩ := hlin D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL
  obtain ⟨e, he⟩ := hlaw D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL
  obtain ⟨C0, hC0, hCc⟩ := hcell D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL
  obtain ⟨ρ, hρ, hfin⟩ := hrho D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL
  have hzero : ∀ y : GR n, L y (fP (cLoc l τ) (0 : PX V.rank n)) = 0 := by
    intro y
    have h2 := hlinL y 1 0 0
    simp only [one_smul, add_zero] at h2
    have : L y (fP (cLoc l τ) (0 : PX V.rank n)) + L y (fP (cLoc l τ) (0 : PX V.rank n)) =
        L y (fP (cLoc l τ) (0 : PX V.rank n)) + 0 := by rw [add_zero]; exact h2.symm
    exact add_left_cancel this
  let sL : PX V.rank n →ₗ[ℂ] (GR n → ℂ) :=
    { toFun := fun P => sLd L (cLoc l τ) P
      map_add' := fun P Q => by
        funext y
        have h2 := hlinL y 1 P Q
        rw [one_smul, one_smul] at h2
        simp only [sLd, Pi.add_apply, h2]
      map_smul' := fun a P => by
        funext y
        have h2 := hlinL y a P 0
        rw [add_zero, hzero y, add_zero] at h2
        simp only [sLd, Pi.smul_apply, RingHom.id_apply, h2, smul_eq_mul] }
  have hsign : ((tLoc l τ = cLoc l τ ∧ (pqOf ε l τ).1 = cnt ε true ∧ (pqOf ε l τ).2 = cnt ε false) ∨
      (tLoc l τ = -cLoc l τ ∧ (pqOf ε l τ).1 = cnt ε false ∧ (pqOf ε l τ).2 = cnt ε true)) := by
    unfold tLoc cLoc pqOf
    split_ifs with h
    · exact Or.inl ⟨by rw [abs_of_pos h], rfl, rfl⟩
    · have hneg : l τ < 0 := lt_of_le_of_ne (not_lt.mp h) hl0
      exact Or.inr ⟨by rw [abs_of_neg hneg]; ring, rfl, rfl⟩
  have hcpos : 0 < cLoc l τ := by
    unfold cLoc
    have := abs_pos.mpr hl0
    positivity
  have h11 : sLd L (cLoc l τ) 1 1 = 1 := by
    simp [sLd, hid, fP, evX, gs]
  have hvac' : ∀ g, sLd L (cLoc l τ) 1 g = F0 (pqOf ε l τ).1 (pqOf ε l τ).2 e g :=
    hvac V.rank n ε (cLoc l τ) (tLoc l τ) (pqOf ε l τ).1 (pqOf ε l τ).2 e hcpos hsign (sLd L (cLoc l τ) 1) C0
      (hcont D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL 1) h11 (fun y g hy => he 1 y g hy) (fun g b hb hg => hCc 1 g b hb hg)
  refine ⟨sL, ρ, (pqOf ε l τ).1, (pqOf ε l τ).2, e, ?_, ?_, fun P y => rfl, hρ⟩
  · have hs := hC.hsig
    unfold pqOf GoodSig at *
    split_ifs <;> omega
  · refine ⟨hcpos, hsign, fun P => hcont D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL P, hvac', fun P y g hy => he P y g hy,
      ⟨C0, hC0, fun P g b hb hg => hCc P g b hb hg⟩,
      fun P g k hk' => hk D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL ρ hρ P g k hk', ?_, hfin⟩
    intro k hkK
    have h1 := hkv D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL e hvac' k hkK
    rw [hρ k 1 hkK] at h1
    apply fP_injective (c := cLoc l τ)
    rw [h1]
    have := fP_smul_add (cLoc l τ) (F0 (pqOf ε l τ).1 (pqOf ε l τ).2 e k) (1 : PX V.rank n) 0
    simp only [add_zero] at this
    rw [this]
    funext u
    simp [fP, evX]

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ZReAddZImStar
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open MvPolynomial

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.IInvH

variable {D : D7} {m n : ℕ}

def xyC (Z : Matrix (Fin m) (Fin m) ℂ) (a : Fin m) (i : Fin n) (b : Bool) : PX m n :=
  ∑ c, C (Z a c) * MvPolynomial.X (c, i, b)

def vfC (c : ℝ) (Zh Za : Matrix (Fin m) (Fin m) ℂ) (P : PX m n) : PX m n :=
  ∑ a, ∑ i, (xyC Zh a i false * pderiv (a, i, false) P + xyC Za a i true * pderiv (a, i, true) P -
    C (c : ℂ) * (xyC Zh a i false * MvPolynomial.X (a, i, true) + xyC Za a i true * MvPolynomial.X (a, i, false)) * P)

theorem vfX_eq (c : ℝ) (Z : Matrix (Fin m) (Fin m) ℂ) (P : PX m n) : vfX c Z P = vfC c Z (Z.map star) P := by
  have h1 : ∀ a (i : Fin n), xyP Z a i false = xyC Z a i false := fun a i => by simp [xyP, xyC]
  have h2 : ∀ a (i : Fin n), xyP Z a i true = xyC (Z.map star) a i true := fun a i => by simp [xyP, xyC, Matrix.map_apply]
  simp only [vfX, vfC, h1, h2]

theorem xyC_add_smul (Z Z' : Matrix (Fin m) (Fin m) ℂ) (r : ℂ) (a : Fin m) (i : Fin n) (b : Bool) :
    xyC (Z + r • Z') a i b = xyC Z a i b + C r * xyC Z' a i b := by
  simp only [xyC, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum, mul_assoc]

theorem vfC_lin (c : ℝ) (Zh Za Zh' Za' : Matrix (Fin m) (Fin m) ℂ) (r : ℂ) (P : PX m n) :
    vfC c Zh Za P + r • vfC c Zh' Za' P = vfC c (Zh + r • Zh') (Za + r • Za') P := by
  simp only [vfC, xyC_add_smul, smul_eq_C_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem xyC_single (a b a' : Fin m) (r : ℂ) (i : Fin n) (β : Bool) :
    xyC (r • Matrix.single a b (1 : ℂ)) a' i β = if a' = a then C r * MvPolynomial.X (b, i, β) else 0 := by
  by_cases h : a' = a
  · subst h
    simp only [xyC, Matrix.smul_apply, Matrix.single_apply, true_and, smul_eq_mul, mul_ite, mul_one,
      mul_zero, if_true]
    rw [Finset.sum_eq_single b]
    · simp
    · intro x _ hx
      simp [Ne.symm hx]
    · simp
  · simp [xyC, Matrix.single_apply, h, Ne.symm h]

theorem sgn_star (ε : Fin m → Bool) (a : Fin m) : star (sgn ε a) = sgn ε a := by
  unfold sgn; split_ifs <;> simp

theorem zRe_add_zIm (ε : Fin m → Bool) (a b : Fin m) :
    zRe ε a b + Complex.I • zIm ε a b = (1 : ℂ) • Matrix.single a b (1 : ℂ) := by
  ext i j
  simp only [zRe, zIm, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem zRe_add_zIm_star (ε : Fin m → Bool) (a b : Fin m) :
    (zRe ε a b).map star + Complex.I • (zIm ε a b).map star = (-(sgn ε a * sgn ε b)) • Matrix.single b a (1 : ℂ) := by
  have hs : (starRingEnd ℂ) (sgn ε a) = sgn ε a := sgn_star ε a
  have ht : (starRingEnd ℂ) (sgn ε b) = sgn ε b := sgn_star ε b
  have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := map_ofNat _ 2
  ext i j
  simp only [zRe, zIm, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.map_apply,
    smul_eq_mul, Matrix.neg_apply, Matrix.single_apply, Complex.star_def]
  split_ifs <;> simp [map_add, map_mul, map_neg, map_sub, hs, ht, h2, Complex.conj_I] <;> ring_nf <;>
    simp [Complex.I_sq] <;> ring

theorem hOp_eq (ε : Fin m → Bool) (c : ℝ) (a b : Fin m) (P : PX m n) :
    hOp ε c a b P = vfX c (zRe ε a b) P + Complex.I • vfX c (zIm ε a b) P := by
  rw [vfX_eq, vfX_eq, vfC_lin, zRe_add_zIm, zRe_add_zIm_star]
  unfold vfC hOp
  simp only [xyC_single]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [ite_mul, zero_mul, mul_ite, mul_zero, add_mul, mul_add]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [map_neg, map_one, map_mul, map_sub]
  ring

end PositivityTheory.Rg.Sw.Glob.IInvH
end
end

