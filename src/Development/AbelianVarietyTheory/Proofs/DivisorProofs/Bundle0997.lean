import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0236
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0978
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0045
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0347
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0348
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0334
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0969
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0418
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0970
import Development.AbelianVarietyTheory.Counterexamples.TwistSurvey.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0965
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0764
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0971
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalRingCardinality.Bundle0007
import Formalism.LocalRingCardinality.Bundle0003
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0972
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0936
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0607

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormEqMulInner
section
open scoped InnerProductSpace ComplexConjugate

namespace GlobalTheory.ConjLiftUnique

private lemma exists_linearMap_sesqForm_eq_inner {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (b : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ) : ∃ A : E →ₗ[ℂ] E, ∀ x y, b x y = ⟪A x, y⟫_ℂ := by
  let f : E → E := fun x => (InnerProductSpace.toDual ℂ E).symm (LinearMap.toContinuousLinearMap (b x))
  have hf : ∀ x y, ⟪f x, y⟫_ℂ = b x y := by
    intro x y
    simp only [f, InnerProductSpace.toDual_symm_apply, LinearMap.coe_toContinuousLinearMap']
  refine ⟨{ toFun := f, map_add' := ?_, map_smul' := ?_ }, fun x y => (hf x y).symm⟩
  · intro x x'
    apply ext_inner_right ℂ
    intro y
    simp [hf, inner_add_left]
  · intro c x
    apply ext_inner_right ℂ
    intro y
    simp [hf, inner_smul_left]

theorem form_eq_mul_inner {E I : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (g : I → E →ₗ[ℂ] E) (hu : ∀ k x y, ⟪g k x, g k y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hirr : ∀ U : Submodule ℂ E, (∀ k, ∀ x ∈ U, g k x ∈ U) → U = ⊥ ∨ U = ⊤)
    (b : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ) (hb : ∀ k x y, b (g k x) (g k y) = b x y) : ∃ c : ℂ, ∀ x y, b x y = c * ⟪x, y⟫_ℂ := by
  obtain ⟨A, hA⟩ := exists_linearMap_sesqForm_eq_inner b
  have hinj : ∀ k, Function.Injective (g k) := by
    intro k
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    have h0 : ⟪x, x⟫_ℂ = 0 := by rw [← hu k x x, LinearMap.mem_ker.mp hx, inner_zero_left]
    exact inner_self_eq_zero.mp h0
  have hsurj : ∀ k, Function.Surjective (g k) := fun k => LinearMap.injective_iff_surjective.mp (hinj k)
  have hcomm : ∀ k x, A (g k x) = g k (A x) := by
    intro k x
    apply ext_inner_right ℂ
    intro y
    obtain ⟨z, rfl⟩ := hsurj k y
    rw [← hA, hb, hu, hA]
  rcases subsingleton_or_nontrivial E with hE | hE
  · exact ⟨0, fun x y => by simp [Subsingleton.elim x 0]⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue A
  have hinv : ∀ k, ∀ x ∈ Module.End.eigenspace A c, g k x ∈ Module.End.eigenspace A c := by
    intro k x hx
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    rw [hcomm, hx, map_smul]
  rcases hirr _ hinv with h | h
  · exact absurd h (Module.End.hasEigenvalue_iff.mp hc)
  · refine ⟨conj c, fun x y => ?_⟩
    have hx : x ∈ Module.End.eigenspace A c := h ▸ Submodule.mem_top
    rw [Module.End.mem_eigenspace_iff] at hx
    rw [hA, hx, inner_smul_left]

private lemma inner_self_eq_one_of_norm_eq_one' {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {u : F}
    (hu : ‖u‖ = 1) : ⟪u, u⟫_ℂ = 1 := by
  rw [inner_self_eq_norm_sq_to_K, hu]; simp

variable {ι : Type} [Fintype ι] [DecidableEq ι] {E : ι → Type} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℂ (E i)] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]

theorem exists_const (B : (∀ i, E i) → W → (∀ i, E i) → W → ℂ) (w₀ : W) (h₀ : ‖w₀‖ = 1)
    (h1 : ∀ w w' i v v', ∃ c : ℂ, ∀ a a' : E i,
      B (Function.update v i a) w (Function.update v' i a') w' = c * ⟪a, a'⟫_ℂ)
    (h2 : ∀ v v', ∃ c : ℂ, ∀ w w', B v w v' w' = c * ⟪w, w'⟫_ℂ) :
    ∃ c : ℂ, ∀ v w v' w', B v w v' w' = c * ((∏ i, ⟪v i, v' i⟫_ℂ) * ⟪w, w'⟫_ℂ) := by
  by_cases hall : ∀ i, Nontrivial (E i)
  · have he : ∀ i, ∃ e : E i, ‖e‖ = 1 := fun i => by
      haveI := hall i
      exact exists_norm_eq (E i) zero_le_one
    choose e he using he
    have hee : ∀ i, ⟪e i, e i⟫_ℂ = 1 := fun i => inner_self_eq_one_of_norm_eq_one' (he i)
    have hw : ∀ v v' w w', B v w v' w' = B v w₀ v' w₀ * ⟪w, w'⟫_ℂ := by
      intro v v' w w'
      obtain ⟨c, hc⟩ := h2 v v'
      rw [hc, hc w₀ w₀, inner_self_eq_one_of_norm_eq_one' h₀, mul_one]
    have hs : ∀ s : Finset ι, ∀ v v' : ∀ i, E i, (∀ i ∉ s, v i = e i) → (∀ i ∉ s, v' i = e i) →
        B v w₀ v' w₀ = B e w₀ e w₀ * ∏ i ∈ s, ⟪v i, v' i⟫_ℂ := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        intro v v' hv hv'
        have e1 : v = e := funext fun i => hv i (by simp)
        have e2 : v' = e := funext fun i => hv' i (by simp)
        subst e1 e2
        simp
      | insert j s hj ih =>
        intro v v' hv hv'
        obtain ⟨c, hc⟩ := h1 w₀ w₀ j v v'
        have k1 := hc (v j) (v' j)
        have k2 := hc (e j) (e j)
        rw [Function.update_eq_self, Function.update_eq_self] at k1
        rw [hee, mul_one] at k2
        have ih' := ih (Function.update v j (e j)) (Function.update v' j (e j)) ?_ ?_
        · rw [k1, ← k2, ih', Finset.prod_insert hj]
          have hcg : ∀ i ∈ s, ⟪Function.update v j (e j) i, Function.update v' j (e j) i⟫_ℂ = ⟪v i, v' i⟫_ℂ := by
            intro i hi
            have hij : i ≠ j := fun h => hj (h ▸ hi)
            rw [Function.update_of_ne hij, Function.update_of_ne hij]
          rw [Finset.prod_congr rfl hcg]
          ring
        · intro i hi
          by_cases hij : i = j
          · subst hij
            simp
          · rw [Function.update_of_ne hij]
            exact hv i (by simp [hij, hi])
        · intro i hi
          by_cases hij : i = j
          · subst hij
            simp
          · rw [Function.update_of_ne hij]
            exact hv' i (by simp [hij, hi])
    refine ⟨B e w₀ e w₀, fun v w v' w' => ?_⟩
    rw [hw, hs Finset.univ v v' (by simp) (by simp)]
    ring
  · obtain ⟨i, hi⟩ := not_forall.mp hall
    haveI : Subsingleton (E i) := not_nontrivial_iff_subsingleton.mp hi
    refine ⟨0, fun v w v' w' => ?_⟩
    obtain ⟨c, hc⟩ := h1 w w' i v v'
    have k := hc (v i) (v' i)
    rw [Function.update_eq_self, Function.update_eq_self, Subsingleton.elim (v i) 0, inner_zero_left,
      mul_zero] at k
    rw [k, zero_mul]

private lemma inner_self_eq_one_of_unit_norm {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {u : F}
    (hu : ‖u‖ = 1) : ⟪u, u⟫_ℂ = 1 := by
  rw [inner_self_eq_norm_sq_to_K, hu]; simp

private lemma eq_smul_of_form_eq_of_unit_modulus {Y : Type} [AddCommGroup Y] [Module ℂ Y] (b : Y →ₗ⋆[ℂ] Y →ₗ[ℂ] ℂ)
    (hs : ∀ x y, b y x = conj (b x y)) (hd : ∀ x, b x x = 0 → x = 0)
    {x y : Y} {κ : ℂ} (hk : conj κ * κ = 1) (hyy : b y y = b x x) (hxy : b x y = κ * b x x) :
    y = κ • x := by
  have hyx : b y x = conj κ * b x x := by
    rw [hs x y, hxy, map_mul, ← hs x x]
  rw [← sub_eq_zero]
  apply hd
  simp only [map_sub, LinearMap.map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, map_smul, smul_eq_mul]
  linear_combination hyy - κ * hyx - conj κ * hxy - b x x * hk

theorem exists_phase {Y : Type} [AddCommGroup Y] [Module ℂ Y] (b : Y →ₗ⋆[ℂ] Y →ₗ[ℂ] ℂ)
    (hs : ∀ x y, b y x = conj (b x y)) (hp : ∀ x, 0 ≤ (b x x).re) (hd : ∀ x, b x x = 0 → x = 0)
    (F F' : (∀ i, E i) → W → Y) {c₁ c₂ c₃ : ℂ}
    (h1 : ∀ v w v' w', b (F v w) (F v' w') = c₁ * ((∏ i, ⟪v i, v' i⟫_ℂ) * ⟪w, w'⟫_ℂ))
    (h2 : ∀ v w v' w', b (F' v w) (F' v' w') = c₂ * ((∏ i, ⟪v i, v' i⟫_ℂ) * ⟪w, w'⟫_ℂ))
    (h3 : ∀ v w v' w', b (F v w) (F' v' w') = c₃ * ((∏ i, ⟪v i, v' i⟫_ℂ) * ⟪w, w'⟫_ℂ))
    {v₀ v₀' : ∀ i, E i} {w₀ w₀' : W} (n1 : ∀ i, ‖v₀ i‖ = 1) (n2 : ∀ i, ‖v₀' i‖ = 1) (n3 : ‖w₀‖ = 1) (n4 : ‖w₀'‖ = 1)
    {l : ℂ} (hl : ‖l‖ = 1) (hm : F v₀ w₀ = l • F' v₀' w₀') :
    ∃ κ : ℂ, ‖κ‖ = 1 ∧ ∀ v w, F' v w = κ • F v w := by
  have P1 : (∏ i, ⟪v₀ i, v₀ i⟫_ℂ) * ⟪w₀, w₀⟫_ℂ = 1 := by
    rw [Finset.prod_eq_one (fun i _ => inner_self_eq_one_of_unit_norm (n1 i)), inner_self_eq_one_of_unit_norm n3, one_mul]
  have P2 : (∏ i, ⟪v₀' i, v₀' i⟫_ℂ) * ⟪w₀', w₀'⟫_ℂ = 1 := by
    rw [Finset.prod_eq_one (fun i _ => inner_self_eq_one_of_unit_norm (n2 i)), inner_self_eq_one_of_unit_norm n4, one_mul]
  have hl1 : conj l * l = 1 := by
    rw [Complex.conj_mul', hl]
    simp
  have e1 : b (F v₀ w₀) (F v₀ w₀) = c₁ := by rw [h1, P1, mul_one]
  have e2 : b (F' v₀' w₀') (F' v₀' w₀') = c₂ := by rw [h2, P2, mul_one]
  have hc : c₁ = c₂ := by
    rw [← e1, ← e2, hm]
    simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul]
    linear_combination b (F' v₀' w₀') (F' v₀' w₀') * hl1
  have hA : c₃ * ((∏ i, ⟪v₀ i, v₀' i⟫_ℂ) * ⟪w₀, w₀'⟫_ℂ) = conj l * c₁ := by
    have t := h3 v₀ w₀ v₀' w₀'
    rw [hm] at t
    simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul] at t
    rw [e2, ← hc] at t
    exact t.symm
  have hB : c₃ = conj l * c₁ * ((∏ i, ⟪v₀' i, v₀ i⟫_ℂ) * ⟪w₀', w₀⟫_ℂ) := by
    have t1 := h3 v₀ w₀ v₀ w₀
    have t2 := h2 v₀' w₀' v₀ w₀
    rw [P1, mul_one, hm] at t1
    simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul] at t1
    rw [t2] at t1
    rw [← t1, hc]
    ring
  by_cases h0 : c₁ = 0
  · refine ⟨1, by simp, fun v w => ?_⟩
    have a1 : F v w = 0 := hd _ (by rw [h1, h0, zero_mul])
    have a2 : F' v w = 0 := hd _ (by rw [h2, ← hc, h0, zero_mul])
    rw [a1, a2, smul_zero]
  · set p := (∏ i, ⟪v₀ i, v₀' i⟫_ℂ) * ⟪w₀, w₀'⟫_ℂ with hp
    set q := (∏ i, ⟪v₀' i, v₀ i⟫_ℂ) * ⟪w₀', w₀⟫_ℂ with hq
    have hqp : q = conj p := by
      rw [hp, hq]
      simp [map_prod]
    have hl0 : conj l ≠ 0 := by
      intro h
      rw [map_eq_zero] at h
      rw [h, norm_zero] at hl
      exact zero_ne_one hl
    have hqp1 : q * p = 1 := by
      have hz : conj l * c₁ * (q * p - 1) = 0 := by linear_combination hA - p * hB
      rcases mul_eq_zero.mp hz with h | h
      · exact absurd h (mul_ne_zero hl0 h0)
      · exact sub_eq_zero.mp h
    have hq1 : ‖q‖ = 1 := by
      have h := congrArg norm hqp1
      rw [norm_mul, norm_one] at h
      have e : ‖p‖ = ‖q‖ := by rw [hqp, Complex.norm_conj]
      rw [e] at h
      rcases mul_self_eq_one_iff.mp h with h | h
      · exact h
      · linarith [norm_nonneg q]
    have hκ : ‖conj l * q‖ = 1 := by rw [norm_mul, Complex.norm_conj, hl, hq1, one_mul]
    refine ⟨conj l * q, hκ, fun v w => ?_⟩
    apply eq_smul_of_form_eq_of_unit_modulus b hs hd
    · rw [Complex.conj_mul', hκ]
      simp
    · rw [h2, h1, hc]
    · rw [h3, h1, hB]
      ring

end GlobalTheory.ConjLiftUnique
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameUnitCorrespondence
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnitFrameReal

theorem gram_eq {D : D7} (V : HSp D) (X : Data D.host.E V.rank) (hW : ModelW V rfl X) (ρ : D.what₂.Tau)
    (z : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    gram (tauE D ρ) X.Gm z = -(zᴴ * gramAt D V ρ * z)ᵀ := by
  have hG : X.Gm.map (tauE D ρ) = -(gramAt D V ρ)ᵀ := by
    rw [hW.1]
    ext a b
    simp [gramAt]
  have hg : gram (tauE D ρ) X.Gm z = zᵀ * X.Gm.map (tauE D ρ) * zᴴᵀ := by
    ext a b
    simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, of_apply, mul_apply, transpose_apply, conjTranspose_apply, map_apply,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    rfl
  rw [hg, hG, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]

theorem gram_iff {D : D7} (V : HSp D) (X : Data D.host.E V.rank) (hW : ModelW V rfl X) (ρ : D.what₂.Tau)
    (z : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    (gram (tauE D ρ) X.Gm z = diagonal fun a : Fin V.rank => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) ↔
      zᴴ * gramAt D V ρ * z = diagonal fun c : Fin V.rank => if (c : ℕ) < X.p0 then (-1 : ℂ) else 1 := by
  have e : (diagonal fun a : Fin V.rank => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) =
      -(diagonal fun c : Fin V.rank => if (c : ℕ) < X.p0 then (-1 : ℂ) else 1)ᵀ := by
    rw [diagonal_transpose, diagonal_neg]
    congr 1
    funext a
    unfold sgn
    split_ifs <;> simp
  rw [gram_eq V X hW, e, neg_inj, Matrix.transpose_inj]

theorem negFirst_unit {D : D7} {V : HSp D} {q : ℕ} {x : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (h : NegFirst V q x) (ρ : D.what₂.Tau) : IsUnit (x ρ).det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  have h1 := congrArg Matrix.det (h ρ)
  rw [det_mul, h0, mul_zero, det_diagonal] at h1
  refine Finset.prod_ne_zero_iff.2 (fun c _ => ?_) h1.symm
  split_ifs <;> simp

theorem unit_frames : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (r : ℕ) (hr : V.rank = r) (X : Data D.host.E r) (x : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsInfFam θ → ModelOf V hr X → NegFirst V X.p0 x → (∀ u y, FrIs θ V hr X x u y → IsUnitFr X y) ∧ (∀ y, IsUnitFr X y → ∃ u ∈ GinfC V, FrIs θ V hr X x u y) ∧ (∀ u, ∃ y, FrIs θ V hr X x u y) ∧ (∀ u y y', FrIs θ V hr X x u y → FrIs θ V hr X x u y' → y = y') ∧ ∀ u ∈ GinfC V, ∀ u' ∈ GinfC V, ∀ y, FrIs θ V hr X x u y → FrIs θ V hr X x u' y → u = u' := by
  intro D θ V r hr X x hθ hM hx
  subst hr
  obtain ⟨hΨ, hW⟩ := hM
  have hre : ∀ A : Matrix (Fin V.rank) (Fin V.rank) ℂ,
      Matrix.reindex (finCongr (rfl : V.rank = V.rank)) (finCongr rfl) A = A := fun _ => rfl
  have hmem : ∀ ρ, tauE D ρ ∈ X.Ψ := fun ρ => (hΨ _).2 ⟨ρ, rfl⟩
  choose s hs using fun τ : X.Ψ => (hΨ τ.1).1 τ.2
  have hU : ∀ u ρ, (archM V (θ ρ) u)ᴴ * gramAt D V ρ * archM V (θ ρ) u = gramAt D V ρ := fun u ρ =>
    GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V u ρ
  have hxu := negFirst_unit hx
  refine ⟨fun u y h τ => ?_, fun y hy => ?_, fun u => ?_, fun u y y' h h' => ?_, fun u hu u' hu' y h h' => ?_⟩
  · rw [h (s τ) τ (hs τ), hre, hs τ, gram_iff V X hW, ← hx (s τ), conjTranspose_mul]
    conv_rhs => rw [← hU u (s τ)]
    simp only [Matrix.mul_assoc]
  · obtain ⟨u, hu, e⟩ := (GlobalTheory.SmoothForms.RealPts.glue θ hθ V).2
      (fun ρ => mat y ⟨tauE D ρ, hmem ρ⟩ * (x ρ)⁻¹) (fun ρ => by
        have h1 := (gram_iff V X hW ρ _).1 (hy ⟨tauE D ρ, hmem ρ⟩)
        rw [← hx ρ] at h1
        show (mat y ⟨tauE D ρ, hmem ρ⟩ * (x ρ)⁻¹)ᴴ * gramAt D V ρ * (mat y ⟨tauE D ρ, hmem ρ⟩ * (x ρ)⁻¹) =
          gramAt D V ρ
        calc _ = ((x ρ)⁻¹)ᴴ * ((mat y ⟨tauE D ρ, hmem ρ⟩)ᴴ * gramAt D V ρ * mat y ⟨tauE D ρ, hmem ρ⟩) * (x ρ)⁻¹ := by
              simp only [conjTranspose_mul, Matrix.mul_assoc]
          _ = (x ρ * (x ρ)⁻¹)ᴴ * gramAt D V ρ * (x ρ * (x ρ)⁻¹) := by
              rw [h1]; simp only [conjTranspose_mul, Matrix.mul_assoc]
          _ = _ := by rw [Matrix.mul_nonsing_inv _ (hxu ρ)]; simp)
    refine ⟨u, hu, fun ρ τ hτ => ?_⟩
    obtain rfl : τ = ⟨tauE D ρ, hmem ρ⟩ := Subtype.ext hτ
    rw [hre, archM_eq, e ρ, Matrix.nonsing_inv_mul_cancel_right _ _ (hxu ρ)]
  · refine ⟨fun τ => (archM V (θ (s τ)) u * x (s τ) : Matrix _ _ ℂ), fun ρ τ hτ => ?_⟩
    obtain rfl : s τ = ρ := GlobalTheory.SmoothForms.RealPts.tauE_injective D ((hs τ).symm.trans hτ)
    rfl
  · funext τ
    exact (h (s τ) τ (hs τ)).trans (h' (s τ) τ (hs τ)).symm
  · refine ((GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V).2.2.1 u hu u' hu' fun ρ => ?_
    have h1 : archM V (θ ρ) u * x ρ = archM V (θ ρ) u' * x ρ :=
      (h ρ ⟨tauE D ρ, hmem ρ⟩ rfl).symm.trans (h' ρ ⟨tauE D ρ, hmem ρ⟩ rfl)
    have h2 := congrArg (· * (x ρ)⁻¹) h1
    simp only [Matrix.mul_nonsing_inv_cancel_right _ _ (hxu ρ)] at h2
    exact h2

end GlobalTheory.UnitFrameReal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussIntegralDiagonalHermitianFormMatrices
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem hasGauss_diag_norm : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure], ∃ g : ℂ, ∀ t : α → ν → Fˣ, HasGauss μ (fun x => ψ (∑ i, ∑ j, (t i j : F) * Algebra.norm F (x i j))) (g * ∏ i, ∏ j, (sgn E (t i j) * ((nabs F (t i j))⁻¹ : ℝ))) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ ψ hψ hn h1 _ _ μ _
  obtain ⟨hfd, -, -, -, -, -, -, hmat⟩ := GlobalTheory.T.quadExt_topological_properties F E c δ hE
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  haveI : FiniteDimensional F E := hfd
  have hGE : Good E := GlobalTheory.T.isSelfDualCompactOpenGroup_of_finiteDimensional F E
  haveI := hGE.grp; haveI := hGE.lc; haveI := hGE.sc; haveI := hGE.t2
  let μE : Measure E := Measure.addHaar
  obtain ⟨g₁, hg₁⟩ := GlobalTheory.T.gaussIntegral_normForm_scaled_eq_sign_abs_inv F E c δ hE ψ hψ hn h1 μE
  have hGM : Good (Matrix α ν E) := (hmat α ν).2
  haveI := hGM.grp; haveI := hGM.lc; haveI := hGM.sc
  let T : Matrix α ν E ≃ₜ+ (α × ν → E) :=
    { toFun := fun x p => x p.1 p.2
      invFun := fun y i j => y (i, j)
      left_inv := fun x => rfl
      right_inv := fun y => rfl
      map_add' := fun x y => rfl
      continuous_toFun := continuous_pi fun p => (continuous_apply p.2).comp (continuous_apply p.1)
      continuous_invFun := continuous_pi fun i => continuous_pi fun j => continuous_apply (i, j) }
  haveI : BorelSpace (α × ν → E) := Pi.borelSpace
  haveI : (μ.map T).IsAddHaarMeasure := T.isAddHaarMeasure_map μ
  have hr : μ.map T = (μ.map T).addHaarScalarFactor (Measure.pi fun _ : α × ν => μE) •
      Measure.pi fun _ : α × ν => μE := Measure.isAddLeftInvariant_eq_smul _ _
  refine ⟨(((μ.map T).addHaarScalarFactor (Measure.pi fun _ : α × ν => μE) : ℝ) : ℂ) *
    g₁ ^ Fintype.card (α × ν), fun t => ?_⟩
  have hpi := GlobalTheory.T.hasGaussIntegralCompactOpen_pi E hGE μE (α × ν) (fun p z => ψ ((t p.1 p.2 : F) * Algebra.norm F z))
    (fun p => g₁ * (sgn E (t p.1 p.2) * ((nabs F (t p.1 p.2))⁻¹ : ℝ))) (fun p => hg₁ _)
  have hm := GlobalTheory.T.hasGaussIntegral_comp_addEquiv_rescale _ _ μ _ T _ _ _ hr hpi
  have hsum : ∀ (s : Finset (α × ν)) (f : α × ν → F), ψ (∑ p ∈ s, f p) = ∏ p ∈ s, ψ (f p) := by
    intro s f
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]
  convert hm using 1
  · funext x
    rw [← Fintype.sum_prod_type', hsum]
    rfl
  · rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.prod_prod_type, mul_assoc]

end GlobalTheory.KSp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermConstantsEqAlongAffineSpaceSquareStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.germ_constants_eq_along_affineSpace_square : ∀ (Rg : Type) [CommRing Rg] (A₀ T X : Scheme.{0}) (f : A₀ ⟶ Sp Rg) (n : ℕ) (g : T ⟶ Sp (MvPolynomial (Fin n) Rg)) (φ : X ⟶ A₀) (p : X ⟶ T), φ ≫ f = p ≫ g ≫ affπ Rg n → ∀ (z : X) (r : Rg), gs φ z ⊤ (GlobalTheory.FormsLocus.cstT f r) = gs p z ⊤ (GlobalTheory.FormsLocus.ringOf g (MvPolynomial.C r)) := by
  first | (exact @GlobalTheory.FormsLocus.germ_cstT_eq_germ_ringOf_C) | (exact GlobalTheory.FormsLocus.germ_cstT_eq_germ_ringOf_C) | (intros; apply GlobalTheory.FormsLocus.germ_cstT_eq_germ_ringOf_C <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermFormPulledBackCombinationsExpandMonomialsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.germ_form_pulledBack_combinations_expand_monomials : ∀ (Rg : Type) [CommRing Rg] (A₀ T X : Scheme.{0}) (f : A₀ ⟶ Sp Rg) (N : LB A₀) (mA mB : ℕ) (a : Fin mA → LB.Sec N) (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) (φ : X ⟶ A₀) (p : X ⟶ T), φ ≫ f = p ≫ g ≫ affπ Rg (mA * mB) → ∀ (d : ℕ) (F : MvPolynomial (Fin mB) Rg), F.IsHomogeneous d → ∀ (z : X) (q : N.ι), φ z ∈ N.U q → MvPolynomial.eval₂Hom (gc (p ≫ g ≫ affπ Rg (mA * mB)) z) (comb a φ p (matOf g) z q) F = ∑ ν ∈ (GlobalTheory.FormsLocus.expand mA mB F).support, gs p z ⊤ (GlobalTheory.FormsLocus.ringOf g ((GlobalTheory.FormsLocus.expand mA mB F).coeff ν)) * gs φ z (N.U q) ((GlobalTheory.FormsLocus.monSec a d ν).f q) := by
  first | (exact @GlobalTheory.FormsLocus.germ_eval_comb) | (exact GlobalTheory.FormsLocus.germ_eval_comb) | (intros; apply GlobalTheory.FormsLocus.germ_eval_comb  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodEmbeddingLabelIff
section
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolRead

theorem good_iff_labE_and_lab_conj :
    ∀ (D : D7) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL], LawsJ T → AlgTie T → ∀ (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau), (GoodEmb T.Q.c (res T σ) ↔ labE σ (lab σ ρ) = tauE D ρ) ∧ lab ((starRingEnd ℂ).comp σ) ρ = lab σ ρ :=
  fun _ T _ hl ha σ ρ => ⟨GlobalTheory.ConjReading.branch_of_pins T ha hl.pins σ ρ, GlobalTheory.ConjReading.lab_conj σ ρ⟩

end GlobalTheory.HolRead
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraFinitenessAutomorphicGLOfEigen
section
noncomputable section

open NumberField GlobalTheory.CuspRep

namespace GlobalTheory.HCF

theorem automorphicFormsFiniteGL_of_core (h : CoreFiniteGL) : GlobalTheory.Published.AutomorphicFormsFiniteGL := by
  intro E _ _ _ a L hL W _ _ _ ρ _ c
  classical
  haveI hW' : FiniteDimensional ℂ (GlobalTheory.Published.AutFin.coeffSpan ρ) := GlobalTheory.T.finiteDimensional_matrixCoefficientSpan _ W ρ
  let χ : Module.End ℂ (Sm E a) → ℂ := fun z =>
    if hz : ∃ s : ℂ, ∀ φ : Sm E a, (∀ τ u, cap τ u φ = c τ u • φ) → z φ = s • φ then hz.choose else 0
  have hsub : GlobalTheory.Published.AutFinGL.forms L ρ c ⊆ formsGL E a L (GlobalTheory.Published.AutFin.coeffSpan ρ) {χ} 1 := by
    rintro φ ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, h3, χ, rfl, ?_⟩
    intro zs hlen hzs
    match zs, hlen with
    | [z], _ =>
      have hz : z ∈ Zalg E a := hzs z (List.mem_singleton_self z)
      have hex := GlobalTheory.T.center_acts_by_scalar_on_eigenforms E a c z hz
      have hχ : χ z = hex.choose := dif_pos hex
      simp only [List.foldr_cons, List.foldr_nil]
      rw [hχ, hex.choose_spec φ h4, sub_self]
  have hfin := h E a L hL (GlobalTheory.Published.AutFin.coeffSpan ρ) hW' {χ} (Set.finite_singleton χ) 1
  exact Submodule.finiteDimensional_of_le (Submodule.span_mono hsub)

end GlobalTheory.HCF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeChoiceClausesOfWeakCharacterisationAtFaceAlStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hk3Core_and_tup_mu_of_weakCharacterisation : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → R.toRealDat.ExAt → GlobalTheory.Hk3.Core R.toRealDat F.lv2 ∧ R.toRealDat.tup_mu_off ∧ R.toRealDat.tup_mu_used := by
  first | exact @GlobalTheory.OneMapBridge.heckeChoiceClauses_of_weakCharacterisation_at_face | exact GlobalTheory.OneMapBridge.heckeChoiceClauses_of_weakCharacterisation_at_face | (intros; apply GlobalTheory.OneMapBridge.heckeChoiceClauses_of_weakCharacterisation_at_face <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCompatFiniteIsometryStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_compat_finite_isometry : ∀ {D : D7} (V V' : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ) (β' : GL (Fin V'.rank) (EAf D)) (Λ' : Submodule (𝓞 D.host.E) (Fin V'.rank → D.host.E)) (N' : ℕ) (Pg : Finset (Pl D.host.E)) (j : Matrix (Fin V'.rank) (Fin V.rank) (EAf D)) (Φ : GfC V ≃ₜ* GfC V') (PP : Pl D.host.E), IsFinIso V V' β β' Pg j Φ → IsBaseFrame V β Λ N → IsBaseFrame V' β' Λ' N' → ((N : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal → ((N' : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal → ∀ k (α : GfC V), IsHeckeAt V PP k α ↔ IsHeckeAt V' PP k (Φ α) := by
  first | exact @GlobalTheory.HeckeTrans.isHeckeAt_iff | exact GlobalTheory.HeckeTrans.isHeckeAt_iff | (intros; apply GlobalTheory.HeckeTrans.isHeckeAt_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousComponentInRangeEmbeddingStatement
section
open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homogeneous_component_in_range_embedding : ∀ (P Q R : ℕ) (h : P ≤ R) (k : ℕ) (G : Mdl P Q) (n : ℕ), homogeneousComponent n (embR P Q R h k G) ∈ LinearMap.range (embR P Q R h k) := by
  first | exact @GlobalTheory.CharPair.GradR.homogeneousComponent_embR_mem | exact GlobalTheory.CharPair.GradR.homogeneousComponent_embR_mem | (intros; apply GlobalTheory.CharPair.GradR.homogeneousComponent_embR_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomomorphismsSameMatrixIsomorphicTestDataStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homomorphisms_same_matrix_isomorphic_test_data : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (k : ℕ) (mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))), Hyps L M k bA bB eA eB → ∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A₁ B₁ : Over (Sp R)) [GrpObj A₁] [GrpObj B₁] (φA₁ : A₁.left ⟶ A.left) (φB₁ : B₁.left ⟶ B.left) (Φ₁ : A₁ ⟶ B₁) (A₂ B₂ : Over (Sp R)) [GrpObj A₂] [GrpObj B₂] (φA₂ : A₂.left ⟶ A.left) (φB₂ : B₂.left ⟶ B.left) (Φ₂ : A₂ ⟶ B₂) (c : Fin mA → Fin mB → Γ(Sp R, ⊤)), IsTest A B L M t A₁ B₁ φA₁ φB₁ Φ₁ → IsTest A B L M t A₂ B₂ φA₂ φB₂ Φ₂ → IsMat L M k bA bB eA eB t A₁ B₁ φA₁ φB₁ Φ₁ c → IsMat L M k bA bB eA eB t A₂ B₂ φA₂ φB₂ Φ₂ c → IsPullD φA₁ φB₁ Φ₁ φA₂ φB₂ Φ₂ (𝟙 (Sp R)) := by
  first | exact @GlobalTheory.HomFixMat.mat_determines | exact GlobalTheory.HomFixMat.mat_determines | (intros; apply GlobalTheory.HomFixMat.mat_determines <;> assumption)
end

