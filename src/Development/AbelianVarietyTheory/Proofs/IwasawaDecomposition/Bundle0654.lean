import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0053
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0633
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0037
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0572
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0599
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0589
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0600
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0602
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0590
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0588
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0596
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0592
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0607
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0630
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0610
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArithmeticCMKnownTheoremsProof
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0067
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MahlerCompactness
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FirstMinimumEqZeroOfRankZero
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0014
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.ExistsGoodLevel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0042
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.BigStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0038
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0636
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0028
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0622
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0637
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0010

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinearOnIsFineOfLinearOnPolarisationBaseFunction
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan.LinOn

theorem finrank_int_eq' (E : Type) [Field E] [NumberField E] (X : Type) [AddCommGroup X] [Module (𝓞 E) X] :
    Module.finrank ℤ X = Module.finrank ℚ E * Module.finrank (𝓞 E) X := by
  rw [← (TensorProduct.isBaseChange ℤ X ℚ).finrank_eq, ← (TensorProduct.isBaseChange (𝓞 E) X E).finrank_eq,
    Module.finrank_mul_finrank, (Algebra.IsPushout.cancelBaseChange ℤ ℚ (𝓞 E) E X).finrank_eq]

variable {X : Type} [AddCommGroup X] {m : ℕ}

section Pol

variable [Module.Finite ℤ X]

theorem sum_le_evalR {φ : InvFun ℤ} (h : IsPolFanOn (id : ℤ → ℤ) φ X) {γ : Fin m → LinearMap.BilinForm ℤ X}
    (h1 : ∀ i, γ i ∈ balForms (id : ℤ → ℤ) X) (h2 : ∀ i y, 0 ≤ γ i y y) {c : Fin m → ℝ} (hc : ∀ i, 0 ≤ c i) :
    ∑ i, c i * φ.evalZ (γ i) ≤ evalR φ (∑ i, c i • toReal (γ i)) := by
  classical
  have hmem : ∀ d : Fin m → ℝ, (∀ i, 0 ≤ d i) → ∑ i, d i • toReal (γ i) ∈ psdCone (id : ℤ → ℤ) X :=
    fun d hd => GlobalTheory.PolFan.ConeSub.sum_smul_toReal_mem_psdCone ℤ id X m γ d h1 h2 hd
  have hsub : ∀ s : Finset (Fin m), ∑ i ∈ s, c i • toReal (γ i) ∈ psdCone (id : ℤ → ℤ) X := fun s => by
    have := hmem (fun i => if i ∈ s then c i else 0) fun i => by
      split_ifs
      · exact hc i
      · exact le_rfl
    simpa [ite_smul, Finset.sum_ite_mem] using this
  have hone : ∀ a, toReal (γ a) ∈ psdCone (id : ℤ → ℤ) X := fun a => by
    have := hmem (Pi.single a 1) fun i => by
      by_cases e : i = a
      · subst e; simp
      · simp [Pi.single_eq_of_ne e]
    simpa [Pi.single_apply, ite_smul] using this
  have key : ∀ s : Finset (Fin m), ∑ i ∈ s, c i * φ.evalZ (γ i) ≤ evalR φ (∑ i ∈ s, c i • toReal (γ i)) := fun s => by
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      refine le_trans ?_ (h.superadd _ (smul_mem_psdCone (hone a) (hc a)) _ (hsub s))
      rw [h.homog _ (hone a) _ (hc a), evalR_toReal]
      linarith
  simpa using key Finset.univ

end Pol

section Mean

variable (M : ℕ) {k : ℕ} {s : (Fin k → ℤ) →ₗ[ℤ] X}

abbrev rd (s : (Fin k → ℤ) →ₗ[ℤ] X) (B : X → X → ℝ) : (Fin k → ℤ) → (Fin k → ℤ) → ℝ := fun a b => B (s a) (s b)

theorem fineMean_eval [Module.Finite ℤ X] (hs : Function.Surjective s) (B : X → X → ℝ) :
    (fineMean M).eval X B = (((M : ℝ) + 1) ^ k)⁻¹ * ∑ y, classMin M (rd s B) y - B 0 0 := by
  rw [InvFun.eval_eq _ hs]
  simp [fineMean]

theorem classMin_le {β : LinearMap.BilinForm ℤ X} (h : ∀ y, 0 ≤ β y y) (s : (Fin k → ℤ) →ₗ[ℤ] X) (a : Fin k → ℤ) :
    classMin M (rd s fun a b => (β a b : ℝ)) (redV M a) ≤ (β (s a) (s a) : ℝ) := by
  refine csInf_le ⟨0, ?_⟩ ⟨a, rfl, rfl⟩
  rintro x ⟨a, -, rfl⟩
  show (0 : ℝ) ≤ ((β (s a) (s a) : ℤ) : ℝ)
  exact_mod_cast h (s a)

theorem sum_classMin_le {γ : Fin m → LinearMap.BilinForm ℤ X} (h : ∀ i y, 0 ≤ γ i y y) (s : (Fin k → ℤ) →ₗ[ℤ] X)
    {c : Fin m → ℝ} (hc : ∀ i, 0 ≤ c i) (y : Fin k → ZMod (M + 1)) :
    ∑ i, c i * classMin M (rd s fun a b => (γ i a b : ℝ)) y ≤
      classMin M (rd s fun a b => ∑ i, c i * (γ i a b : ℝ)) y := by
  obtain ⟨a₀, ha₀⟩ := redV_surjective M k y
  refine le_csInf ⟨_, a₀, ha₀, rfl⟩ ?_
  rintro x ⟨a, rfl, rfl⟩
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (classMin_le M (h i) s a) (hc i)

theorem sum_mul_mean {Y : Type} [Fintype Y] (K : ℝ) (c : Fin m → ℝ) (f : Fin m → Y → ℝ) :
    ∑ i, c i * (K * ∑ y, f i y) = K * ∑ y, ∑ i, c i * f i y := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun i _ => by ring

theorem mean_pos : (0 : ℝ) < (((M : ℝ) + 1) ^ k)⁻¹ := by positivity

theorem fineMean_evalZ [Module.Finite ℤ X] (hs : Function.Surjective s) (β : LinearMap.BilinForm ℤ X) :
    (fineMean M).evalZ β = (((M : ℝ) + 1) ^ k)⁻¹ * ∑ y, classMin M (rd s fun a b => (β a b : ℝ)) y := by
  rw [InvFun.evalZ, fineMean_eval M hs]
  simp

theorem fineMean_evalSum [Module.Finite ℤ X] (hs : Function.Surjective s) (γ : Fin m → LinearMap.BilinForm ℤ X)
    (c : Fin m → ℝ) :
    (fineMean M).eval X (fun a b => ∑ i, c i * (γ i a b : ℝ)) =
      (((M : ℝ) + 1) ^ k)⁻¹ * ∑ y, classMin M (rd s fun a b => ∑ i, c i * (γ i a b : ℝ)) y := by
  rw [fineMean_eval M hs]
  simp

theorem sum_fineMean_le [Module.Finite ℤ X] {γ : Fin m → LinearMap.BilinForm ℤ X} (h : ∀ i y, 0 ≤ γ i y y)
    {c : Fin m → ℝ} (hc : ∀ i, 0 ≤ c i) :
    ∑ i, c i * (fineMean M).evalZ (γ i) ≤ (fineMean M).eval X (fun a b => ∑ i, c i * (γ i a b : ℝ)) := by
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin' ℤ X
  rw [fineMean_evalSum M hs]
  simp only [fineMean_evalZ M hs]
  rw [sum_mul_mean]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => sum_classMin_le M h s hc y) (mean_pos M).le

theorem classMin_sum_eq [Module.Finite ℤ X] {γ : Fin m → LinearMap.BilinForm ℤ X} (h : ∀ i y, 0 ≤ γ i y y)
    (hs : Function.Surjective s)
    (he : (fineMean M).eval X (fun a b => ∑ i, (1 : ℝ) * (γ i a b : ℝ)) = ∑ i, (1 : ℝ) * (fineMean M).evalZ (γ i))
    (y : Fin k → ZMod (M + 1)) :
    classMin M (rd s fun a b => ∑ i, (1 : ℝ) * (γ i a b : ℝ)) y =
      ∑ i, (1 : ℝ) * classMin M (rd s fun a b => (γ i a b : ℝ)) y := by
  rw [fineMean_evalSum M hs] at he
  simp only [fineMean_evalZ M hs] at he
  rw [sum_mul_mean] at he
  have e3 := mul_left_cancel₀ (mean_pos (k := k) M).ne' he
  have := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ)
    (f := fun y => ∑ i, (1 : ℝ) * classMin M (rd s fun a b => (γ i a b : ℝ)) y)
    (g := fun y => classMin M (rd s fun a b => ∑ i, (1 : ℝ) * (γ i a b : ℝ)) y)
    fun y _ => sum_classMin_le M h s (fun _ => zero_le_one) y).1 e3.symm y (Finset.mem_univ y)
  exact this.symm

theorem exists_classMin_attained {β : LinearMap.BilinForm ℤ X} (h : ∀ y, 0 ≤ β y y) (s : (Fin k → ℤ) →ₗ[ℤ] X)
    (a₀ : Fin k → ℤ) :
    ∃ α, redV M α = redV M a₀ ∧ ∀ a, redV M a = redV M a₀ → β (s α) (s α) ≤ β (s a) (s a) := by
  obtain ⟨⟨α, hα⟩, -, h0⟩ := (measure fun a : {a : Fin k → ℤ // redV M a = redV M a₀} =>
    (β (s a.1) (s a.1)).toNat).wf.has_min Set.univ ⟨⟨a₀, rfl⟩, trivial⟩
  refine ⟨α, hα, fun a ha => ?_⟩
  have h1 : ¬ (β (s a) (s a)).toNat < (β (s α) (s α)).toNat := h0 ⟨a, ha⟩ trivial
  have := h (s a)
  have := h (s α)
  omega

theorem isFine_of_additive [Module.Finite ℤ X] {γ : Fin m → LinearMap.BilinForm ℤ X} (h : ∀ i y, 0 ≤ γ i y y)
    (he : (fineMean M).eval X (fun a b => ∑ i, (1 : ℝ) * (γ i a b : ℝ)) = ∑ i, (1 : ℝ) * (fineMean M).evalZ (γ i)) :
    IsFine (M + 1) γ := by
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin' ℤ X
  intro y
  obtain ⟨a₀, rfl⟩ := hs y
  let σ : LinearMap.BilinForm ℤ X := ∑ i, γ i
  have hσa : ∀ a b, σ a b = ∑ i, γ i a b := fun a b => by simp [σ, LinearMap.sum_apply]
  have hσ : ∀ y, 0 ≤ σ y y := fun y => by
    rw [hσa]; exact Finset.sum_nonneg fun i _ => h i y
  obtain ⟨α, hα, hmin⟩ := exists_classMin_attained M hσ s a₀
  obtain ⟨d, hd⟩ := exists_eq_add_of_redV_eq hα
  have hcm := classMin_sum_eq M h hs he (redV M a₀)

  have hval : classMin M (rd s fun a b => ∑ i, (1 : ℝ) * (γ i a b : ℝ)) (redV M a₀) = ((σ (s α) (s α) : ℤ) : ℝ) := by
    refine IsLeast.csInf_eq ⟨⟨α, hα, ?_⟩, ?_⟩
    · simp [rd, hσa]
    · rintro x ⟨a, ha, rfl⟩
      have := hmin a ha
      have h2 : ((σ (s α) (s α) : ℤ) : ℝ) ≤ ((σ (s a) (s a) : ℤ) : ℝ) := by exact_mod_cast this
      simpa [rd, hσa] using h2
  have hle : ∀ i, classMin M (rd s fun a b => (γ i a b : ℝ)) (redV M a₀) ≤ (γ i (s α) (s α) : ℝ) := fun i => by
    rw [← hα]; exact classMin_le M (h i) s α
  have hsum : ∑ i, classMin M (rd s fun a b => (γ i a b : ℝ)) (redV M a₀) = ∑ i, (γ i (s α) (s α) : ℝ) := by
    rw [hval] at hcm
    simp only [one_mul] at hcm
    rw [← hcm, hσa]
    push_cast
    rfl
  have heq := (Finset.sum_eq_sum_iff_of_le fun i _ => hle i).1 hsum
  refine ⟨s d, fun i μ => ?_⟩
  obtain ⟨e, rfl⟩ := hs μ
  have hn : ∀ x : X, (M + 1) • x = ((M : ℤ) + 1) • x := fun x => by
    rw [← natCast_zsmul]; push_cast; rfl
  have e1 : s a₀ + (M + 1) • s d = s α := by
    rw [hd, map_add, map_smul, hn]
  have e2 : s a₀ + (M + 1) • s e = s (a₀ + ((M : ℤ) + 1) • e) := by
    rw [map_add, map_smul, hn]
  rw [e1, e2]
  have h3 := classMin_le M (h i) s (a₀ + ((M : ℤ) + 1) • e)
  rw [redV_add_smul, heq i (Finset.mem_univ i)] at h3
  exact_mod_cast h3

end Mean

end GlobalTheory.PolFan.LinOn

open GlobalTheory.PolFan.LinOn in

theorem GlobalTheory.PolFan.linearOn_and_isFine_of_linearOn_baseFun (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (g q D : ℕ) (φs : InvFun ℤ) (𝓜 : Finset ℕ) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X]
    [Module.Projective (𝓞 E) X] (hD : 0 < D) (hφ : IsPolFan (id : ℤ → ℤ) g φs) (hq : Module.finrank ℚ E * q ≤ g)
    (hX : Module.finrank (𝓞 E) X ≤ q) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (hb : ∀ i, γ i ∈ balForms H.bar X)
    (hp : ∀ i y, 0 ≤ γ i y y) (hl : (baseFun (𝓞 E) D φs 𝓜).LinearOn γ) :
    (restr (𝓞 E) φs).LinearOn γ ∧ ∀ M ∈ 𝓜, IsFine (M + 1) γ := by
  haveI : Module.Finite ℤ X := Module.Finite.trans (𝓞 E) X
  haveI : Module.Projective ℤ X := by
    obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' (𝓞 E) X
    obtain ⟨h, hh⟩ := Module.projective_lifting_property r LinearMap.id hr
    exact Module.Projective.of_split (h.restrictScalars ℤ) (r.restrictScalars ℤ)
      (LinearMap.ext fun x => LinearMap.congr_fun hh x)
  have hrank : Module.finrank ℤ X ≤ g := by
    rw [finrank_int_eq' E X]
    exact (Nat.mul_le_mul_left _ hX).trans hq
  have hpol : IsPolFanOn (id : ℤ → ℤ) φs X := hφ X hrank
  have h1 : ∀ i, γ i ∈ balForms (id : ℤ → ℤ) X := fun i => mem_balForms_int.2 (hb i).1
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD

  have hsplit : ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) →
      φs.eval X (fun a b => ∑ i, c i * (γ i a b : ℝ)) = ∑ i, c i * φs.evalZ (γ i) ∧
      ∀ M ∈ 𝓜, (fineMean M).eval X (fun a b => ∑ i, c i * (γ i a b : ℝ)) = ∑ i, c i * (fineMean M).evalZ (γ i) := by
    intro c hc
    have e0 : ∑ i, c i * φs.evalZ (γ i) ≤ φs.eval X (fun a b => ∑ i, c i * (γ i a b : ℝ)) := by
      have := sum_le_evalR hpol h1 hp hc
      simpa [evalR, LinearMap.sum_apply] using this
    have eM : ∀ M ∈ 𝓜, ∑ i, c i * (fineMean M).evalZ (γ i) ≤
        (fineMean M).eval X (fun a b => ∑ i, c i * (γ i a b : ℝ)) := fun M _ => sum_fineMean_le M hp hc
    have e3 : φs.eval X (fun a b => ∑ i, c i * (γ i a b : ℝ)) +
        ∑ M ∈ 𝓜, (fineMean M).eval X (fun a b => ∑ i, c i * (γ i a b : ℝ)) =
        ∑ i, c i * φs.evalZ (γ i) + ∑ M ∈ 𝓜, ∑ i, c i * (fineMean M).evalZ (γ i) := by
      have e4 : ∑ i, c i * ((D : ℝ) * (φs.evalZ (γ i) + ∑ M ∈ 𝓜, (fineMean M).evalZ (γ i))) =
          D * (∑ i, c i * φs.evalZ (γ i) + ∑ M ∈ 𝓜, ∑ i, c i * (fineMean M).evalZ (γ i)) := by
        have e7 : ∀ i, c i * ((D : ℝ) * (φs.evalZ (γ i) + ∑ M ∈ 𝓜, (fineMean M).evalZ (γ i))) =
            D * (c i * φs.evalZ (γ i) + ∑ M ∈ 𝓜, c i * (fineMean M).evalZ (γ i)) := fun i => by
          rw [← Finset.mul_sum]; ring
        simp only [e7]
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_comm (s := Finset.univ)]
      have h2 : (D : ℝ) * (φs.eval X (fun a b => ∑ i, c i * (γ i a b : ℝ)) +
          ∑ M ∈ 𝓜, (fineMean M).eval X (fun a b => ∑ i, c i * (γ i a b : ℝ))) =
          ∑ i, c i * ((D : ℝ) * (φs.evalZ (γ i) + ∑ M ∈ 𝓜, (fineMean M).evalZ (γ i))) := by
        simpa only [InvFun.evalZ, eval_baseFun] using hl c hc
      rw [e4] at h2
      exact mul_left_cancel₀ hDr.ne' h2
    have hs2 : ∑ M ∈ 𝓜, ∑ i, c i * (fineMean M).evalZ (γ i) ≤
        ∑ M ∈ 𝓜, (fineMean M).eval X (fun a b => ∑ i, c i * (γ i a b : ℝ)) := Finset.sum_le_sum eM
    have e5 : φs.eval X (fun a b => ∑ i, c i * (γ i a b : ℝ)) = ∑ i, c i * φs.evalZ (γ i) := by linarith
    refine ⟨e5, ?_⟩
    have e6 : ∑ M ∈ 𝓜, ∑ i, c i * (fineMean M).evalZ (γ i) =
        ∑ M ∈ 𝓜, (fineMean M).eval X (fun a b => ∑ i, c i * (γ i a b : ℝ)) := by linarith
    exact fun M hM => ((Finset.sum_eq_sum_iff_of_le eM).1 e6 M hM).symm
  refine ⟨fun c hc => ?_, fun M hM => ?_⟩
  · simp only [InvFun.evalZ, eval_restr]
    exact (hsplit c hc).1
  · exact isFine_of_additive M hp ((hsplit (fun _ => 1) fun _ => zero_le_one).2 M hM)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalOrderBoundaryFormEq
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.TorRef.BalancedTrait

theorem le_of_pow_dvd {W : Type} [CommRing W] [IsDomain W] {ϖ : W} (hϖ : Irreducible ϖ) {m k : ℕ}
    (h : ϖ ^ m ∣ ϖ ^ k) : m ≤ k := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨c, hc⟩ := h
  have h0 : ϖ ^ k ≠ 0 := pow_ne_zero _ hϖ.ne_zero
  have hm : ϖ ^ m = ϖ ^ k * ϖ ^ (m - k) := by rw [← pow_add]; congr 1; omega
  rw [hm, mul_assoc] at hc
  have h1 : ϖ ^ (m - k) * c = 1 := by
    have := mul_left_cancel₀ h0 (hc.symm.trans (mul_one _).symm)
    exact this
  have hu : IsUnit (ϖ ^ (m - k)) := ⟨⟨ϖ ^ (m - k), c, h1, (mul_comm _ _).trans h1⟩, rfl⟩
  exact hϖ.not_isUnit ((isUnit_pow_iff (by omega)).1 hu)

theorem pow_eq_of_associated {W : Type} [CommRing W] [IsDomain W] {ϖ : W} (hϖ : Irreducible ϖ) {m k : ℕ}
    (h : Associated (ϖ ^ m) (ϖ ^ k)) : m = k :=
  le_antisymm (le_of_pow_dvd hϖ h.dvd) (le_of_pow_dvd hϖ h.symm.dvd)

theorem two_mul_apply {X : Type} [AddCommGroup X] (be : LinearMap.BilinForm ℤ X) (hs : ∀ y z, be y z = be z y)
    (y z : X) : 2 * be y z = be (y + z) (y + z) - be y y - be z z := by
  simp only [map_add, LinearMap.add_apply, hs z y]
  ring

theorem smul_left {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {O : Type} [Ring O] [StarRing O]
    (Dg : DegPre R) [Module O Dg.X] (ρ : Dg.OAct O) {W : Type} [CommRing W] [IsDomain W] {ϖ : W}
    (hϖ : Irreducible ϖ) (f : R →+* W) (be : LinearMap.BilinForm ℤ Dg.X) (hs : ∀ y z, be y z = be z y)
    (hF : FormAt Dg f ϖ be) (x : O) (y z : Dg.X) : be (x • y) z = be y (star x • z) := by
  choose r n hr hn ha using hF
  obtain ⟨u, hu⟩ := GlobalTheory.PeriodBalance.coord_balance Dg ρ x y z (hr (x • y + z)) (hr (x • y)) (hr z)
    (hr (y + star x • z)) (hr y) (hr (star x • z))
  have hA : Associated (f (r (x • y + z)) * f (r y) * f (r (star x • z)))
      (f (r (y + star x • z)) * f (r (x • y)) * f (r z)) := by
    refine ⟨(Units.map f.toMonoidHom u), ?_⟩
    have := congrArg f hu
    simp only [map_mul] at this
    rw [← this]
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    ring
  have hP : Associated (ϖ ^ (n (x • y + z) + n y + n (star x • z))) (ϖ ^ (n (y + star x • z) + n (x • y) + n z)) := by
    simp only [pow_add]
    exact (((ha _).symm.mul_mul (ha _).symm).mul_mul (ha _).symm).trans
      (hA.trans (((ha _).mul_mul (ha _)).mul_mul (ha _)))
  have he := pow_eq_of_associated hϖ hP
  have h1 := two_mul_apply be hs (x • y) z
  have h2 := two_mul_apply be hs y (star x • z)
  rw [hn, hn, hn] at h1
  rw [hn, hn, hn] at h2
  have he' : ((n (x • y + z) : ℤ) + n y + n (star x • z)) = (n (y + star x • z) : ℤ) + n (x • y) + n z := by
    exact_mod_cast he
  omega

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Z : GMod Xo c) (g : ℕ) (φs : InvFun ℤ) (𝒩 : Finset ℕ) (φ : InvFun (𝓞 E)) (EX : EffCartierData Z.X) (N : ℕ) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ Z.X) (t : SAB H (Sp R)), SABMap t Z.t ξ → ∀ (P : PELUnif (maximalIdeal R) t) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), Module.finrank ℚ E * min D.p D.q ≤ g → IsPolFan id g φs → Refines H (min D.p D.q) φs 𝒩 φ → 0 < N → IsPhiDiv (comb 0 φ N φ) Z EX → IsCN R → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified → P.TorsionIso → ConeZ E φs P.D.toPre.X m γ → InCone P.D.toPre γ → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ ϖ : W, Irreducible ϖ → ∀ (f : R →+* W) (be : LinearMap.BilinForm ℤ P.D.toPre.X), (∀ y z, be y z = be z y) → FormAt P.D.toPre f ϖ be → be ∈ balForms H.bar P.D.toPre.X := by
  intro E _ _ _ H D l Xo c Z g φs 𝒩 φ EX N R _ _ _ ξ t _ P m γ _ _ _ _ _ _ _ _ _ _ _ W _ _ _ _ ϖ hϖ f be hs hF
  letI := H.starRing
  exact ⟨hs, fun a y z => smul_left P.D.toPre P.oD hϖ f be hs hF a y z⟩

end GlobalTheory.TorRef.BalancedTrait
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemCommonRefinementStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_system_common_refinement : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → (N2 Y ∧ ∀ i, (Y i).SplitFibres ∧ (Y i).N3 ∧ (Y i).N4) → ∀ (n : ℕ) (Z : Fin (n + 1) → Mdl Y i₀), (∀ a, (Z a).i = (Z 0).i ∧ (Z a).ty = (Z 0).ty) → ∃ Z' : Mdl Y i₀, Z'.i = (Z 0).i ∧ Z'.ty = (Z 0).ty ∧ ∀ a, ∃ f : Z'.X ⟶ (Z a).X, IsMap Z' (Z a) f := by
  first | exact @GlobalTheory.ShFam.Pad.exists_dominating_model | exact GlobalTheory.ShFam.Pad.exists_dominating_model | (intros; apply GlobalTheory.ShFam.Pad.exists_dominating_model <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMapStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_system_model_map : HTBoundSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → (N2 Y ∧ ∀ i, (Y i).SplitFibres ∧ (Y i).N3 ∧ (Y i).N4) → ∀ (Z Z' : Mdl Y i₀) (f : Z'.X ⟶ Z.X), IsMap Z' Z f → (∀ τ k, k ≤ Dw.mult τ → k ∈ Z.ty τ) → ∀ b st x, letterOf Dw st = some x → Nonempty (LineModel Z b st x) → Nonempty (LineModel Z' b st x) := by
  first | exact @GlobalTheory.ShFam.Pad.Pull.lineModel_pull | exact GlobalTheory.ShFam.Pad.Pull.lineModel_pull | (intros; apply GlobalTheory.ShFam.Pad.Pull.lineModel_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCuspOfVanishOn
section
noncomputable section

namespace GlobalTheory.CuspFrom

section Analytic

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {la : Wt X.Ψ r}
  {P : Frame X.Ψ r → ℂ}

theorem thickBdd (hP : X.IsSec la P) : ThickBdd X (X.pnorm la P) := by
  intro ε hε
  obtain ⟨K, hK, hKd, hcov⟩ := GlobalTheory.FlagMahler.mahler_compactness (E := E) r X ε hε
  obtain ⟨C, hC⟩ := (hK.image_of_continuousOn ((AR.Up.BigB.pnorm_contOn X la hP).mono hKd)).bddAbove
  refine ⟨C, fun x hx hl => ?_⟩
  obtain ⟨γ, hγ, b, hb, h⟩ := hcov x hx hl
  have := hC ⟨_, h, rfl⟩
  rwa [AR.Up.OW.pnorm_lact la hP hγ (AR.Up.OntoS.dom_rmul X hx hb), FrameDegreeData.pnorm_rmul X la P hP.2.1 x hx b hb] at this

theorem freqNonneg (hf : 1 < Module.finrank ℚ E / 2) (hP : X.IsSec la P) : FreqNonneg X la P :=
  GlobalTheory.T.koecher_principle_flagDomain_frequencies_nonneg (GlobalTheory.T.flowOrbitFirstMinimum_of_isotropicFlowMajorant GlobalTheory.T.isotropicFlow_majorant_cauchySchwarz) E r X la P hf hP (thickBdd X hP)

theorem growth (hf : 1 < Module.finrank ℚ E / 2) (hP : X.IsSec la P) {w : ℝ} (hw : 0 ≤ w)
    (h : ∀ τ, X.spread la τ / 2 ≤ w) : ∃ C A : ℝ, ∀ x ∈ X.dom, X.pnorm la P x ≤ C * X.la1 x ^ (-(A * w)) :=
  GlobalTheory.T.moderate_growth_of_firstMinimum_and_flow_bounds GlobalTheory.T.isotropicFlow_majorant_cauchySchwarz E r X w _ hw (fun x _ => mul_nonneg (norm_nonneg _) (Formalism.L2.Pj.pnorm_fac_nonneg X la x))
    (thickBdd X hP) (GlobalTheory.T.maximum_principle_isotropicFlow_rescaledBound E r X la P w hP (freqNonneg X hf hP) h)

theorem isModerate (hf : 1 < Module.finrank ℚ E / 2) (hP : X.IsSec la P) : X.IsModerate la P := by
  obtain ⟨C, A, h⟩ := growth X hf hP (w := ∑ τ, |X.spread la τ / 2|) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    fun τ => (le_abs_self _).trans (Finset.single_le_sum (f := fun τ => |X.spread la τ / 2|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ τ))
  exact ⟨C, _, h⟩

end Analytic

section Geometric

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam
open scoped LaurentSeries

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ r}

theorem exists_input [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (Uw : UnfWit U)
    (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U) {k : U.Comp} {ξ' : Fin r → E}
    (hξ : (U.X k).IsIso ξ') {x : Frame (U.X k).Ψ r} (hx : x ∈ (U.X k).dom) :
    ∃ a : ArcIn Dw l (RingHom.id c.F) ℂ σ, ∀ (O : Type) [CommRing O] (β : O →+* c.F),
      FlowTie Uw (a.restrict β) k ξ' x := by
  letI := H.starRing
  obtain ⟨hp, hq⟩ := GlobalTheory.ArcCM.Exist.one_le_of_isIso hU hξ
  obtain ⟨A, gam, ξ, jj, DB, tyB, eB, hO, hξ0, hrk, hdvd, -, hprim, -, hab, hDp, hDq⟩ :=
    GlobalTheory.T.exists_analytic_model_on_frame_orbit_isolating E H Dw l Xo c σ r U Uw k ξ' x 0 0 hσ hU hξ hx
      (fun m _ => ⟨0, by simp, by funext τ i; simp [Data.embV, Data.emb]⟩) (by simp [cc]) (by simp)
      (fun s _ _ => ⟨0, by simp⟩)
  obtain ⟨B, ex, hex⟩ := GlobalTheory.T.exists_principalCMTriple_exponential_of_period E H l DB _ tyB _ hab.2.1 hab.2.2.2.2
  obtain ⟨aC, Λ, hA, h1, h2⟩ := GlobalTheory.T.exists_complex_arc_of_analytic_model_on_flow_orbit E H Dw l Xo c σ r U Uw k ξ' x B hσ hU A gam ξ DB tyB eB ex hO hrk hdvd
    hprim hab hDp hDq hp hq hex
  subst hA
  exact ⟨aC, GlobalTheory.T.arcs_on_flow_lines_of_analytic_model_on_orbit E H Dw l Xo c σ r U Uw k ξ' x aC Λ hσ hU hξ hx gam ξ hO hξ0 hrk h1 h2⟩

theorem exists_model (Xo : Moduli Dw l) (c : Coeff l) (hr : 1 ≤ Dw.p + Dw.q) :
    ∃ (W : ValuationSubring ℂ) (Y : Model Xo c (c.V W).subtype), Y.N4 ∧ PushInvertible Y.t.G Y.t.PP.L := by
  classical
  have hK := GlobalTheory.ArcCM.known_holds
  obtain ⟨W, hW⟩ := GlobalTheory.GlobalModelGuards.exists_place 2 Nat.prime_two
  have hg : l.GoodAt 2 := by
    have := l.three_le
    rwa [Level.GoodAt, Nat.factorization_eq_zero_of_not_dvd l.odd.not_two_dvd_nat, pow_zero, Nat.div_one]
  have key : ∀ Xs : ∀ l' : Level H, Moduli Dw l',
      ∃ Y : Model (Xs l) c (c.V W).subtype, Y.N4 ∧ PushInvertible Y.t.G Y.t.PP.L := by
    intro Xs
    obtain ⟨Y, hY, -⟩ := hK.models.2 E H Dw hr Xs
    obtain ⟨h2, h4⟩ := hY 2 W Nat.prime_two hW
    exact ⟨Y 2 W Nat.prime_two hW ⟨l, c, hg⟩, (h4 _).2.2, (h2.1 ⟨l, c, hg⟩).2.2.1⟩
  have h := key (Function.update (fun l' => Classical.choice (hK.n1ab E H Dw l' hr)) l Xo)
  rw [Function.update_self] at h
  exact ⟨W, h⟩

theorem coeff_eq_zero {v : PowerSeries ℂ} (hv : v ∈ IsLocalRing.maximalIdeal (PowerSeries ℂ)) {j : ℤ} (hj : j ≤ 0) :
    (algebraMap (PowerSeries ℂ) ℂ⸨X⸩ v).coeff j = 0 := by
  rw [PowerSeries.maximalIdeal_eq_span_X, Ideal.mem_span_singleton, PowerSeries.X_dvd_iff] at hv
  rw [LaurentSeries.coe_algebraMap, PowerSeries.coeff_coe]
  split_ifs with h0
  · rfl
  · obtain rfl : j = 0 := by omega
    simpa using hv

end Geometric

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam
open scoped LaurentSeries

end GlobalTheory.CuspFrom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemberFormsLayerMidStepChartsConditionsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.G Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.ChartsLv GlobalTheory.Mem.Top.KerOne.CertEq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.memberFormsLayer_midStep_charts_conditions : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∀ (i : ℕ) (hi : i + 1 ≤ (w.D Z).R.m), i + 1 + 1 ≤ (w.D Z).R.m →
      ∃ (Fo : FormsIn ((w.D Z).fm u) (i + 1) hi) (_ : Finite Fo.Ch) (S : StepD t.g.herm u v hg Fo),
        StepTiesD t.g.herm u v hg hi Fo S t.cmp := by
  first | exact @GlobalTheory.Mem.Top.KerOne.CertEq.stepTiesD_mid | exact GlobalTheory.Mem.Top.KerOne.CertEq.stepTiesD_mid | (intros; apply GlobalTheory.Mem.Top.KerOne.CertEq.stepTiesD_mid <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MumfordGoodGrowthPolynomialRepresentationStatement
section
open AlgebraicGeometry MvPolynomial GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordGoodGrowth_polynomialRepresentation : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (ρ : PolyRep m) (c : ℝ) (N : ℕ), ∃ (c' : ℝ) (N' : ℕ), ∀ (n : ℕ) (S : Finset (Fin n)) (G : V n → Mat m ℂ) (v : V n), (∀ τ, MContDiffAt 2 (fun u => G u τ) v) → (∀ τ, (G v τ).det ≠ 0) → 1 ≤ ∑ a ∈ S, |Real.log ‖v a‖| → (∀ τ, GoodBound S c N (fun u => G u τ) v) → GoodBound S c' N' (fun u => ρ.ev (G u)) v := by
  first | exact @GlobalTheory.RepBound.goodBound_ev | exact GlobalTheory.RepBound.goodBound_ev | (intros; apply GlobalTheory.RepBound.goodBound_ev <;> assumption)
end

