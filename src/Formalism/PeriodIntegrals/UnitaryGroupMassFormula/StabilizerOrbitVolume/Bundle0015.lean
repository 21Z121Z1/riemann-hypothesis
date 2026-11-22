import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle0011
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.SdDual
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle0012
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle0006
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle0005

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensVolB
section
noncomputable section

namespace PI.VolStabSW

namespace VolAAW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes SdUniqW
  PositiveNearLattice SdDualW

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E)

theorem hform_single {A : Type} [CommRing A] {M : ℕ} (s : A →+* A) (Am : Matrix (Fin M) (Fin M) A)
    (i j : Fin M) (x y : A) :
    Formalism.UG.hform s Am (Pi.single i x) (Pi.single j y) = s x * Am i j * y := by
  unfold Formalism.UG.hform
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro j' _ hj'
      simp [hj']
    · simp
  · intro i' _ hi'
    simp [hi']
  · simp

def gG (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (a : ℕ) :
    Matrix (Fin a × Fin M × Fin d) (Fin a × Fin M × Fin d) F :=
  fun q q' => if q.1 = q'.1 then Algebra.trace F E (σ (b q.2.2) * J q.2.1 q'.2.1 * b q'.2.2) else 0

def cT {a M : ℕ} (v : HeightOneSpectrum (𝓞 F)) (Y : Fin a → Fin M → Fv F v ⊗[F] E) :
    Fin a × Fin M × Fin d → Fv F v :=
  fun q => crd b (Fv F v) (Y q.1 q.2.1) q.2.2

variable [FiniteDimensional F E] (v : HeightOneSpectrum (𝓞 F))

theorem BR_eT (σ : E →ₐ[F] E) {M a : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (q q' : Fin a × Fin M × Fin d) :
    BR (Fv F v) σ J (eT v b q) (eT v b q') = algebraMap F (Fv F v) (gG b σ J a q q') := by
  obtain ⟨p, i, k⟩ := q
  obtain ⟨p', j, l⟩ := q'
  simp only [BR, eT]
  rw [Finset.sum_eq_single p (fun p'' _ h => by simp [Pi.single_apply, h, hR, Formalism.UG.hform])
    (by simp)]
  simp only [Pi.single_eq_same, gG]
  by_cases hp : p = p'
  · subst hp
    simp only [Pi.single_eq_same, if_true, hR, hform_single, JR, Matrix.map_apply]
    have e : sigR (Fv F v) σ ((1 : Fv F v) ⊗ₜ[F] b k) * inclR (Fv F v) (J i j) *
        ((1 : Fv F v) ⊗ₜ[F] b l) = (1 : Fv F v) ⊗ₜ[F] (σ (b k) * J i j * b l) := by
      simp [sigR, inclR, Algebra.TensorProduct.tmul_mul_tmul]
    rw [e, trace_one_tmul]
  · have hp' : p' ≠ p := fun h => hp h.symm
    simp [Pi.single_apply, hp, hR, Formalism.UG.hform]

theorem BR_eT_left (σ : E →ₐ[F] E) {M a : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (q : Fin a × Fin M × Fin d) (Y : Fin a → Fin M → Fv F v ⊗[F] E) :
    BR (Fv F v) σ J (eT v b q) Y =
      ((gG b σ J a).map (algebraMap F (Fv F v))).mulVec (cT b v Y) q := by
  have h := congrFun (congrArg (phiL (a := a) v b σ J) (sum_eT v b Y)) q
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
  change BR (Fv F v) σ J (eT v b q) Y = _
  have h2 : phiL (a := a) v b σ J Y q = BR (Fv F v) σ J (eT v b q) Y := rfl
  rw [← h2, h]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, cT]
  refine Finset.sum_congr rfl fun q' _ => ?_
  have h3 : phiL (a := a) v b σ J (eT v b q') q = BR (Fv F v) σ J (eT v b q) (eT v b q') := rfl
  rw [h3, BR_eT, mul_comm]

theorem BR_eq_sum (σ : E →ₐ[F] E) {M a : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X Y : Fin a → Fin M → Fv F v ⊗[F] E) :
    BR (Fv F v) σ J X Y =
      ∑ q, cT b v X q * ((gG b σ J a).map (algebraMap F (Fv F v))).mulVec (cT b v Y) q := by
  rw [BR_expand v b σ J X Y]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [BR_eT_left]
  rfl

theorem cT_surj {a M : ℕ} (c : Fin a × Fin M × Fin d → Fv F v) :
    ∃ Y : Fin a → Fin M → Fv F v ⊗[F] E, cT b v Y = c := by
  refine ⟨fun p i => (Algebra.TensorProduct.basis (Fv F v) b).equivFun.symm
    (fun k => c (p, i, k)), ?_⟩
  funext q
  obtain ⟨p, i, k⟩ := q
  simp only [cT, crd]
  rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]

theorem mem_latV_iff {a M : ℕ} (Y : Fin a → Fin M → Fv F v ⊗[F] E) :
    Y ∈ latV (M := M) (n := a) b v ↔ ∀ q, cT b v Y q ∈ v.adicCompletionIntegers F := by
  constructor
  · intro h q
    exact h q.1 q.2.1 q.2.2
  · intro h p i k
    exact h (p, i, k)

theorem mulVec_int {ι : Type} [Fintype ι] (A : Matrix ι ι F)
    (hA : ∀ i j, algebraMap F (Fv F v) (A i j) ∈ v.adicCompletionIntegers F)
    (w : ι → Fv F v) (hw : ∀ i, w i ∈ v.adicCompletionIntegers F) (i : ι) :
    (A.map (algebraMap F (Fv F v))).mulVec w i ∈ v.adicCompletionIntegers F := by
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
  exact sum_mem fun j _ => mul_mem (hA i j) (hw j)

include v in

theorem det_gG [Algebra.IsSeparable F E] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M a : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : J.det ≠ 0) : (gG b σ J a).det ≠ 0 := by
  classical
  intro h0
  set G := (gG b σ J a).map (algebraMap F (Fv F v)) with hG
  have hdet : G.det = 0 := by
    rw [hG, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  obtain ⟨Y, hY⟩ := cT_surj b v (a := a) (M := M) w
  have hY0 : Y = 0 := by
    apply nondeg_BR v σ hσ J hJ Y
    intro X
    rw [BR_eq_sum, hY, hw]
    simp
  apply hw0
  rw [← hY, hY0]
  funext q
  simp [cT, crd]

theorem ev_dual [Algebra.IsSeparable F E] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M a : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : J.det ≠ 0) :
    ∀ᶠ v in cofinite, {Y | ∀ X ∈ latV (M := M) (n := a) b v,
      BR (Fv F v) σ J X Y ∈ v.adicCompletionIntegers F} = latV (M := M) (n := a) b v := by
  classical
  filter_upwards [ev_int_all (fun q : (Fin a × Fin M × Fin d) × (Fin a × Fin M × Fin d) =>
      gG b σ J a q.1 q.2),
    ev_int_all (fun q : (Fin a × Fin M × Fin d) × (Fin a × Fin M × Fin d) =>
      (gG b σ J a)⁻¹ q.1 q.2)] with v h1 h2
  have hdet := det_gG b v σ hσ J hJ (a := a)
  set g := gG b σ J a with hg
  ext Y
  constructor
  · intro hY
    rw [Set.mem_setOf_eq] at hY
    rw [mem_latV_iff]
    have hw : ∀ q, (g.map (algebraMap F (Fv F v))).mulVec (cT b v Y) q ∈
        v.adicCompletionIntegers F := by
      intro q
      rw [← BR_eT_left]
      exact hY _ (eT_mem v b q)
    have hinv : (g⁻¹.map (algebraMap F (Fv F v))).mulVec
        ((g.map (algebraMap F (Fv F v))).mulVec (cT b v Y)) = cT b v Y := by
      rw [Matrix.mulVec_mulVec, ← Matrix.map_mul,
        Matrix.nonsing_inv_mul g (isUnit_iff_ne_zero.2 hdet), Matrix.map_one _ (map_zero _)
        (map_one _), Matrix.one_mulVec]
    intro q
    rw [← hinv]
    exact mulVec_int v g⁻¹ (fun i j => h2 (i, j)) _ hw q
  · intro hY
    rw [Set.mem_setOf_eq]
    intro X hX
    rw [BR_eq_sum]
    rw [mem_latV_iff] at hX hY
    exact sum_mem fun q _ => mul_mem (hX q) (mulVec_int v g (fun i j => h1 (i, j)) _ hY q)

end VolAAW

end PI.VolStabSW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.NuInvSt
section
noncomputable section

namespace PI.VolStabSW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct ENNReal

def DetAdm : Prop := InCtx fun F E _ _ _ _ _ _σ M _J a _X0 _hT =>
  ∀ ν1 ν2 : Measure (Fin a → Fin M → AF F ⊗[F] E),
    (∀ K, IsCompact K → ν1 K < ⊤) → (∀ K, IsCompact K → ν2 K < ⊤) →
    (∀ Φ, IsAdm F E Φ → ∫ X, Φ X ∂ν1 = ∫ X, Φ X ∂ν2) → ν1 = ν2

def OmUniq : Prop := InCtx fun F E _ _ _ _ _ σ M J _a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ ν1 ν2, IsOmT F E σ M J ψ (gramE σ J X0) hT ν1 →
    IsOmT F E σ M J ψ (gramE σ J X0) hT ν2 → ν1 = ν2

def OmInv : Prop := InCtx fun F E _ _ _ _ _ σ M J _a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ νX, IsOmT F E σ M J ψ (gramE σ J X0) hT νX →
    ∀ g : HA (AF F) σ J, IsOmT F E σ M J ψ (gramE σ J X0) hT (νX.map fun y => g • y)

theorem continuous_smul_tup {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    [FiniteDimensional F E]
    (σ : E →ₐ[F] E) {M a : ℕ} (J : Matrix (Fin M) (Fin M) E) (g : HA (AF F) σ J) :
    Continuous (fun y : Fin a → Fin M → AF F ⊗[F] E => g • y) := by
  refine continuous_pi fun x => ?_
  change Continuous fun y : Fin a → Fin M → AF F ⊗[F] E =>
    ((HA.mat (AF F) σ J g : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) _).mulVec (y x)
  exact continuous_const.matrix_mulVec (continuous_apply x)

theorem nuInv_of (hU : OmUniq) (hI : OmInv) : NuInv := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ νX hν g s hs
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hm : Measurable (fun y : Fin a → Fin M → AF F ⊗[F] E => g • y) :=
    (continuous_smul_tup σ J g).measurable
  rw [← Measure.map_apply hm hs,
    hU F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ _ _
      (hI F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ νX hν g) hν]

theorem omUniq_of (hD : DetAdm) : OmUniq := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ ν1 ν2 h1 h2
  refine hD F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ν1 ν2
    (nuFin_holds F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ ν1 h1)
    (nuFin_holds F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ ν2 h2) fun Φ hΦ => ?_
  obtain ⟨d, b, Φinf, Φf, Φv, hcΦ, hcs, hpure, hprod⟩ := hΦ
  obtain ⟨⟨μinf, hμinf⟩, a1⟩ := h1.2
  obtain ⟨⟨νinf, hνinf⟩, a2⟩ := a1 μinf hμinf
  obtain ⟨⟨μv, hμv⟩, a3⟩ := a2 νinf hνinf
  obtain ⟨⟨νv, hνv⟩, a4⟩ := a3 μv hμv
  obtain ⟨⟨fibInf, hfi⟩, a5⟩ := a4 νv hνv
  obtain ⟨⟨fibV, hfv⟩, a6⟩ := a5 fibInf hfi
  have e1 := (a6 fibV hfv d b Φ Φinf Φf Φv hcΦ hcs hpure hprod).2.2
  have e2 := ((((((h2.2.2 μinf hμinf).2 νinf hνinf).2 μv hμv).2 νv hνv).2 fibInf hfi).2
    fibV hfv d b Φ Φinf Φf Φv hcΦ hcs hpure hprod).2.2
  rw [e1, e2]

end PI.VolStabSW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.RPGlue
section
noncomputable section

namespace PI.VolStabSW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Topology Filter
open scoped TensorProduct RestrictedProduct

namespace RestrictedProductGluing

open PositiveNearLattice

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {M a d : ℕ} (b : Module.Basis (Fin d) F E)

def good : Set ((Fin a → Fin M → Ainf F ⊗[F] E) ×
    (∀ v : HeightOneSpectrum (𝓞 F), Fin a → Fin M → Fv F v ⊗[F] E)) :=
  {p | ∀ᶠ v in cofinite, p.2 v ∈ latV b v}

def mkAf (x : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v)
    (h : ∀ᶠ v in cofinite, x v ∈ v.adicCompletionIntegers F) : Af F :=
  (⟨x, h⟩ : Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F])

omit [FiniteDimensional F E] in
theorem evalV_mkAf (x : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v)
    (h : ∀ᶠ v in cofinite, x v ∈ v.adicCompletionIntegers F) (v : HeightOneSpectrum (𝓞 F)) :
    evalV F v (mkAf x h) = x v := rfl

open Classical in

def finAd (p : (Fin a → Fin M → Ainf F ⊗[F] E) ×
    (∀ v : HeightOneSpectrum (𝓞 F), Fin a → Fin M → Fv F v ⊗[F] E)) (i : Fin a) (j : Fin M)
    (k : Fin d) : Af F :=
  if h : p ∈ good b then
    mkAf (fun v => crd b (Fv F v) (p.2 v i j) k)
      ((show ∀ᶠ v in cofinite, p.2 v ∈ latV b v from h).mono fun _ hv => hv i j k)
  else 0

def crdA (p : (Fin a → Fin M → Ainf F ⊗[F] E) ×
    (∀ v : HeightOneSpectrum (𝓞 F), Fin a → Fin M → Fv F v ⊗[F] E)) (i : Fin a) (j : Fin M)
    (k : Fin d) : AF F :=
  pairA F (crd b (Ainf F) (p.1 i j) k) (finAd b p i j k)

def glue (p : (Fin a → Fin M → Ainf F ⊗[F] E) ×
    (∀ v : HeightOneSpectrum (𝓞 F), Fin a → Fin M → Fv F v ⊗[F] E)) :
    Fin a → Fin M → AF F ⊗[F] E :=
  fun i j => (Algebra.TensorProduct.basis (AF F) b).equivFun.symm (fun k => crdA b p i j k)

theorem crd_glue (p : (Fin a → Fin M → Ainf F ⊗[F] E) ×
    (∀ v : HeightOneSpectrum (𝓞 F), Fin a → Fin M → Fv F v ⊗[F] E)) (i : Fin a) (j : Fin M)
    (k : Fin d) : crd b (AF F) (glue b p i j) k = crdA b p i j k := by
  show (Algebra.TensorProduct.basis (AF F) b).repr
      ((Algebra.TensorProduct.basis (AF F) b).equivFun.symm fun k => crdA b p i j k) k = _
  rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]

theorem measurableSet_good :
    MeasurableSet (good (F := F) (E := E) (M := M) (a := a) b) := by
  have e : good (F := F) (E := E) (M := M) (a := a) b = ⋃ S : Finset (HeightOneSpectrum (𝓞 F)),
      ⋂ v, ⋂ (_ : v ∉ S), {p | p.2 v ∈ latV b v} := by
    ext p
    simp only [good, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter, eventually_cofinite]
    constructor
    · intro h
      exact ⟨h.toFinset, fun v hv => by
        by_contra hc
        exact hv (h.mem_toFinset.2 hc)⟩
    · rintro ⟨S, hS⟩
      exact S.finite_toSet.subset fun v hv => by
        by_contra hc
        exact hv (hS v hc)
  rw [e]
  have : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  refine MeasurableSet.iUnion fun S => MeasurableSet.iInter fun v =>
    MeasurableSet.iInter fun _ => ?_
  exact ((measurable_pi_apply v).comp measurable_snd)
    (isClopen_latV b v a M).isOpen.measurableSet

def coeA (x : Af F) : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v := fun v => evalV F v x

theorem measurableEmbedding_coeA : MeasurableEmbedding (coeA (F := F)) := by
  have : BorelSpace (Af F) := ⟨rfl⟩
  have : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  have : PolishSpace (Af F) := TopoPolish.polish_of_lcsc (Af F)
  refine Continuous.measurableEmbedding ?_ ?_
  · exact continuous_pi fun v => by exact RestrictedProduct.continuous_eval v
  · intro x y h
    exact Subtype.ext (funext fun v => congrFun h v)

theorem measurable_finAd (i : Fin a) (j : Fin M) (k : Fin d) :
    Measurable (fun p : (Fin a → Fin M → Ainf F ⊗[F] E) ×
      (∀ v : HeightOneSpectrum (𝓞 F), Fin a → Fin M → Fv F v ⊗[F] E) => finAd b p i j k) := by
  classical
  have : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  refine (measurableEmbedding_coeA (F := F)).measurable_comp_iff.1 ?_
  have e : (coeA (F := F)) ∘ (fun p : (Fin a → Fin M → Ainf F ⊗[F] E) ×
      (∀ v : HeightOneSpectrum (𝓞 F), Fin a → Fin M → Fv F v ⊗[F] E) => finAd b p i j k) =
      (good b).piecewise (fun p v => crd b (Fv F v) (p.2 v i j) k) 0 := by
    funext p
    by_cases hp : p ∈ good b
    · funext v
      rw [Set.piecewise_eq_of_mem _ _ _ hp]
      simp only [Function.comp, coeA]
      rw [finAd, dif_pos hp, evalV_mkAf]
    · funext v
      rw [Set.piecewise_eq_of_notMem _ _ _ hp]
      simp only [Function.comp, coeA, Pi.zero_apply]
      rw [finAd, dif_neg hp, map_zero]
  rw [e]
  refine Measurable.piecewise (measurableSet_good b) ?_ measurable_const
  exact measurable_pi_lambda _ fun v => (continuous_crd b (Fv F v) k).measurable.comp
    ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp
      ((measurable_pi_apply v).comp measurable_snd)))

theorem measurable_crdA (i : Fin a) (j : Fin M) (k : Fin d) :
    Measurable (fun p : (Fin a → Fin M → Ainf F ⊗[F] E) ×
      (∀ v : HeightOneSpectrum (𝓞 F), Fin a → Fin M → Fv F v ⊗[F] E) => crdA b p i j k) := by
  have : BorelSpace (Ainf F) := ⟨rfl⟩
  have : BorelSpace (Af F) := ⟨rfl⟩
  have : BorelSpace (AF F) := ⟨rfl⟩
  have hc : Continuous (fun q : Ainf F × Af F => pairA F q.1 q.2) := continuous_id
  have hx : Measurable (fun p : (Fin a → Fin M → Ainf F ⊗[F] E) ×
      (∀ v : HeightOneSpectrum (𝓞 F), Fin a → Fin M → Fv F v ⊗[F] E) =>
      crd b (Ainf F) (p.1 i j) k) :=
    (continuous_crd b (Ainf F) k).measurable.comp
      ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_fst))
  exact hc.measurable.comp (hx.prodMk (measurable_finAd b i j k))

theorem measurable_glue :
    Measurable (glue (F := F) (E := E) (M := M) (a := a) b) := by
  have : BorelSpace (AF F) := ⟨rfl⟩
  have : BorelSpace (AF F ⊗[F] E) := ⟨rfl⟩
  have hL : Continuous (Algebra.TensorProduct.basis (AF F) b).equivFun.symm :=
    IsModuleTopology.continuous_of_linearMap
      ((Algebra.TensorProduct.basis (AF F) b).equivFun.symm.toLinearMap)
  exact measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j =>
    hL.measurable.comp (measurable_pi_lambda _ fun k => measurable_crdA b i j k)

theorem glue_spec (p : (Fin a → Fin M → Ainf F ⊗[F] E) ×
    (∀ v : HeightOneSpectrum (𝓞 F), Fin a → Fin M → Fv F v ⊗[F] E)) (hp : p ∈ good b) :
    projInf (glue b p) = p.1 ∧ ∀ v, projV v (projFin (glue b p)) = p.2 v := by
  refine ⟨?_, fun v => ?_⟩
  · funext i j
    refine (Algebra.TensorProduct.basis (Ainf F) b).ext_elem fun k => ?_
    show crd b (Ainf F) (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (glue b p i j)) k =
      crd b (Ainf F) (p.1 i j) k
    rw [crd_map, crd_glue]
    rfl
  · funext i j
    refine (Algebra.TensorProduct.basis (Fv F v) b).ext_elem fun k => ?_
    show crd b (Fv F v) (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)
      (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (glue b p i j))) k =
      crd b (Fv F v) (p.2 v i j) k
    rw [crd_map, crd_map, crd_glue]
    show evalV F v (finAd b p i j k) = _
    rw [finAd, dif_pos hp, evalV_mkAf]

end RestrictedProductGluing

theorem rpGlue_holds : RPGlue := by
  intro F E _ _ _ _ _ M a d b
  exact ⟨RestrictedProductGluing.glue b, RestrictedProductGluing.measurable_glue b,
    fun p hp => RestrictedProductGluing.glue_spec b p hp⟩

end PI.VolStabSW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.RestrProdG
section
noncomputable section

namespace PI.VolStabSW.RestrProdG

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

section Maps

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R S : Type} [CommRing R] [Algebra F R]
  [CommRing S] [Algebra F S]

theorem map_sigR (f : R →ₐ[F] S) (σ : E →ₐ[F] E) (z : R ⊗[F] E) :
    Algebra.TensorProduct.map f (AlgHom.id F E) (sigR R σ z) =
      sigR S σ (Algebra.TensorProduct.map f (AlgHom.id F E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [sigR, Algebra.TensorProduct.map_tmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

theorem map_inclR (f : R →ₐ[F] S) (e : E) :
    Algebra.TensorProduct.map f (AlgHom.id F E) (inclR R e) = inclR S e := by
  simp [inclR, Algebra.TensorProduct.map_tmul]

theorem map_gramR (f : R →ₐ[F] S) (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → R ⊗[F] E) (x y : Fin n) :
    Algebra.TensorProduct.map f (AlgHom.id F E) (gramR R σ J X x y) =
      gramR S σ J (fun x i => Algebra.TensorProduct.map f (AlgHom.id F E) (X x i)) x y := by
  simp only [gramR, hR, Formalism.UG.hform, JR, Matrix.map_apply, map_sum, map_mul, map_sigR,
    map_inclR]

end Maps

theorem t2_tensor_product {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] (R : Type)
    [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] :
    T2Space (R ⊗[F] E) := by
  let b := Module.finBasis F E
  refine T2Space.of_injective_continuous
    (f := fun y : R ⊗[F] E => fun k => PositiveNearLattice.crd b R y k) ?_
    (continuous_pi fun k => PositiveNearLattice.continuous_crd b R k)
  intro y y' h
  have h' : ∀ k, PositiveNearLattice.crd b R y k = PositiveNearLattice.crd b R y' k := fun k => congrFun h k
  rw [PositiveNearLattice.eq_sum_crd b R y, PositiveNearLattice.eq_sum_crd b R y']
  simp only [h']

theorem rpGram_holds : RPGram := by
  intro F E _ _ _ _ _ σ M J a T
  let b := Module.finBasis F E
  refine ⟨?_, ?_, fun v => ?_, ?_⟩
  · have : T2Space (AF F ⊗[F] E) := t2_tensor_product (AF F)
    have : T2Space (Matrix (Fin a) (Fin a) (AF F ⊗[F] E)) :=
      inferInstanceAs (T2Space (Fin a → Fin a → AF F ⊗[F] E))
    exact (isClosed_singleton.preimage (continuous_gramR (AF F) σ J)).isOpen_compl.measurableSet
  · have : T2Space (Ainf F ⊗[F] E) := t2_tensor_product (Ainf F)
    have : T2Space (Matrix (Fin a) (Fin a) (Ainf F ⊗[F] E)) :=
      inferInstanceAs (T2Space (Fin a → Fin a → Ainf F ⊗[F] E))
    exact (isClosed_singleton.preimage (continuous_gramR (Ainf F) σ J)).measurableSet
  · have : LocallyCompactSpace (Fv F v) := locallyCompact_Fv F v
    have : T2Space (Fv F v ⊗[F] E) := t2_tensor_product (Fv F v)
    have : T2Space (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
      inferInstanceAs (T2Space (Fin a → Fin a → Fv F v ⊗[F] E))
    exact (isClosed_singleton.preimage (continuous_gramR (Fv F v) σ J)).measurableSet
  · intro X hI hV
    have key : ∀ w w' : AF F ⊗[F] E,
        Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) w =
          Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) w' →
        (∀ v, Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)
            (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) w) =
          Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)
            (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) w')) → w = w' := by
      intro w w' h1 h2
      rw [PositiveNearLattice.eq_sum_crd b (AF F) w, PositiveNearLattice.eq_sum_crd b (AF F) w']
      refine Finset.sum_congr rfl fun k _ => ?_
      congr 1
      have e1 := congrArg (fun u => PositiveNearLattice.crd b (Ainf F) u k) h1
      simp only [PositiveNearLattice.crd_map] at e1
      refine Prod.ext e1 (FiniteAdeleRing.ext (K := F) fun v => ?_)
      have e2 := congrArg (fun u => PositiveNearLattice.crd b (Fv F v) u k) (h2 v)
      simp only [PositiveNearLattice.crd_map] at e2
      exact e2
    funext x y
    refine key _ _ ?_ fun v => ?_
    · rw [map_gramR, Matrix.map_apply, map_inclR]
      exact congrFun (congrFun hI x) y
    · rw [map_gramR, map_gramR, Matrix.map_apply, map_inclR, map_inclR]
      exact congrFun (congrFun (hV v) x) y

end PI.VolStabSW.RestrProdG
end
end

