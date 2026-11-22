import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0004
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0071
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0078
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0079
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0244
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle0005
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0054
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0367
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0263
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0423
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0290
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotIsobaricRigid
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TeichmullerInertiaLabelCondition
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0105
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0115

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalTranslationCompCommutingOperator
section
open NumberField IsDedekindDomain Matrix

namespace GlobalTheory.LocFactor

open GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem glAf_ext {x y : GL (Fin a) (Af E)}
    (h : ∀ v : HeightOneSpectrum (𝓞 E), GeneralLinearGroup.map (pLoc E v) x = GeneralLinearGroup.map (pLoc E v) y) :
    x = y := by
  refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext (R := 𝓞 E) E fun v => ?_)
  have := congrArg (fun m : GL (Fin a) (v.adicCompletion E) => (m.val : Matrix (Fin a) (Fin a) (v.adicCompletion E)) i j) (h v)
  exact this

theorem locGL_comm_away (w : HeightOneSpectrum (𝓞 E)) (k : GL (Fin a) (Af E))
    (h : GL (Fin a) (w.adicCompletion E)) :
    locGL E a w h * ((locGL E a w (GeneralLinearGroup.map (pLoc E w) k))⁻¹ * k) =
      ((locGL E a w (GeneralLinearGroup.map (pLoc E w) k))⁻¹ * k) * locGL E a w h := by
  refine glAf_ext fun v => ?_
  simp only [map_mul, map_inv]
  by_cases hv : v = w
  · subst hv
    rw [pLoc_locGL, pLoc_locGL, inv_mul_cancel, mul_one, one_mul]
  · rw [pLoc_locGL_of_ne hv, pLoc_locGL_of_ne hv, inv_one, one_mul, one_mul, mul_one]

theorem op_eq_locRep_comp (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) (o : Op E a) :
    ∃ (g : GL (Fin a) (w.adicCompletion E)) (T : Module.End ℂ π.V),
      (∀ h, T ∘ₗ π.locRep w h = π.locRep w h ∘ₗ T) ∧ π.op o = π.locRep w g ∘ₗ T := by
  cases o with
  | fin k =>
    set kw := GeneralLinearGroup.map (pLoc E w) k
    set k' := (locGL E a w kw)⁻¹ * k
    refine ⟨kw, π.op (.fin k'), fun h => ?_, ?_⟩
    · refine LinearMap.ext fun φ => Subtype.ext ?_
      change rt E a (finGL E a k') (rt E a (finGL E a (locGL E a w h)) φ.1) =
        rt E a (finGL E a (locGL E a w h)) (rt E a (finGL E a k') φ.1)
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, ← map_mul, ← map_mul,
        locGL_comm_away]
    · refine LinearMap.ext fun φ => Subtype.ext ?_
      change rt E a (finGL E a k) φ.1 = rt E a (finGL E a (locGL E a w kw)) (rt E a (finGL E a k') φ.1)
      rw [← Module.End.mul_apply, ← map_mul, ← map_mul, mul_inv_cancel_left]
  | cpt k =>
    refine ⟨1, π.op (.cpt k), fun h => ?_, ?_⟩
    · refine LinearMap.ext fun φ => Subtype.ext ?_
      change rt E a (infGL E a (Unitary.toUnits k)) (rt E a (finGL E a (locGL E a w h)) φ.1) =
        rt E a (finGL E a (locGL E a w h)) (rt E a (infGL E a (Unitary.toUnits k)) φ.1)
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, infGL_comm]
    · rw [map_one]; rfl
  | lie X =>
    refine ⟨1, π.op (.lie X), fun h => ?_, ?_⟩
    · refine LinearMap.ext fun φ => Subtype.ext ?_
      change lie E a X (rt E a (finGL E a (locGL E a w h)) φ.1) =
        rt E a (finGL E a (locGL E a w h)) (lie E a X φ.1)
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, lie_rt_fin]
    · rw [map_one]; rfl

theorem exists_locRep_comp : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : GlobalTheory.CuspRep.CuspSub E a)
    (w : HeightOneSpectrum (𝓞 E)) (o : GlobalTheory.CuspRep.Op E a), ∃ (g : GL (Fin a) (w.adicCompletion E))
    (T : Module.End ℂ π.V), (∀ h, T ∘ₗ π.locRep w h = π.locRep w h ∘ₗ T) ∧ π.op o = π.locRep w g ∘ₗ T :=
  fun _ _ _ _ _ π w o => op_eq_locRep_comp π w o

end GlobalTheory.LocFactor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharCmEqOneOfTrivialDegreeOne
section
open NumberField IsDedekindDomain HeckeValGen GlobalTheory.HeckeSplit

namespace GlobalTheory.HeckeSplit

theorem heckeChar_eq_one_of_degOne : ∀ (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E]
    [Algebra.IsQuadraticExtension F E] (χ : Ideles E →* ℂˣ), IsHeckeChar E χ →
    (∀ᶠ w in Filter.cofinite, DegOne F w → TrivAt χ w) → χ = 1 := by
  intro F E _ _ _ _ _ _ _ _ χ hχ hdeg
  have hinf := GlobalTheory.T.heckeChar_inf_trivial_of_trivAt_degOne F E χ hχ hdeg
  have hfin := GlobalTheory.T.heckeChar_trivialAtPlace_of_degOne_cofinite_trivial F E χ hχ hdeg hinf
  ext1 x
  have hfact := (GlobalTheory.T.continuous_ideleChar_local_factorization E χ hχ.1).2.2 x ∅ (fun v _ => hfin v _)
  rw [hfact, hinf]
  simp

end GlobalTheory.HeckeSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntegralDetOfStable
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Ker GlobalTheory.RatEqui

namespace GlobalTheory.DetStab

theorem isIntegral_det_of_stable {R E : Type} [CommRing R] [IsNoetherianRing R] [Field E] [Algebra R E] {n : ℕ}
    (L : Submodule R (Fin n → E)) (hfg : L.FG) (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (γ : Matrix (Fin n) (Fin n) E) (hγ : ∀ v ∈ L, γ.mulVec v ∈ L) : IsIntegral R γ.det := by
  classical
  let N : Submodule R E := Submodule.span R {x | ∃ w : Fin n → L, x = (Matrix.of fun i => (w i : Fin n → E)).det}
  let M : Submodule R E := ⨆ j : Fin n, L.map (LinearMap.proj j : (Fin n → E) →ₗ[R] E)
  have hM : M.FG := Submodule.fg_iSup _ fun j => hfg.map (LinearMap.proj j : (Fin n → E) →ₗ[R] E)
  have hprod : ∀ (s : Finset (Fin n)) (f : Fin n → E), (∀ i, f i ∈ M) → ∏ i ∈ s, f i ∈ M ^ s.card := by
    intro s f hf
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.prod_empty, Finset.card_empty, pow_zero]
      exact Submodule.one_le.1 le_rfl
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ']
      exact Submodule.mul_mem_mul (hf a) ih
  have hle : N ≤ M ^ (Finset.univ : Finset (Fin n)).card := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨w, rfl⟩
    rw [SetLike.mem_coe, Matrix.det_apply]
    refine Submodule.sum_mem _ fun σ _ => ?_
    rw [Units.smul_def]
    refine Submodule.smul_of_tower_mem _ _ (hprod _ _ fun i => ?_)
    exact Submodule.mem_iSup_of_mem i ⟨_, (w (σ i)).2, rfl⟩
  have hN : N.FG := (hM.pow _).of_le hle
  have hne : N ≠ ⊥ := by
    intro h
    have h0 : (Matrix.detRowAlternating (n := Fin n) (R := E)).toMultilinearMap = 0 := by
      refine MultilinearMap.ext_of_span_eq_top (g := fun _ (x : L) => (x : Fin n → E)) (fun _ => ?_) fun w => ?_
      · rw [← hsp]; congr 1; exact Subtype.range_coe
      · have : (Matrix.of fun i => (w i : Fin n → E)).det ∈ N := Submodule.subset_span ⟨w, rfl⟩
        rw [h] at this
        exact this
    have h1 := congrArg (fun f => f (1 : Matrix (Fin n) (Fin n) E)) h0
    have h2 : (1 : Matrix (Fin n) (Fin n) E).det = 0 := h1
    simp at h2
  refine isIntegral_of_smul_mem_submodule N hne hN _ fun x hx => ?_
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    refine Submodule.subset_span ⟨fun i => ⟨γ.mulVec (w i), hγ _ (w i).2⟩, ?_⟩
    rw [smul_eq_mul, mul_comm, ← Matrix.det_transpose γ, ← Matrix.det_mul]
    congr 1
    ext i j
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact N.add_mem hx hy
  | smul r x _ hx => rw [smul_comm]; exact N.smul_mem r hx

theorem prod_emb_det_eq_one (D : D7) (χ : IdE D → ℂ) (hχ : IsChi D χ) (n : ℕ)
    (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (hL : SD D L) (γ : Matrix (Fin n) (Fin n) D.host.E)
    (hu : γ * adj D γ = 1) (hs : ∀ v, v ∈ L ↔ γ.mulVec v ∈ L) : ∏ τ, embT D τ γ.det = 1 := by
  letI := D.host.cmStar
  obtain ⟨hfg, hsp, -⟩ := hL
  have hstar : ∀ x : D.host.E, star x = D.host.conj x := by
    intro x
    haveI := D.host.isCMField_hostE
    apply D.host.φ₀.injective
    rw [Formalism.HC.HostAx.conjE_apply]
    exact IsCMField.complexEmbedding_complexConj D.host.E D.host.φ₀ x
  have hd : γ.det * (adj D γ).det = 1 := by rw [← Matrix.det_mul, hu, Matrix.det_one]
  have hadj : (adj D γ).det = D.host.conj γ.det := by
    unfold adj
    rw [Matrix.det_transpose]
    exact (RingHom.map_det (D.host.conj : D.host.E →+* D.host.E) γ).symm
  have hz : γ.det ∈ unitary D.host.E := by
    rw [Unitary.mem_iff, hstar, ← hadj]
    exact ⟨by rw [mul_comm, hd], hd⟩
  have i1 := isIntegral_det_of_stable L hfg hsp γ fun v hv => (hs v).1 hv
  have i2 := isIntegral_det_of_stable L hfg hsp (adj D γ) fun v hv => (hs _).2 (by
    rw [Matrix.mulVec_mulVec, hu, Matrix.one_mulVec]; exact hv)
  obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (R := 𝓞 D.host.E)).1 i1
  obtain ⟨b, hb⟩ := (IsIntegrallyClosed.isIntegral_iff (R := 𝓞 D.host.E)).1 i2
  have hspan : Submodule.span (𝓞 D.host.E) {γ.det} = Submodule.span (𝓞 D.host.E) {(1 : D.host.E)} := by
    apply le_antisymm
    · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
      exact ⟨a, by rw [Algebra.smul_def, ha, mul_one]⟩
    · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
      exact ⟨b, by rw [Algebra.smul_def, hb, mul_comm, hd]⟩
  have e1 := hχ.2 ⟨γ.det, hz⟩
  have e2 := hχ.2 1
  have e3 : ∏ τ, (embT D τ γ.det)⁻¹ = 1 := by
    have e1' : χ (Submodule.span (𝓞 D.host.E) {γ.det}) = ∏ τ, (embT D τ γ.det)⁻¹ := e1
    have e2' : χ (Submodule.span (𝓞 D.host.E) {(1 : D.host.E)}) = ∏ τ, (embT D τ 1)⁻¹ := e2
    rw [← e1', hspan, e2']
    simp
  rwa [Finset.prod_inv_distrib, inv_eq_one] at e3

end GlobalTheory.DetStab
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsRBasisOfLocBasis
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions

noncomputable section

namespace GlobalTheory.JetTieCompare

open GlobalTheory.IndefiniteRowSideFullHecke.IntegralJetEntries (IsRBasis)

variable {p : ℕ} [Fact p.Prime]

theorem mem_int_iff (x : ℂ_[p]) : x ∈ 𝓞_ℂ_[p] ↔ ‖x‖ ≤ 1 := by
  rw [PadicComplexInt, Valuation.mem_valuationSubring_iff, PadicComplex.norm_eq_norm, Valuation.norm_def,
    PadicComplex.RankOne.hom_eq_embedding, Valuation.embedding_restrict]
  exact_mod_cast Iff.rfl

theorem norm_int_le {E : Type} [Field E] (ρ : E →+* ℂ_[p]) (x : 𝓞 E) : ‖ρ (x : E)‖ ≤ 1 := by
  have h : IsIntegral 𝓞_ℂ_[p] (ρ (x : E)) :=
    IsIntegral.map_of_comp_eq (Int.castRingHom _) ρ (RingHom.ext_int _ _) x.isIntegral_coe
  exact (mem_int_iff _).1 ((PadicComplexInt.integers p).mem_of_integral h)

theorem exists_denom {E : Type} [Field E] [NumberField E] (ρ : E →+* ℂ_[p]) (x : E) (hx : ‖ρ x‖ ≤ 1) :
    ∃ s n : 𝓞 E, ‖ρ (s : E)‖ = 1 ∧ (s : E) * x = n := by
  let I : Ideal (𝓞 E) :=
    { carrier := {y | ‖ρ (y : E)‖ < 1}
      zero_mem' := by simp
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_add] at ha hb ⊢
        exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
      smul_mem' := fun c {a} ha => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul, norm_mul] at ha ⊢
        exact mul_lt_one_of_nonneg_of_lt_one_right (norm_int_le ρ c) (norm_nonneg _) ha }
  have hI : ∀ y : 𝓞 E, y ∉ I ↔ ‖ρ (y : E)‖ = 1 := fun y =>
    ⟨fun h => le_antisymm (norm_int_le ρ y) (not_lt.1 h), fun h h' => absurd h (ne_of_lt h')⟩
  have hp : I.IsPrime := by
    refine ⟨(Ideal.ne_top_iff_one _).2 ((hI 1).2 (by simp)), fun {a b} hab => ?_⟩
    by_contra hc
    rw [not_or, hI, hI] at hc
    exact (hI (a * b)).2 (by simp [hc.1, hc.2]) hab
  have hpI : ((p : ℕ) : 𝓞 E) ∈ I := by
    change ‖ρ (((p : ℕ) : 𝓞 E) : E)‖ < 1
    have : ρ (((p : ℕ) : 𝓞 E) : E) = algebraMap ℚ_[p] ℂ_[p] (p : ℚ_[p]) := by simp
    rw [this, norm_algebraMap']
    exact Padic.norm_p_lt_one
  have hne : I ≠ ⊥ := fun h => by
    rw [h, Ideal.mem_bot] at hpI
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast hpI)
  obtain ⟨n, d, h | h⟩ := (⟨I, hp, hne⟩ : HeightOneSpectrum (𝓞 E)).exists_primeCompl_mul_eq_or_mul_eq (K := E) x
  · exact ⟨d, n, (hI _).1 d.2, by rw [mul_comm]; exact h⟩
  · refine ⟨n, d, le_antisymm (norm_int_le ρ n) ?_, by rw [mul_comm]; exact h⟩
    have h1 : ‖ρ x‖ * ‖ρ (n : E)‖ = 1 := by
      rw [← norm_mul, ← map_mul, ← (hI _).1 d.2]
      exact congrArg (fun y => ‖ρ y‖) h
    nlinarith [norm_nonneg (ρ (n : E)), norm_nonneg (ρ x)]

theorem exists_common_denom {E : Type} [Field E] [NumberField E] (ρ : E →+* ℂ_[p]) {N : ℕ} (x : Fin N → E)
    (hx : ∀ a, ‖ρ (x a)‖ ≤ 1) : ∃ (s : 𝓞 E) (n : Fin N → 𝓞 E), ‖ρ (s : E)‖ = 1 ∧ ∀ a, (s : E) * x a = n a := by
  classical
  choose s n hs hn using fun a => exists_denom ρ (x a) (hx a)
  refine ⟨∏ a, s a, fun a => (∏ b ∈ Finset.univ.erase a, s b) * n a, ?_, fun a => ?_⟩
  · have : ((∏ a, s a : 𝓞 E) : E) = ∏ a, (s a : E) := map_prod (algebraMap (𝓞 E) E) _ _
    rw [this, map_prod, norm_prod]
    exact Finset.prod_eq_one fun a _ => hs a
  · rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ a)]
    change algebraMap (𝓞 E) E (_ * _) * _ = algebraMap (𝓞 E) E (_ * _)
    rw [map_mul, map_mul, mul_assoc]
    exact congrArg _ (hn a)

theorem exists_locBasis (D : D7) (ρ : D.host.E →+* ℂ_[p]) {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (hfg : L.FG) (hsp : Submodule.span D.host.E (L : Set (Fin N → D.host.E)) = ⊤) :
    ∃ P, TaylorLogMetric.LocBasisW D ρ L P := by
  classical
  obtain ⟨s, rfl⟩ := hfg
  rw [Submodule.span_span_of_tower] at hsp
  let M : (Fin N → s) → Matrix (Fin N) (Fin N) D.host.E := fun f => Matrix.of fun k a => (f a).1 k
  obtain ⟨f₀, hf₀⟩ : ∃ f, (M f).det ≠ 0 := by
    obtain ⟨b, hbs, hb, hli⟩ := exists_linearIndependent D.host.E (s : Set (Fin N → D.host.E))
    let B : Module.Basis b D.host.E (Fin N → D.host.E) := Module.Basis.mk hli (by simp [hb, hsp])
    let e := B.indexEquiv (Pi.basisFun D.host.E (Fin N))
    refine ⟨fun a => ⟨(e.symm a).1, hbs (e.symm a).2⟩, ?_⟩
    have h := (Matrix.linearIndependent_cols_iff_isUnit (A := M fun a => ⟨(e.symm a).1, hbs (e.symm a).2⟩)).1
      (hli.comp _ e.symm.injective)
    exact ((Matrix.isUnit_iff_isUnit_det _).1 h).ne_zero
  haveI : Nonempty (Fin N → s) := ⟨f₀⟩
  obtain ⟨f, hf⟩ := Finite.exists_max fun f => ‖ρ (M f).det‖
  have hpos : 0 < ‖ρ (M f).det‖ := lt_of_lt_of_le (norm_pos_iff.2 ((map_ne_zero ρ).2 hf₀)) (hf f₀)
  have hdet : (M f).det ≠ 0 := (map_ne_zero ρ).1 (norm_pos_iff.1 hpos)
  refine ⟨M f, hdet, fun a => ⟨1, by simp, ?_⟩, fun x hx => ?_⟩
  · rw [one_smul]
    exact Submodule.subset_span (f a).2
  · have key : ∃ c : Fin N → D.host.E, (∀ a, ‖ρ (c a)‖ ≤ 1) ∧ x = (M f).mulVec c := by
      induction hx using Submodule.span_induction with
      | mem y hy =>
        refine ⟨((M f).det)⁻¹ • (M f).cramer y, fun a => ?_, ?_⟩
        · have h1 : (M f).updateCol a y = M (Function.update f a ⟨y, hy⟩) := by
            ext k b
            by_cases hb : b = a
            · subst hb; simp [M]
            · simp [M, Matrix.updateCol_ne hb, Function.update_of_ne hb]
          rw [Pi.smul_apply, smul_eq_mul, Matrix.cramer_apply, h1, map_mul, map_inv₀, norm_mul, norm_inv,
            inv_mul_le_iff₀ hpos, mul_one]
          exact hf _
        · rw [Matrix.mulVec_smul, Matrix.mulVec_cramer, smul_smul, inv_mul_cancel₀ hdet, one_smul]
      | zero => exact ⟨0, by simp, by simp⟩
      | add y z _ _ hy hz =>
        obtain ⟨c, hc, rfl⟩ := hy
        obtain ⟨c', hc', rfl⟩ := hz
        refine ⟨c + c', fun a => ?_, by rw [Matrix.mulVec_add]⟩
        rw [Pi.add_apply, map_add]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hc a) (hc' a))
      | smul r y _ hy =>
        obtain ⟨c, hc, rfl⟩ := hy
        refine ⟨(r : D.host.E) • c, fun a => ?_, by rw [Matrix.mulVec_smul]; rfl⟩
        rw [Pi.smul_apply, smul_eq_mul, map_mul, norm_mul]
        exact mul_le_one₀ (norm_int_le ρ r) (norm_nonneg _) (hc a)
    obtain ⟨c, hc, rfl⟩ := key
    obtain ⟨t, n, ht, hn⟩ := exists_common_denom ρ c hc
    refine ⟨t, ht, n, ?_⟩
    funext k
    rw [Finset.sum_apply]
    change (t : D.host.E) * (∑ a, M f k a * c a) = ∑ a, (n a : D.host.E) * M f k a
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [← hn a]; ring

theorem isRBasis_of_locBasis (D : D7) (ρ : D.host.E →+* ℂ_[p]) {N : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {P : Matrix (Fin N) (Fin N) D.host.E} (h : TaylorLogMetric.LocBasisW D ρ L P) : IsRBasis D ρ L (P.map ρ) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)⟩
  · have := ρ.map_det P
    rw [RingHom.mapMatrix_apply] at this
    rw [← this]
    exact (map_ne_zero ρ).2 h1
  · rintro _ ⟨a, rfl⟩
    obtain ⟨s, hs, hL⟩ := h2 a
    have h0 : ρ (s : D.host.E) ≠ 0 := norm_pos_iff.1 (by rw [hs]; exact one_pos)
    have hm := Submodule.smul_mem _ (⟨(ρ (s : D.host.E))⁻¹, (mem_int_iff _).2 (by rw [norm_inv, hs, inv_one])⟩ : 𝓞_ℂ_[p])
      (Submodule.subset_span (R := 𝓞_ℂ_[p])
        (Set.mem_image_of_mem (fun (x : Fin N → D.host.E) k => ρ (x k)) (show _ ∈ (L : Set _) from hL)))
    refine Set.mem_of_eq_of_mem (funext fun k => ?_) hm
    change ρ (P k a) = (ρ (s : D.host.E))⁻¹ * ρ ((s : D.host.E) * P k a)
    rw [map_mul, inv_mul_cancel_left₀ h0]
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨s, hs, c, hc⟩ := h3 x hx
    have h0 : ρ (s : D.host.E) ≠ 0 := norm_pos_iff.1 (by rw [hs]; exact one_pos)
    refine (Submodule.mem_span_range_iff_exists_fun _).2
      ⟨fun a => ⟨(ρ (s : D.host.E))⁻¹ * ρ (c a : D.host.E), (mem_int_iff _).2 ?_⟩, ?_⟩
    · rw [norm_mul, norm_inv, hs, inv_one, one_mul]
      exact norm_int_le ρ _
    · funext k
      have hk := congrFun hc k
      rw [Finset.sum_apply] at hk ⊢
      change (s : D.host.E) * x k = ∑ a, (c a : D.host.E) * P k a at hk
      change ∑ a, (ρ (s : D.host.E))⁻¹ * ρ (c a : D.host.E) * ρ (P k a) = ρ (x k)
      simp only [mul_assoc, ← map_mul, ← Finset.mul_sum, ← map_sum]
      rw [← hk, map_mul, inv_mul_cancel_left₀ h0]

theorem transition_integral (D : D7) (ρ : D.host.E → ℂ_[p]) {N : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {g h : Matrix (Fin N) (Fin N) ℂ_[p]} (hg : IsRBasis D ρ L g) (hh : IsRBasis D ρ L h) (a b : Fin N) :
    ‖(h⁻¹ * g) a b‖ ≤ 1 := by
  have h1 : (fun k => g k b) ∈ Submodule.span 𝓞_ℂ_[p] (Set.range fun a : Fin N => fun k => h k a) := by
    rw [hh.2, ← hg.2]
    exact Submodule.subset_span ⟨b, rfl⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h1
  have h2 : (fun k => g k b) = h.mulVec fun a => (c a : ℂ_[p]) := by
    rw [← hc]
    funext k
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  have h3 : (h⁻¹ * g) a b = (h⁻¹.mulVec fun k => g k b) a := rfl
  rw [h3, h2, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (Ne.isUnit hh.1), Matrix.one_mulVec]
  exact (mem_int_iff _).1 (c a).2

theorem exists_tauHom (D : D7) (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) :
    ∃ ρ : D.host.E →+* ℂ_[p], TaylorLogMetric.tauEmb D lam τ = ρ := by
  have h : ∀ x, TaylorLogMetric.embT D τ x ∈ TaylorLogMetric.Qbar := fun x =>
    mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom (TaylorLogMetric.embT D τ).toRatAlgHom)
  refine ⟨lam.comp ((TaylorLogMetric.embT D τ).codRestrict TaylorLogMetric.Qbar h), funext fun x => ?_⟩
  rw [TaylorLogMetric.tauEmb, TaylorLogMetric.lamC, dif_pos (h x)]
  rfl

end GlobalTheory.JetTieCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JumpWindowBlockExponentConditionOfJumpWindow
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.BlockWindow

theorem jointTB_of_jumpWindow : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (h₁ : ℕ), D.nd.l i ∉ D.host.small → D.nd.l i ≠ D.host.q → D.nd.l i ≠ D.host.d → D.R.t ≤ h₁ → GlobalTheory.BlockWindow.JumpWindow D i r π h₁ → GlobalTheory.BlockWindow.JointTB D HW F i r π h₁ h₁ (GlobalTheory.HubLoc.cBnum (D.nd.l i) h₁ D.R.t (4 * D.R.n * D.R.nV)) := by
  intro D HW F i r π h₁ hsm hq hd ht hJ
  have h2 : D.nd.l i ≠ 2 := fun e => hsm (e ▸ D.host.toHostRaw.two_mem_small)
  refine ⟨h2, fun w hw => ?_⟩
  obtain ⟨hK0, hK1, -⟩ := GlobalTheory.HubLoc.localField_unramified D i hsm hq hd w hw
  have hKur : (D.nbr i w hw).Kw.1 ≤ MaximalUnramifiedExtension (D.nd.l i) := by
    rw [← hK0]; exact inf_le_right
  refine ⟨GlobalTheory.BridgeInertia.inertEq D i w hw, hK1, fun CL h hs Y hc hY => ?_⟩
  have hs1 : (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 CL hs).W.s = 1 :=
    (HW (D.nd.l i)).W_s _ 1 _ hs
  have hell : LocalSituation.ell (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 CL hs) = D.nd.l i :=
    (D.loc (D.nd.l i)).PD_p _
  haveI : CharZero (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 CL hs).Qp :=
    inferInstanceAs (CharZero ℚ_[D.nd.l i])
  haveI : FiniteDimensional (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 CL hs).Qp
      (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 CL hs).K := (D.nbr i w hw).Kw.2
  have hcard : Nat.card (↥(D.nbr i w hw).Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥CL.1) =
      Module.finrank ℚ_[D.nd.l i] ↥(D.nbr i w hw).Kw.1 :=
    GlobalTheory.HubLoc.card_emb _ _ fun τ x => h ((D.nbr i w hw).LL_split τ x)
  have hdeg := GlobalTheory.bridge_finrank_le D i w hw
  obtain ⟨hv1, hv2⟩ := GlobalTheory.HubLoc.padicValNat_finrank_Ks (D.nd.l i) (D.nbr i w hw).Kw
  have hgK : LocalSituation.gK (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 CL hs) = 0 := by
    unfold LocalSituation.gK
    rw [hs1, hell]
    exact hv2 hKur
  have hvd : ∀ m : ℕ, 0 < m → LocalSituation.vdegMs (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 CL hs) m = m - 1 := by
    intro m hm
    unfold LocalSituation.vdegMs
    rw [hs1, hell]
    exact hv1 m hm
  have key := GlobalTheory.T.jumpWindow_and_blockExponent_of_embeddings (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 CL hs) Y h₁ D.R.nV (4 * D.R.n) D.R.t
    hs1 hcard hdeg hgK (hvd _ (by unfold LocalSituation.mN; omega)) ht (fun τ => by
      obtain ⟨U, hU1, hU2, hU3⟩ := hJ w hw CL h τ
      exact ⟨U, hU1, hU2, fun a ha => hU3 a (hY τ a ha)⟩)
  refine ⟨key.1, fun e he => (key.2 e he).trans (le_of_eq ?_)⟩
  rw [hell]

end GlobalTheory.BlockWindow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LabelSettingTameGenerator
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.WeilDeligne Formalism.CyclotomicNorms

namespace GlobalTheory.LabLaws

section WDLaws

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver B w}
variable {g : ℕ} [Fact g.Prime]

theorem lab_lpTw (τ : Fbar g →* ℂ) (γ : G E Ω) (a : WD h) (s : ℝ) :
    WD.lab τ γ (a.lpTw s) = WD.lab τ γ a :=
  WD.lab_lpTw τ γ a s

theorem natDegree_lab_le (τ : Fbar g →* ℂ) (γ : G E Ω) (a : WD h) :
    (WD.lab τ γ a).natDegree ≤ a.lpDim :=
  WD.natDegree_lab_le τ γ a

end WDLaws

section Comparison₂

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}

def LabTie (T : GlobalTheory.RowTie.WDTie N A) (τ : ∀ k, Fb (H.g k) (H.g_prime k) →* ℂ)
    (γ : Fin 2 → PlE H → G H.E N.Om) : Prop :=
  ∀ (k : Fin 2) (v : N.PlG k),
    haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩
    IsTeich (τ k) ∧ TameGenAt (N.plOm.1 (A.plGw k v)) (γ k (A.plGw k v)) ∧
      ∀ a : A.LP (A.plGw k v), A.items₂ k (A.plGw k v) a = WD.lab (τ k) (γ k (A.plGw k v)) (T.e _ a)

theorem tieLab_of_labTie {T : GlobalTheory.RowTie.WDTie N A} {τ : ∀ k, Fb (H.g k) (H.g_prime k) →* ℂ}
    {γ : Fin 2 → PlE H → G H.E N.Om} (hT : LabTie T τ γ) : GlobalTheory.RowCopy.TieLab N A := by
  refine ⟨fun k v a s => ?_, fun k v a => ?_⟩
  · haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩
    rw [(hT k v).2.2, (hT k v).2.2, T.tw, WD.lab_lpTw]
  · haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩
    rw [(hT k v).2.2, ← T.dim]
    exact WD.natDegree_lab_le _ _ _

theorem labTame_of_labTie {T : GlobalTheory.RowTie.WDTie N A} {τ : ∀ k, Fb (H.g k) (H.g_prime k) →* ℂ}
    {γ : Fin 2 → PlE H → G H.E N.Om} (hT : LabTie T τ γ) : GlobalTheory.RowTie.LabTame N A := by
  intro k v a ha σ hσ hw
  haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩
  rw [(hT k v).2.2, ← T.dim] at ha
  rw [T.inePol _ a σ hσ, ← T.dim]
  exact WD.inePol_wild_of_natDegree_lab ha hw

end Comparison₂

section Inhabited

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

end Inhabited

end GlobalTheory.LabLaws
end
end

