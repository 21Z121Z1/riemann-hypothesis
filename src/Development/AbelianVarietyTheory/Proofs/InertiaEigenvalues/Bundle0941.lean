import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0822
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0933
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0856
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0086
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0610
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0934
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0139
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0155
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0136
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0062
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0619
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0866
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemBddFormsOfWithSmoothings
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2045
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0796
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0350
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0958
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0717
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0239
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1055
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0193
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0705
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0935
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0937
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0030
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0821

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapVVSymmMapVV
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ExportSeries GlobalTheory.ConjTwist

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoefLatConj

open MvPolynomial GlobalTheory.SeriesTie.Scale

variable {D : D7} {n : ℕ}

def polLat {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K)) (O : Subring ℂ)
    (lam : D.what₂.Tau → DomWeight n) (M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Submodule O (VV ℂ lam) :=
  Submodule.span O {y | ∃ F ∈ nabAtr emb lam M, y = GlobalTheory.CoefModel.mapVV σ lam F}

theorem coefLatFn_eq {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K))
    (O : Subring ℂ) (lam : D.what₂.Tau → DomWeight n) (M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) :
    coefLatFn σ emb O lam M = (polLat σ emb O lam M).map ((coefLin lam).restrictScalars O) := by
  unfold coefLatFn polLat
  rw [Submodule.map_span]
  congr 1
  ext φ
  constructor
  · rintro ⟨F, hF, rfl⟩
    exact ⟨_, ⟨F, hF, rfl⟩, coefFn_map σ lam _⟩
  · rintro ⟨_, ⟨F, hF, rfl⟩, rfl⟩
    exact ⟨F, hF, coefFn_map σ lam _⟩

theorem polLat_conj {K : Type} [Field K] [NumberField K] {σ : K →+* ℂ} {emb : D.what₂.Tau → (D.host.E →+* K)}
    {O O' : Subring ℂ} {lam : D.what₂.Tau → DomWeight n} {M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (τ : ℂ ≃+* ℂ)
    (hτ : ∀ a : K, τ (σ a) = σ a) (hO : ∀ a ∈ O, τ a ∈ O') {y : VV ℂ lam} (hy : y ∈ polLat σ emb O lam M) :
    GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) lam y ∈ polLat σ emb O' lam M := by
  induction hy using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨F, hF, rfl⟩ := h
    refine Submodule.subset_span ⟨F, hF, Subtype.ext ?_⟩
    change MvPolynomial.map (τ : ℂ →+* ℂ) (MvPolynomial.map σ F.1) = MvPolynomial.map σ F.1
    rw [MvPolynomial.map_map, show (τ : ℂ →+* ℂ).comp σ = σ from RingHom.ext hτ]
  | zero => rw [map_zero]; exact zero_mem _
  | add _ _ _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
  | smul a y _ h1 =>
    have e : GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) lam (a • y) = (⟨τ a, hO a a.2⟩ : O') • GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) lam y := by
      rw [Subring.smul_def, Subring.smul_def, map_smulₛₗ]
      rfl
    rw [e]
    exact Submodule.smul_mem _ _ h1

theorem mapVV_symm_mapVV (lam : D.what₂.Tau → DomWeight n) (τ : ℂ ≃+* ℂ) (y : VV ℂ lam) :
    GlobalTheory.CoefModel.mapVV (τ.symm : ℂ →+* ℂ) lam (GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) lam y) = y := by
  refine Subtype.ext ?_
  change MvPolynomial.map (τ.symm : ℂ →+* ℂ) (MvPolynomial.map (τ : ℂ →+* ℂ) y.1) = y.1
  rw [MvPolynomial.map_map]
  have : (τ.symm : ℂ →+* ℂ).comp (τ : ℂ →+* ℂ) = RingHom.id ℂ := RingHom.ext fun a => τ.symm_apply_apply a
  rw [this, MvPolynomial.map_id]

section Base

variable {i : Fin D.R.m} {B : Base (Vc D i) (Wc D i)}

theorem pq_le (hB : B.Good) (τ : D.what₂.Tau) : B.w.p τ + B.w.q τ ≤ (Wc D i).rank := by
  obtain ⟨e, -⟩ := hB.sigOK (tauE D τ)
  rw [← hB.sig τ] at e
  have := Fintype.card_congr e
  simp only [Fintype.card_fin, Fintype.card_sum] at this
  omega

variable (Φ : VsV D i ℂ →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) {κ : ℂ}

theorem mem_coefLat_iff (hlam : B.w.lam = lamV D i) (hval : ∀ x, Φ x ∈ B.valSpace)
    (hκ : ∀ x : VsV D i ℂ, harmFn (Wc D i).rank B.w B.F.BS (Φ x) =
      κ • coefFn (RingHom.id ℂ) (lamV D i) (x : Pol ℂ D.what₂.Tau (Vc D i).rank))
    {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K)) (O : Subring ℂ)
    (h : Bridge.Gf (Vc D i)) (x : VsV D i ℂ) :
    Φ x ∈ B.coefLat σ emb O h ↔ κ • x ∈ polLat σ emb O (lamV D i) (B.latAt h) := by
  show Φ x ∈ harmLat σ emb O _ B.w B.F.BS (B.latAt h) ↔ _
  rw [mem_harmLat, hlam, coefLatFn_eq, Submodule.mem_map]
  constructor
  · rintro ⟨-, y, hy, he⟩
    have e : coefLin (lamV D i) y = coefLin (lamV D i) (κ • x) := by
      rw [map_smul]
      exact he.trans (hκ x)
    exact coefLin_injective _ e ▸ hy
  · intro hx
    refine ⟨hval x, κ • x, hx, ?_⟩
    change coefLin (lamV D i) (κ • x) = _
    rw [map_smul, hκ]
    rfl

theorem existsUnique_eq (hB : B.Good) (hlam : B.w.lam = lamV D i) (hκ0 : κ ≠ 0) (hval : ∀ x, Φ x ∈ B.valSpace)
    (hκ : ∀ x : VsV D i ℂ, harmFn (Wc D i).rank B.w B.F.BS (Φ x) =
      κ • coefFn (RingHom.id ℂ) (lamV D i) (x : Pol ℂ D.what₂.Tau (Vc D i).rank)) :
    ∀ P ∈ B.valSpace, ∃! x : VsV D i ℂ, P = Φ x := by
  intro P hP
  have h1 : harmFn (Wc D i).rank B.w B.F.BS P ∈ (harm (Wc D i).rank B.w B.F.BS).map (harmFn (Wc D i).rank B.w B.F.BS) :=
    Submodule.mem_map_of_mem hP
  rw [GlobalTheory.T.fockHarmonicValueSpace_map_eq_dualWeylModuleFunctions D _ _ B.w B.F.BS hB.wt (pq_le hB), hlam] at h1
  have hs : Submodule.span ℂ {φ | ∃ F : VV ℂ (lamV D i), φ = coefFn (RingHom.id ℂ) (lamV D i) (F : Pol ℂ D.what₂.Tau (Vc D i).rank)}
      ≤ LinearMap.range (coefLin (lamV D i)) :=
    Submodule.span_le.2 (by rintro _ ⟨F, rfl⟩; exact ⟨F, rfl⟩)
  obtain ⟨y, hy⟩ := hs h1
  have hy' : coefLin (lamV D i) y = harmFn (Wc D i).rank B.w B.F.BS P := hy
  have hv : ∀ x, harmFn (Wc D i).rank B.w B.F.BS (Φ x) = κ • coefLin (lamV D i) x := hκ
  refine ⟨κ⁻¹ • y, ?_, fun x hx => ?_⟩
  · have e : harmFn (Wc D i).rank B.w B.F.BS (Φ (κ⁻¹ • y) - P) = 0 := by
      rw [map_sub, hv, map_smul, smul_smul, mul_inv_cancel₀ hκ0, one_smul, hy', sub_self]
    exact (sub_eq_zero.1 (GlobalTheory.T.harmonic_polynomial_eq_zero_of_function D _ _ B.w B.F.BS hB.wt (pq_le hB) _ (sub_mem (hval _) hP) e)).symm
  · refine coefLin_injective (lamV D i) ?_
    have e := hv x
    rw [← hx, ← hy'] at e
    rw [map_smul, e, smul_smul, inv_mul_cancel₀ hκ0, one_smul]

theorem conj_mem_iff (hlam : B.w.lam = lamV D i) (hκ0 : κ ≠ 0) (hval : ∀ x, Φ x ∈ B.valSpace)
    (hκ : ∀ x : VsV D i ℂ, harmFn (Wc D i).rank B.w B.F.BS (Φ x) =
      κ • coefFn (RingHom.id ℂ) (lamV D i) (x : Pol ℂ D.what₂.Tau (Vc D i).rank))
    {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K)) (O : Subring ℂ)
    (τ : ℂ ≃+* ℂ) (hτ : ∀ a : K, τ (σ a) = σ a) (h : Bridge.Gf (Vc D i)) {x x' : VsV D i ℂ} (hx : ConjVec i τ x x') :
    Φ x ∈ B.coefLat σ emb O h ↔ Φ ((τ κ / κ) • x') ∈ B.coefLat σ emb (O.map (τ : ℂ →+* ℂ)) h := by
  rw [mem_coefLat_iff Φ hlam hval hκ, mem_coefLat_iff Φ hlam hval hκ]
  have hx' : x' = GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) (lamV D i) x := Subtype.ext hx
  have e : κ • ((τ κ / κ) • x') = GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) (lamV D i) (κ • x) := by
    rw [smul_smul, mul_div_cancel₀ _ hκ0, map_smulₛₗ, hx']
    rfl
  rw [e]
  constructor
  · exact polLat_conj τ hτ fun a ha => Subring.mem_map.2 ⟨a, ha, rfl⟩
  · intro h'
    have hτ' : ∀ a : K, τ.symm (σ a) = σ a := fun a => by rw [τ.symm_apply_eq, hτ]
    have := polLat_conj τ.symm hτ' (fun a ha => by
      obtain ⟨b, hb, rfl⟩ := Subring.mem_map.1 ha
      simpa using hb) h'
    rwa [mapVV_symm_mapVV] at this

theorem coefLat_eq_span (hB : B.Good) (hlam : B.w.lam = lamV D i) (hκ0 : κ ≠ 0) (hval : ∀ x, Φ x ∈ B.valSpace)
    (hκ : ∀ x : VsV D i ℂ, harmFn (Wc D i).rank B.w B.F.BS (Φ x) =
      κ • coefFn (RingHom.id ℂ) (lamV D i) (x : Pol ℂ D.what₂.Tau (Vc D i).rank))
    {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K)) (O : Subring ℂ)
    (h : Bridge.Gf (Vc D i)) :
    B.coefLat σ emb O h = Submodule.span O
      {P | ∃ F ∈ nabAtr emb (lamV D i) (B.latAt h), P = Φ (κ⁻¹ • GlobalTheory.CoefModel.mapVV σ (lamV D i) F)} := by
  let Ψ : VsV D i ℂ →ₗ[O] PolF D (Wc D i).rank (Vc D i).rank := (Φ ∘ₗ (κ⁻¹ • LinearMap.id)).restrictScalars O
  have hΨ : ∀ y, Ψ y = Φ (κ⁻¹ • y) := fun _ => rfl
  have e : B.coefLat σ emb O h = (polLat σ emb O (lamV D i) (B.latAt h)).map Ψ := by
    ext P
    constructor
    · intro hP
      obtain ⟨x, rfl, -⟩ := existsUnique_eq Φ hB hlam hκ0 hval hκ P (Submodule.mem_inf.1 hP).1
      refine ⟨κ • x, (mem_coefLat_iff Φ hlam hval hκ σ emb O h x).1 hP, ?_⟩
      rw [hΨ, smul_smul, inv_mul_cancel₀ hκ0, one_smul]
    · rintro ⟨y, hy, rfl⟩
      rw [hΨ, mem_coefLat_iff Φ hlam hval hκ, smul_smul, mul_inv_cancel₀ hκ0, one_smul]
      exact hy
  rw [e, polLat, Submodule.map_span]
  congr 1
  ext P
  constructor
  · rintro ⟨_, ⟨F, hF, rfl⟩, rfl⟩
    exact ⟨F, hF, rfl⟩
  · rintro ⟨F, hF, rfl⟩
    exact ⟨_, ⟨F, hF, rfl⟩, rfl⟩

end Base

end GlobalTheory.CoefLatConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OrbitalIntegralLinearDescentCutoff
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.LinDesc

theorem valuationParitySign_mul_self {F : Type} [NormedField F] (x : F) : eta x * eta x = 1 := by
  unfold eta; split_ifs <;> norm_num

theorem valuationParitySign_one {F : Type} [NormedField F] : eta (1 : F) = 1 := by
  unfold eta; rw [if_pos ⟨1, by simp⟩]

theorem desc_unit_eq {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F} (hG : A.IsGen τ p) (lam : F)
    (M : Meas r F E) (α : GL (Fin r) F → ℝ) (f' : Gl r F → ℂ) (a s : A.Kˣ) :
    desc A M hG lam α f' ((a : A.K) * Ring.inverse (s : A.K), (s : A.K)) * A.etaK s =
      A.etaK a * (letI := M.mG; ∫ g, f' (act g (pt A hG lam 1 a)) * eta ((g : Matrix (Fin r) (Fin r) F).det) *
        (α (g * tm A hG a⁻¹ * tm A hG s) : ℂ) ∂M.μG) := by
  letI := M.mG
  haveI := M.bG
  haveI : M.μG.IsMulRightInvariant := GlobalTheory.T.generalLinear_haar_isMulRightInvariant_unramified F E r M
  have hmul := (GlobalTheory.T.unramifiedValuationParitySign_character_kernel_norms F E).1
  set Y := pt A hG lam 1 (a : A.K) with hY
  set u : A.Kˣ := a * s⁻¹ with hu
  have hpt : pt A hG lam ((a : A.K) * Ring.inverse (s : A.K)) (s : A.K) = act (tm A hG u) Y := by
    rw [hY, act_tm, Ring.inverse_unit]
    congr 1
    · rw [hu, Units.val_mul, mul_one]
    · rw [hu, _root_.mul_inv_rev, inv_inv, Units.val_mul, mul_assoc, Units.inv_mul, mul_one]
  have h1 : desc A M hG lam α f' ((a : A.K) * Ring.inverse (s : A.K), (s : A.K)) =
      ∫ g, f' (act (g * tm A hG u) Y) * eta ((g : Matrix (Fin r) (Fin r) F).det) * (α g : ℂ) ∂M.μG := by
    unfold desc
    simp only [hpt, act_mul]
  have h2 : (∫ g, f' (act (g * tm A hG u) Y) * eta ((g : Matrix (Fin r) (Fin r) F).det) * (α g : ℂ) ∂M.μG) =
      ∫ g, f' (act g Y) * eta (((g * (tm A hG u)⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F).det) *
        (α (g * (tm A hG u)⁻¹) : ℂ) ∂M.μG := by
    have := integral_mul_right_eq_self (μ := M.μG) (fun h : GL (Fin r) F => f' (act h Y) *
      eta (((h * (tm A hG u)⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F).det) * (α (h * (tm A hG u)⁻¹) : ℂ)) (tm A hG u)
    simp only [mul_inv_cancel_right] at this
    exact this
  rw [h1, h2, ← integral_mul_const, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  have hui : (tm A hG u)⁻¹ = tm A hG a⁻¹ * tm A hG s := by
    rw [← map_inv, ← map_mul, hu, _root_.mul_inv_rev, inv_inv, mul_comm]
  have hdg : (g : Matrix (Fin r) (Fin r) F).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.ne_zero _
  have hN : ∀ t : A.Kˣ, Algebra.norm F (t : A.K) ≠ 0 := fun t =>
    (IsUnit.map (Algebra.norm F) (Units.isUnit t)).ne_zero
  have hdet : (((g * (tm A hG u)⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F).det) =
      (g : Matrix (Fin r) (Fin r) F).det * (Algebra.norm F ((a⁻¹ : A.Kˣ) : A.K) * Algebra.norm F (s : A.K)) := by
    rw [hui, Units.val_mul, Matrix.det_mul, ← map_mul, det_tm, Units.val_mul, map_mul]
  have h12 : eta (Algebra.norm F (a : A.K)) * eta (Algebra.norm F ((a⁻¹ : A.Kˣ) : A.K)) = 1 := by
    rw [← hmul _ _ (hN a) (hN a⁻¹), ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one, valuationParitySign_one]
  have h11 := valuationParitySign_mul_self (Algebra.norm F (a : A.K))
  have h33 := valuationParitySign_mul_self (Algebra.norm F (s : A.K))
  simp only []
  rw [hdet, hmul _ _ hdg (mul_ne_zero (hN _) (hN _)), hmul _ _ (hN _) (hN _), hui, ← _root_.mul_assoc g (tm A hG a⁻¹) (tm A hG s)]
  unfold Et.etaK
  set e1 := eta (Algebra.norm F (a : A.K))
  set e2 := eta (Algebra.norm F ((a⁻¹ : A.Kˣ) : A.K))
  set e3 := eta (Algebra.norm F (s : A.K))
  set d := eta ((g : Matrix (Fin r) (Fin r) F).det)
  set fv := f' (act g Y)
  set al : ℂ := (α (g * tm A hG a⁻¹ * tm A hG s) : ℂ)
  linear_combination (fv * d * al * e2) * h33 - (fv * d * al * e2) * h11 + (fv * d * al * e1) * h12

end GlobalTheory.JR.LinDesc

namespace GlobalTheory.JR.LinDesc

theorem orb_descent_unit : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (lam : F), ∀ (M : Meas r F E) (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ (α : GL (Fin r) F → ℝ) (f' : Gl r F → ℂ), IsTest f' → IsLocallyConstant α → HasCompactSupport α → (∀ g, 0 ≤ α g) → (∀ g : GL (Fin r) F, (∃ v w : Fin r → F, f' ((g : Matrix (Fin r) (Fin r) F) * companion p * ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F), v, w, lam) ≠ 0) → ∀ s₀ : A.Kˣ, ∫ s, α (g * LinDesc.tm A hG s₀ * LinDesc.tm A hG s) ∂(LinDesc.unitsMeas A μK) = 1) → ∀ κ₀ : ℂ, (∀ a : A.K, IsUnit a → ∀ g : GL (Fin r) F, omega (act g (LinDesc.pt A hG lam 1 a)) = κ₀ * eta ((g : Matrix (Fin r) (Fin r) F).det) * A.etaK a) → ∀ a : A.K, IsUnit a → orbG M f' (LinDesc.pt A hG lam 1 a) = κ₀ * A.orbK μK (LinDesc.desc A M hG lam α f') a := by
  intro F E _ _ _ _ _ A r τ p hG lam M μK hμK α f' hf' hαlc hαcs hα0 hcut κ₀ hκ a ha
  obtain ⟨a, rfl⟩ := ha
  letI := M.mG
  set Y := pt A hG lam 1 (a : A.K) with hY
  have hconv := (GlobalTheory.T.etaleUnitsHaarMeasureDivAbs_isHaarMeasure F E A μK hμK).2.2
    (fun t => desc A M hG lam α f' ((a : A.K) * Ring.inverse t, t) * A.etaK t)
  have hO : A.orbK μK (desc A M hG lam α f') (a : A.K) =
      ∫ s, desc A M hG lam α f' ((a : A.K) * Ring.inverse (s : A.K), (s : A.K)) * A.etaK s ∂(unitsMeas A μK) := by
    rw [hconv]; rfl
  set Φ : GL (Fin r) F → ℂ := fun g => f' (act g Y) * omega (act g Y) with hΦ
  have hΔ : Delta (inv Y) ≠ 0 := by
    rw [hY, pt_one, GlobalTheory.JR.NormalFormL.inv_sec']
    exact ((GlobalTheory.T.jacquetRallis_invK_regular_iff_isUnit F E A r τ p lam hG).2 (a : A.K)).2.2 (Units.isUnit a)
  have hΦt : IsTest Φ := (GlobalTheory.T.jacquetRallis_orbitalIntegrand_isLocallyConstantCompactSupport F E r M).1 f' hf' Y hΔ
  have hinner : ∀ s : A.Kˣ, κ₀ * (desc A M hG lam α f' ((a : A.K) * Ring.inverse (s : A.K), (s : A.K)) * A.etaK s) =
      ∫ g, Φ g * (α (g * tm A hG a⁻¹ * tm A hG s) : ℂ) ∂M.μG := by
    intro s
    rw [desc_unit_eq, ← mul_assoc, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    simp only [hΦ]
    rw [hκ (a : A.K) (Units.isUnit a) g]
    ring
  have hc : ∀ g, Φ g ≠ 0 → ∫ s, α (g * tm A hG a⁻¹ * tm A hG s) ∂(unitsMeas A μK) = 1 := by
    intro g hg
    refine hcut g ⟨(act g Y).2.1, (act g Y).2.2.1, ?_⟩ a⁻¹
    intro h0
    apply hg
    have h1 : f' (act g Y) = 0 := h0
    simp only [hΦ, h1, zero_mul]
  rw [hO, ← integral_const_mul]
  simp_rw [hinner]
  exact ((GlobalTheory.T.fubini_cutoff_integral_generalLinear_torus) F E A r τ p hG M μK hμK α Φ hΦt hαlc hαcs hα0 (tm A hG a⁻¹) hc).symm

end GlobalTheory.JR.LinDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PsiLocConductorEventually
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host GlobalTheory.Published GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.Petersson
open scoped nonZeroDivisors ComplexConjugate

open IsDedekindDomain Formalism.UG GlobalTheory.LFun

theorem GlobalTheory.JSW.psiLoc_conductor_eventually : ∀ (E : Type) [Field E] [NumberField E], ∃ S : Finset (HeightOneSpectrum (𝓞 E)), ∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, GlobalTheory.JSW.psiLoc w (x * y) = 1) ↔ x ∈ Ov E w := by
  intro E _ _
  classical
  have hD : (differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) ≠ 0 := differentIdeal_ne_bot (A := ℤ)
  obtain hfin := Ideal.finite_factors hD
  refine ⟨hfin.toFinset, fun w hw x => ?_⟩
  have hw' : ¬ w.asIdeal ∣ differentIdeal ℤ (𝓞 E) := by simpa using hw
  rw [Ideal.dvd_iff_le] at hw'
  obtain ⟨y, hy, hyw⟩ := SetLike.not_le_iff_exists.mp hw'
  have hval : Valued.v ((algebraMap (𝓞 E) E y : E) : w.adicCompletion E) = 1 := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
    exact le_antisymm (w.intValuation_le_one y) (not_lt.mp fun h => hyw ((w.intValuation_lt_one_iff_mem y).mp h))
  have key : x ∈ GroundTheory.Global.localInvDifferent w ↔ x ∈ w.adicCompletionIntegers E := by
    refine ⟨fun h => ?_, GroundTheory.Global.mem_localInvDifferent_of_mem⟩
    have h1 := h y hy
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.map_mul, hval, mul_one] at h1
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr h1
  show _ ↔ x ∈ w.adicCompletionIntegers E
  rw [← key, ← GroundTheory.Global.forall_localAdelicChar_mul_eq_one_iff]
  refine forall₂_congr fun a _ => ?_
  rw [GlobalTheory.JSW.WhitModel.psiLoc_eq, Circle.coe_eq_one, mul_comm]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftVectorIsThetaFunctionTwoStepModel
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.TwoStepModel

open GlobalTheory.ExportSeries

theorem datum_eq_tensorHalf {D : D7} {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    {Pg Q : Finset (Pl D.host.E)} {eg eQ : AE D} (hg : IsIdemSum eg Pg) (hq : IsIdemSum eQ Q) (hd : Disjoint Pg Q)
    (he : IsIdemSum (eg + eQ) (Pg ∪ Q)) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) :
    (fun x => if IsHalf (cA D (eg + eQ)) x ∧ IsIntM (frMapAdj S T βS βT x) then
        omegaK Pg (fun PP => redM PP (frMapAdj S T βS βT x)) *
          omegaQ Q T.rank ξ (-1) (fun PP => redM PP (frMapAdj S T βS βT x)) else 0) =
      tensorHalf (cA D eQ) (cA D eg)
        (fun x => if IsHalf (cA D eg) x ∧ IsIntM (frMapAdj S T βS βT x) then
          omegaK Pg (fun PP => redM PP (frMapAdj S T βS βT x)) else 0)
        (fun x => if IsHalf (cA D eQ) x ∧ IsIntM (frMapAdj S T βS βT x) then
          omegaQ Q T.rank ξ (-1) (fun PP => redM PP (frMapAdj S T βS βT x)) else 0) := by
  have hA := GlobalTheory.T.adjointFrame_integral_iff_parts_conj_half D S T βS βT Pg Q eg eQ hg hq hd he
  have hB := GlobalTheory.T.reduction_adjointFrame_conj_half_two_parts D S T βS βT Pg Q eg eQ hg hq hd he
  have heg := GlobalTheory.PlaceVec.idemSum_mul_self hg
  have heQ := GlobalTheory.PlaceVec.idemSum_mul_self hq
  have hcg : ∀ x : WO S T, IsHalf (cA D eg) (cA D eg • x) :=
    fun x => GlobalTheory.ExportSeries.RestrictHalfModel.isHalf_smul (by rw [← map_mul, heg]) x
  have hcQ : ∀ x : WO S T, IsHalf (cA D eQ) (cA D eQ • x) :=
    fun x => GlobalTheory.ExportSeries.RestrictHalfModel.isHalf_smul (by rw [← map_mul, heQ]) x
  funext x
  rw [tensorHalf_apply]
  have hc : cA D (eg + eQ) = cA D eQ + cA D eg := by rw [map_add, add_comm]
  by_cases hx : IsHalf (cA D (eg + eQ)) x
  · have hx' : IsHalf (cA D eQ + cA D eg) x := hc ▸ hx
    rw [if_pos hx', mul_one]
    by_cases hi : IsIntM (frMapAdj S T βS βT x)
    · obtain ⟨i1, i2⟩ := (hA x hx).1 hi
      obtain ⟨r1, r2⟩ := hB x hx hi
      have c1 : IsHalf (cA D (eg + eQ)) x ∧ IsIntM (frMapAdj S T βS βT x) := ⟨hx, hi⟩
      have c2 : IsHalf (cA D eQ) (cA D eQ • x) ∧ IsIntM (frMapAdj S T βS βT (cA D eQ • x)) := ⟨hcQ x, i2⟩
      have c3 : IsHalf (cA D eg) (cA D eg • x) ∧ IsIntM (frMapAdj S T βS βT (cA D eg • x)) := ⟨hcg x, i1⟩
      rw [if_pos c1, if_pos c2, if_pos c3, mul_comm]
      congr 1
      · exact GlobalTheory.PlaceVec.omegaQ_congr Q _ ξ _ fun PP hPP => (r2 PP hPP).symm
      · exact GlobalTheory.PlaceVec.omegaK_congr Pg fun PP hPP => (r1 PP hPP).symm
    · have c1 : ¬ (IsHalf (cA D (eg + eQ)) x ∧ IsIntM (frMapAdj S T βS βT x)) := fun h => hi h.2
      rw [if_neg c1]
      have := mt (hA x hx).2 hi
      rcases not_and_or.1 this with h | h
      · have c3 : ¬ (IsHalf (cA D eg) (cA D eg • x) ∧ IsIntM (frMapAdj S T βS βT (cA D eg • x))) := fun h' => h h'.2
        rw [if_neg c3, mul_zero]
      · have c2 : ¬ (IsHalf (cA D eQ) (cA D eQ • x) ∧ IsIntM (frMapAdj S T βS βT (cA D eQ • x))) := fun h' => h h'.2
        rw [if_neg c2, zero_mul]
  · have c1 : ¬ (IsHalf (cA D (eg + eQ)) x ∧ IsIntM (frMapAdj S T βS βT x)) := fun h => hx h.1
    have hx' : ¬ IsHalf (cA D eQ + cA D eg) x := hc ▸ hx
    rw [if_neg c1, if_neg hx', mul_zero]

end GlobalTheory.TwoStepModel

namespace GlobalTheory.ConjTwist

theorem isThetaAt_vP_twoStep : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0) (eg eQ : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg → IsIdemSum eQ (R.Q t) → IsThetaAt R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) (cA D eg) (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 (R.vacP i) (fun x => if IsHalf (cA D eg) x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then omegaK R.Pg (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0) fg → IsThetaAt R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) (cA D eQ) (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 fg (fun x => if IsHalf (cA D eQ) x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then omegaQ (R.Q t) (Wc D i).rank (R.xiR t) (-1) (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0) (R.vP i t) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC _hG i t eg eQ fg hg hq hfg
  obtain ⟨⟨hψ, -⟩, e, he, hTe⟩ := hC.thP.vP i t
  have hSV := GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hC.lev.βV i))
  have hSW := GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hC.lev.βW i))
  have hd := GlobalTheory.TwistPlaces.typePlaces_disjoint_twistPlaces R F hC t
  have hsum : e = eg + eQ := by
    rw [← GlobalTheory.ExportSeries.idem_eq he, ← GlobalTheory.ExportSeries.idem_eq hg, ← GlobalTheory.ExportSeries.idem_eq hq]
    exact Finset.sum_union hd
  subst hsum
  have heg := GlobalTheory.PlaceVec.idemSum_mul_self hg
  have heQ := GlobalTheory.PlaceVec.idemSum_mul_self hq
  have hee := GlobalTheory.PlaceVec.idemSum_mul_self he
  have hgQ : eg * eQ = 0 := by
    refine GlobalTheory.PlaceVec.natCast_mul_eq_zero 2 _ two_pos ?_
    push_cast
    linear_combination hee - heg - heQ
  have hcg : cA D eg * cA D eg = cA D eg := by rw [← map_mul, heg]
  have hcQ : cA D eQ * cA D eQ = cA D eQ := by rw [← map_mul, heQ]
  have hQg : cA D eQ * cA D eg = 0 := by rw [← map_mul, mul_comm, hgQ, map_zero]
  have hgQ' : cA D eg * cA D eQ = 0 := by rw [mul_comm, hQg]
  have hΛ : ∀ a : AE D, a * a = a → ∀ u ∈ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True),
      a • u ∈ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) :=
    fun a ha u hu => GlobalTheory.PlaceModelSum.idem_smul_latO ha hu
  have hinfg : infPart D (cA D eg) = 0 := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart hg)
  have hinfQ : infPart D (cA D eQ) = 0 := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart hq)
  have hSBg := GlobalTheory.PlaceVec.isSBHalf_of_red hSV.1 hSW.1 hinfg (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i))
    (GlobalTheory.PlaceVec.frMapAdj_add _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_up _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_down _ _ _ _)
    R.Pg (fun y => omegaK R.Pg y) fun y y' h => GlobalTheory.PlaceVec.omegaK_congr R.Pg h
  have hSBQ := GlobalTheory.PlaceVec.isSBHalf_of_red hSV.1 hSW.1 hinfQ (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i))
    (GlobalTheory.PlaceVec.frMapAdj_add _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_up _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_down _ _ _ _)
    (R.Q t) (fun y => omegaQ (R.Q t) (Wc D i).rank (R.xiR t) (-1) y) fun y y' h => GlobalTheory.PlaceVec.omegaQ_congr _ _ _ _ h
  obtain ⟨⟨Te, hTe1⟩, hTe2⟩ := hTe
  have hc : cA D (eg + eQ) = cA D eQ + cA D eg := by rw [map_add, add_comm]
  have hc' : cA D (eg + eQ) = cA D eg + cA D eQ := map_add _ _ _
  have hm1 := GlobalTheory.TwoStepModel.isPlaceModel_comp_tensorHalf hcQ hcg hQg hΛ hSBg (hc ▸ hTe1)
  have hm2 := GlobalTheory.ExportSeries.isPlaceModel_comp_restrictHalf hcg hcQ hgQ' hΛ (hc' ▸ hTe1)
  have hbase := hfg.2 _ hm2
  simp only [LinearMap.comp_apply] at hbase
  rw [← hbase] at hm1
  refine ⟨⟨_, hm1⟩, fun T' hT' => ?_⟩
  rw [hTe2 Te hTe1, GlobalTheory.TwoStepModel.datum_eq_tensorHalf (R.βV i) (R.βW i) hg hq hd he (R.xiR t)]
  exact GlobalTheory.PlaceVec.placeModel_unique hψ hSV hSW hcQ hinfQ hm1 hT' hSBQ

end GlobalTheory.ConjTwist

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightVectorRealizationExistsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.GeoTie
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_vector_realization_exists : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T1 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m) (T0 : CoreJ D) [Algebra T0.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T0.Q.c.F) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (fw : FWTie T0 Rl.toRealDat κ v₀) (i : D.ntw.Tw) (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]), (∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range) → ∀ (b : Bool) (j : Fin D.R.m), (∀ f : NX.FmK S ((j : ℕ) + 1), (show ↥(S.A ((j : ℕ) + 1)).WK from f).1 ∈ (S.A ((j : ℕ) + 1)).MK → f ∈ locBall YS fw iC b j) → (∀ f : NX.FmK S ((j : ℕ) + 1), ∃ c : S.Ks, c ≠ 0 ∧ c • f ∈ locBall YS fw iC b j) := by
  first | exact @GlobalTheory.GeoTie.exists_smul_mem_locBall | exact GlobalTheory.GeoTie.exists_smul_mem_locBall | (intros; apply GlobalTheory.GeoTie.exists_smul_mem_locBall <;> assumption)
end

