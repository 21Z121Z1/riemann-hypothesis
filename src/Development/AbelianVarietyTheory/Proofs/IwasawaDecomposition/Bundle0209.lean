import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0188
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0205
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalRingCardinality.Bundle0007
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0203
import Formalism.LocalRingCardinality.DataTheta
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0173
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0202
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RedivisionStructureEq
import Formalism.LocalToGlobal.GroupLattices.Joint0
import Formalism.LocalToGlobal.NumberFieldFamilies.OwnStruct
import Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibreMeasuresTransportUnitarySimilitude
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx

theorem isFibreFamily_transport {V R : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [MeasurableSpace R] [BorelSpace R]
    (μ : Measure V) (ν : Measure R) (q q₂ : V → R) (e : V ≃ₜ V) (u : Rˣ) (a d : ℝ≥0) (hd : d ≠ 0)
    (hμ : μ = a • μ.map e) (hν : ν = d • ν.map (fun z => (u : R) * z))
    (hq : ∀ v, q₂ (e v) = u * q v) (fib : R → Measure V)
    (h : IsFibreFamily μ q id Set.univ ν {c | IsUnit c} fib) :
    IsFibreFamily μ q₂ id Set.univ ν {c | IsUnit c}
      (fun b => (a * d⁻¹) • (fib ((u⁻¹ : Rˣ) * b)).map e) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hme : MeasurableEmbedding e := e.measurableEmbedding
  have hmu : MeasurableEmbedding (fun z : R => (u : R) * z) :=
    (Homeomorph.smul u : R ≃ₜ R).measurableEmbedding
  refine ⟨fun b => ?_, fun φ hφ => ?_, fun φ hφ hc _ => ?_⟩
  · rw [Measure.smul_apply, hme.map_apply]
    have : e ⁻¹' (q₂ ⁻¹' {id b} ∩ Set.univ)ᶜ = (q ⁻¹' {id ((u⁻¹ : Rˣ) * b)} ∩ Set.univ)ᶜ := by
      ext v
      simp [hq, Units.eq_inv_mul_iff_mul_eq]
    rw [this, h1, smul_zero]
  · have h2' := h2 (φ ∘ e) (hφ.comp e.measurable)
    simp only [Measure.restrict_univ, Function.comp] at h2' ⊢
    have hL : ∫⁻ v, φ v ∂μ = (a : ℝ≥0∞) * ∫⁻ v, φ (e v) ∂μ := by
      conv_lhs => rw [hμ]
      rw [lintegral_smul_measure, hme.lintegral_map, ENNReal.smul_def, smul_eq_mul]
    rw [hL, h2']
    conv_rhs => rw [hν]
    rw [lintegral_smul_measure, hmu.lintegral_map]
    simp only [lintegral_smul_measure, hme.lintegral_map, Units.inv_mul_cancel_left,
      ENNReal.smul_def, smul_eq_mul]
    rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, ← mul_assoc, ← ENNReal.coe_mul]
    congr 2
    field_simp
  · obtain ⟨h4, h5⟩ := h3 (φ ∘ e) (hφ.comp e.continuous) (hc.comp_homeomorph e) (Set.subset_univ _)
    have hmem : ∀ b ∈ {c : R | IsUnit c}, ((u⁻¹ : Rˣ) : R) * b ∈ {c : R | IsUnit c} :=
      fun b hb => (Units.isUnit _).mul hb
    refine ⟨fun b hb => ?_, ?_⟩
    · exact (hme.integrable_map_iff.2 (h4 _ (hmem b hb))).smul_measure_nnreal
    · simp only [integral_smul_nnreal_measure, hme.integral_map]
      exact (h5.comp (continuous_const.mul continuous_id).continuousOn hmem).const_smul _

theorem lrAct_one_right {S : Type} [CommRing S] {n M : ℕ} (g : Matrix (Fin M) (Fin M) S)
    (X : Fin n → Fin M → S) : lrAct g 1 X = fun a => g.mulVec (X a) := by
  funext a
  simp [lrAct, Matrix.one_apply]

theorem exists_homeomorph_lrAct {S : Type} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
    {n M : ℕ} (g : Matrix (Fin M) (Fin M) S) (hg : IsUnit g.det) :
    ∃ e : (Fin n → Fin M → S) ≃ₜ (Fin n → Fin M → S), ⇑e = lrAct g 1 := by
  refine ⟨{ toFun := fun X a => g.mulVec (X a)
            invFun := fun X a => g⁻¹.mulVec (X a)
            left_inv := fun X => ?_
            right_inv := fun X => ?_
            continuous_toFun := continuous_pi fun a =>
              continuous_const.matrix_mulVec (continuous_apply a)
            continuous_invFun := continuous_pi fun a =>
              continuous_const.matrix_mulVec (continuous_apply a) }, ?_⟩
  · funext a
    simp [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul g hg]
  · funext a
    simp [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv g hg]
  · funext X
    rw [lrAct_one_right]
    rfl

theorem fibAt_similitude : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], Nice R → ∀ (M : ℕ) (J J₂ : Matrix (Fin M) (Fin M) E) (lam : Measure (R ⊗[F] E)) (ν : Measure R) (β c : R) (m : Measure (Fin 1 → Fin M → R ⊗[F] E)) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)), lam.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsUnit g.det → IsUnit c → (∀ z, qR R σ J₂ (g.mulVec z) = c * qR R σ J z) → FibAt R σ J (tupMeas lam 1 M) ν β m → FibAt R σ J₂ (tupMeas lam 1 M) ν (c * β) ((modu (R ⊗[F] E) g.det * (modu R c)⁻¹) • m.map (lrAct g 1)) := by
  intro F E _ _ _ _ _ σ R _ _ _ _ _ _ _ _ _ hR M J J₂ lam ν β c m g hlam hν hg hc hq hfib
  obtain ⟨fib, hfib, rfl⟩ := hfib
  obtain ⟨hA, hred, -⟩ := GlobalTheory.T.tensor_niceRing_artinian_reduced_openUnits F E R hR
  have hμ := GlobalTheory.T.vectorTupleProductMeasure_two_sided_action (R ⊗[F] E) hA hred lam hlam 1 M g 1 hg (by simp)
  rw [Matrix.det_one, (modu_basic (R ⊗[F] E)).2.2.1, one_pow, mul_one, pow_one] at hμ
  obtain ⟨e, he⟩ := exists_homeomorph_lrAct (n := 1) g hg
  obtain ⟨hpos, hν'⟩ := (modu_basic R).1 c hc
  obtain ⟨u, rfl⟩ := hc
  rw [← he] at hμ ⊢
  refine ⟨_, isFibreFamily_transport _ ν _ _ e u _ _ hpos.ne' hμ (hν' ν hν) (fun X => ?_) fib hfib, ?_⟩
  · rw [he, lrAct_one_right]
    exact hq _
  · simp only [Units.inv_mul_cancel_left]

end GlobalTheory.GaugeEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameFunctionActionHolomorphicExtremalLowest
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.JointHarm

theorem vhol_diff_prod {E κ : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {s : Set E} (u : Finset κ)
    (f : κ → E → ℂ) (h : ∀ i, DifferentiableOn ℂ (f i) s) :
    DifferentiableOn ℂ (fun z => ∏ i ∈ u, f i z) s := by
  induction u using Finset.induction_on with
  | empty => simpa using differentiableOn_const _
  | insert a u ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a).mul ih

theorem vhol_diff_det {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {n : ℕ} {s : Set E}
    (A : E → Matrix (Fin n) (Fin n) ℂ) (h : ∀ i j, DifferentiableOn ℂ (fun z => A z i j) s) :
    DifferentiableOn ℂ (fun z => (A z).det) s := by
  simp only [Matrix.det_apply']
  refine DifferentiableOn.fun_sum fun σ _ => DifferentiableOn.const_mul ?_ _
  exact vhol_diff_prod _ (fun i z => A z (σ i) i) fun i => h _ _

theorem vhol_diff_inv {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {n : ℕ} {s : Set E}
    (A : E → Matrix (Fin n) (Fin n) ℂ) (h : ∀ i j, DifferentiableOn ℂ (fun z => A z i j) s)
    (h0 : ∀ z ∈ s, (A z).det ≠ 0) (i j : Fin n) :
    DifferentiableOn ℂ (fun z => (A z)⁻¹ i j) s := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, Matrix.adjugate_apply]
  refine ((vhol_diff_det A h).inv h0).mul (vhol_diff_det _ fun a b => ?_)
  by_cases ha : a = j
  · simp only [Matrix.updateRow_apply, if_pos ha]
    exact differentiableOn_const _
  · simp only [Matrix.updateRow_apply, if_neg ha]
    exact h a b

variable {ι : Type} [Fintype ι] {n : ℕ}

theorem vhol_diff_fock {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {s : Set E}
    (U : E → ι → Matrix (Fin n) (Fin n) ℂ) (h : ∀ τ i j, DifferentiableOn ℂ (fun z => U z τ i j) s)
    (x y : Pol ℂ ι n) :
    DifferentiableOn ℂ (fun z => fockL x (Formalism.GradedWeylDivisibility.blockAct ℂ (U z) y)) s := by
  induction y using MvPolynomial.induction_on generalizing x with
  | C a =>
    simp only [MvPolynomial.algHom_C]
    exact differentiableOn_const _
  | add p q hp hq =>
    simp only [map_add]
    exact (hp x).add (hq x)
  | mul_X p v hp =>
    have e1 : ∀ z, Formalism.GradedWeylDivisibility.blockAct ℂ (U z) (p * MvPolynomial.X v) =
        ∑ b : Fin n, U z v.1 v.2.1 b • (MvPolynomial.X (v.1, (b, v.2.2)) * Formalism.GradedWeylDivisibility.blockAct ℂ (U z) p) := by
      intro z
      rw [map_mul, blockAct_X, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [MvPolynomial.smul_eq_C_mul]; ring
    simp only [e1, map_sum, map_smul, ← fockL_pderiv_X, smul_eq_mul]
    exact DifferentiableOn.fun_sum fun b _ => (h _ _ _).mul (hp _)

theorem vhol_aniso {σ : Type} (x : MvPolynomial σ ℂ) (hx : fockL x x = 0) : x = 0 := by
  rw [fockL_apply, fockS] at hx
  have e : ∀ m, star (x.coeff m) * x.coeff m * (mfact m : ℂ) =
      ((Complex.normSq (x.coeff m) * (mfact m : ℝ) : ℝ) : ℂ) := by
    intro m
    rw [Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]
    simp
  simp only [e] at hx
  rw [← Complex.ofReal_sum, Complex.ofReal_eq_zero,
    Finset.sum_eq_zero_iff_of_nonneg fun m _ => mul_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _)] at hx
  ext m
  by_contra hm
  have h1 := hx m (MvPolynomial.mem_support_iff.2 hm)
  have h2 : 0 < mfact m := Finset.prod_pos fun k _ => Nat.factorial_pos _
  rcases mul_eq_zero.1 h1 with h | h
  · exact hm (Complex.normSq_eq_zero.1 h)
  · exact h2.ne' (by exact_mod_cast h)

theorem vhol_one (lam : ι → DomWeight n) : vact lam 1 = 1 := by
  unfold vact
  simp only [Pi.one_apply, Matrix.det_one, _root_.one_zpow, Finset.prod_const_one, one_smul, inv_one, blockAct_one]
  rfl

theorem vhol_mul (lam : ι → DomWeight n) (a b : ι → Matrix (Fin n) (Fin n) ℂ) :
    vact lam (a * b) = vact lam a * vact lam b := by
  apply LinearMap.ext
  intro F
  have := congrArg (fun φ => φ F) (blockAct_comp (fun τ => (a τ)⁻¹) (fun τ => (b τ)⁻¹))
  simp only [AlgHom.comp_apply] at this
  simp only [vact, Pi.mul_apply, Matrix.det_mul, mul_zpow, Finset.prod_mul_distrib, Matrix.mul_inv_rev,
    Module.End.mul_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_smul, smul_smul, this]
  rw [mul_comm]

theorem vhol_adj (lam : ι → DomWeight n) (a : ι → Matrix (Fin n) (Fin n) ℂ) (x y : Pol ℂ ι n) :
    fockL (vact lam a x) y = fockL x (vact lam (fun τ => (a τ)ᴴ) y) := by
  simp only [vact, LinearMap.smul_apply, AlgHom.toLinearMap_apply, LinearMap.map_smulₛₗ, map_smul,
    fockL_blockAct_adj, Matrix.conjTranspose_nonsing_inv, Matrix.det_conjTranspose, starRingEnd_apply, star_prod,
    star_zpow₀, RingHom.id_apply]

theorem vhol_units (lam : ι → DomWeight n) (G : ι → GL (Fin n) ℂ) :
    vact lam (fun τ => (G τ : Matrix (Fin n) (Fin n) ℂ)) = actP lam (invTrK G) := by
  unfold vact actP trAct
  rw [detTw_eq]
  simp only [invTrK_coe, Matrix.transpose_transpose, Matrix.det_transpose, Matrix.coe_units_inv,
    Matrix.det_nonsing_inv, Ring.inverse_eq_inv', _root_.zpow_neg, _root_.inv_zpow]

theorem vhol_ext (lam : ι → DomWeight n) (τ : ι) (g : GL (Fin n) ℂ) (c : ℂ)
    (h : sqAct ℂ n (lam τ) (inside₂ ℂ n g) (extremal ℂ n (lam τ)) = c • extremal ℂ n (lam τ)) :
    vact lam (Pi.mulSingle τ (g : Matrix (Fin n) (Fin n) ℂ)) (ten fun τ => extremal ℂ n (lam τ)) =
      c • ten fun τ => extremal ℂ n (lam τ) := by
  have e : (Pi.mulSingle τ (g : Matrix (Fin n) (Fin n) ℂ) : ι → Matrix (Fin n) (Fin n) ℂ) =
      fun σ => ((Pi.mulSingle τ g : ι → GL (Fin n) ℂ) σ : Matrix (Fin n) (Fin n) ℂ) := by
    funext σ
    by_cases hσ : σ = τ
    · subst hσ; simp
    · simp [hσ]
  rw [e, vhol_units, actTen]
  unfold ten
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ),
    ← Finset.mul_prod_erase _ (fun σ => Formalism.GradedWeylDivisibility.blockEmb ℂ σ (extremal ℂ n (lam σ))) (Finset.mem_univ τ),
    ← smul_mul_assoc]
  congr 1
  · rw [← map_smul, ← h]
    show Formalism.GradedWeylDivisibility.blockEmb ℂ τ (sqAct ℂ n (lam τ) (inside₂ ℂ n ((Pi.mulSingle τ g : ι → GL (Fin n) ℂ) τ)) _) = _
    rw [Pi.mulSingle_eq_same]
  · refine Finset.prod_congr rfl fun σ hσ => ?_
    refine congrArg (Formalism.GradedWeylDivisibility.blockEmb ℂ σ) ?_
    refine (factSqHighestWeight ℂ n (lam σ)).2 _ ?_ ?_
    · rw [invTrK_coe, Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase hσ)]
      simpa using Matrix.blockTriangular_one
    · intro a
      rw [invTrK_coe, Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase hσ)]
      simp

theorem vhol_lo_inv (g : Matrix (Fin n) (Fin n) ℂ) (hg : IsUnit g) (h : IsLoUni g) :
    (g⁻¹)ᵀ.BlockTriangular id ∧ ∀ a, g⁻¹ a a = 1 := by
  have h1 : gᵀ.BlockTriangular id := fun i j hij => (h j i).1 hij
  have hu : IsUnit gᵀ := (Matrix.isUnit_transpose g).2 hg
  obtain ⟨inst⟩ := hu.nonempty_invertible
  have h2 : (gᵀ)⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular h1
  rw [← Matrix.transpose_nonsing_inv] at h2
  refine ⟨h2, fun a => ?_⟩
  have h3 := congrFun (congrFun (Matrix.mul_nonsing_inv g ((Matrix.isUnit_iff_isUnit_det g).1 hg)) a) a
  rw [Matrix.mul_apply, Finset.sum_eq_single a, (h a a).2 rfl, one_mul, Matrix.one_apply_eq] at h3
  · exact h3
  · intro b _ hb
    rcases lt_or_gt_of_ne hb with hlt | hlt
    · have : g⁻¹ b a = 0 := h2 (i := a) (j := b) hlt
      rw [this, mul_zero]
    · rw [(h a b).1 hlt, zero_mul]
  · simp

theorem vact_isHolFam_isBotFam : ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n),
    IsHolFam (fun _ => allPos n) fockL (vact lam) ∧
    IsBotFam (fun _ => allPos n) (vact lam) (fun τ j => -((lam τ).w j : ℝ)) (ten fun τ => extremal ℂ n (lam τ)) ∧
    (ten fun τ => extremal ℂ n (lam τ)) ≠ 0 ∧ (ten fun τ => extremal ℂ n (lam τ)) ∈ VV ℂ lam := by
  intro ι _ n lam
  refine ⟨⟨vhol_aniso, vhol_one lam, fun a b _ _ => vhol_mul lam a b, fun τ =>
    ⟨vhol_aniso, ?_, fun a _ b _ => ?_, fun g _ x y => ?_, fun x y => ?_⟩⟩, fun τ => ⟨fun g hg hl => ?_, fun θ => ?_⟩,
    ?_, ?_⟩
  · show vact lam (Pi.mulSingle τ 1) = 1
    rw [Pi.mulSingle_one, vhol_one]
  · show vact lam (Pi.mulSingle τ (a * b)) = _
    rw [Pi.mulSingle_mul, vhol_mul]
  · show fockL (vact lam (Pi.mulSingle τ g) x) y = fockL x (vact lam (Pi.mulSingle τ gᴴ) y)
    rw [vhol_adj]
    refine congrArg (fun u => fockL x (vact lam u y)) ?_
    funext σ
    by_cases hσ : σ = τ
    · subst hσ; simp
    · simp [hσ]
  · have h1 : ∀ σ i j, DifferentiableOn ℂ (fun g : Fin n → Fin n → ℂ =>
        (Pi.mulSingle τ (Matrix.of g) : ι → Matrix (Fin n) (Fin n) ℂ) σ i j)
        {g | Matrix.of g ∈ GlobalTheory.Dec.KC (allPos n)} := by
      intro σ i j
      by_cases hσ : σ = τ
      · subst hσ
        simp only [Pi.mulSingle_eq_same, Matrix.of_apply]
        fun_prop
      · simp only [Pi.mulSingle_eq_of_ne hσ]
        exact differentiableOn_const _
    have h0 : ∀ σ, ∀ g ∈ {g : Fin n → Fin n → ℂ | Matrix.of g ∈ GlobalTheory.Dec.KC (allPos n)},
        ((Pi.mulSingle τ (Matrix.of g) : ι → Matrix (Fin n) (Fin n) ℂ) σ).det ≠ 0 := by
      intro σ g hg
      by_cases hσ : σ = τ
      · subst hσ
        rw [Pi.mulSingle_eq_same]
        exact ((Matrix.isUnit_iff_isUnit_det _).1 hg.1).ne_zero
      · rw [Pi.mulSingle_eq_of_ne hσ]
        simp
    simp only [vact, LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_smul, smul_eq_mul]
    refine DifferentiableOn.mul (vhol_diff_prod _ (fun σ (g : Fin n → Fin n → ℂ) =>
      ((Pi.mulSingle τ (Matrix.of g) : ι → Matrix (Fin n) (Fin n) ℂ) σ).det ^ (-(lam σ).detShift)) fun σ => ?_)
      (vhol_diff_fock _ (fun σ => vhol_diff_inv _ (h1 σ) (h0 σ)) x y)
    exact (vhol_diff_det _ (h1 σ)).zpow (Or.inl (h0 σ))
  · obtain ⟨h2, h3⟩ := vhol_lo_inv g hg.1 hl
    obtain ⟨G, rfl⟩ := hg.1
    have := vhol_ext lam τ G 1 (by
      rw [one_smul]
      refine (factSqHighestWeight ℂ n (lam τ)).2 _ ?_ ?_
      · simpa [inside₂] using h2
      · simpa [inside₂] using h3)
    rwa [one_smul] at this
  · let t : Fin n → ℂˣ := fun a => Units.mk0 (Complex.exp ((θ a : ℂ) * Complex.I)) (Complex.exp_ne_zero _)
    have e1 : ((diagGL ℂ n t : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) =
        Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I) := rfl
    have e2 : inside₂ ℂ n (diagGL ℂ n t) = diagGL ℂ n t⁻¹ := by
      apply Units.ext
      exact Matrix.diagonal_transpose _
    show vact lam (Pi.mulSingle τ _) _ = _
    rw [← e1]
    apply vhol_ext
    rw [e2, (factSqHighestWeight ℂ n (lam τ)).1]
    congr 1
    rw [Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum, Units.coe_prod]
    refine Finset.prod_congr rfl fun a _ => ?_
    simp only [t, Pi.inv_apply, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, Units.val_mk0,
      ← Complex.exp_neg, ← Complex.exp_int_mul]
    congr 1
    push_cast
    ring
  · refine Finset.prod_ne_zero_iff.2 fun τ _ h => Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl (lam τ).natW ?_
    exact MvPolynomial.rename_injective (fun v : Fin n × Fin n => (τ, v)) (fun _ _ h => congrArg Prod.snd h)
      (h.trans (map_zero _).symm)
  · exact Submodule.subset_span ⟨fun τ => extremal ℂ n (lam τ),
      fun τ => Formalism.GradedWeylDivisibility.hwMem ℂ n n le_rfl _ (natW_antitone (lam τ)), rfl⟩

end GlobalTheory.JointHarm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDerivAtInnerPolynomialMovingGaussian
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder

namespace GlobalTheory.OscPairDer

open MvPolynomial

variable {P Q : ℕ}

def derForm (A' : Matrix (Fin P) (Fin Q) ℂ) (x' : Ix P Q → ℂ) (T : MvPolynomial (Ix P Q) ℂ → ℂ)
    (f : MvPolynomial (Ix P Q) ℂ) : ℂ :=
  ∑ i, ∑ j, A' i j * T (pderiv (Sum.inl i) (pderiv (Sum.inr j) f)) + ∑ l, x' l * T (pderiv l f)

theorem derForm_comb {κ : Type} [Fintype κ] (A' : Matrix (Fin P) (Fin Q) ℂ) (x' : Ix P Q → ℂ)
    (T U : MvPolynomial (Ix P Q) ℂ → ℂ) (a : ℂ) (b : κ → ℂ) (e : κ → Ix P Q)
    (hU : ∀ g, U g = a * T g + ∑ k, b k * T (pderiv (e k) g)) (f : MvPolynomial (Ix P Q) ℂ) :
    derForm A' x' U f = a * derForm A' x' T f + ∑ k, b k * derForm A' x' T (pderiv (e k) f) := by
  simp only [derForm, hU, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  have h1 : ∑ i, ∑ j, ∑ k, A' i j * (b k * T (pderiv (e k) (pderiv (Sum.inl i) (pderiv (Sum.inr j) f)))) =
      ∑ k, ∑ i, ∑ j, b k * (A' i j * T (pderiv (Sum.inl i) (pderiv (Sum.inr j) (pderiv (e k) f)))) := by
    rw [Finset.sum_comm (s := (Finset.univ : Finset κ))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    rw [GlobalTheory.Oscillator.pderiv_pderiv_comm (e k), GlobalTheory.Oscillator.pderiv_pderiv_comm (e k), mul_left_comm]
  have h2 : ∑ l, ∑ k, x' l * (b k * T (pderiv (e k) (pderiv l f))) =
      ∑ k, ∑ l, b k * (x' l * T (pderiv l (pderiv (e k) f))) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    rw [GlobalTheory.Oscillator.pderiv_pderiv_comm (e k), mul_left_comm]
  rw [h1, h2]
  simp only [mul_left_comm a]
  ring

theorem pderiv_X_mul (m l : Ix P Q) (f : MvPolynomial (Ix P Q) ℂ) :
    pderiv m (X l * f) = X l * pderiv m f + if m = l then f else 0 := by
  rw [Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul, Pi.single_apply]
  by_cases h : m = l
  · simp [h]
  · simp [h, Ne.symm h]

theorem derForm_X_inl (A' : Matrix (Fin P) (Fin Q) ℂ) (x' : Ix P Q → ℂ)
    (T : MvPolynomial (Ix P Q) ℂ →+ ℂ) (i : Fin P) (f : MvPolynomial (Ix P Q) ℂ) :
    derForm A' x' T (X (Sum.inl i) * f) = derForm A' x' (fun g => T (X (Sum.inl i) * g)) f +
      (x' (Sum.inl i) * T f + ∑ j, A' i j * T (pderiv (Sum.inr j) f)) := by
  simp only [derForm, pderiv_X_mul, map_add, apply_ite T, map_zero, mul_add, Finset.sum_add_distrib, mul_ite,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, reduceCtorEq, if_false, add_zero, Sum.inl.injEq]
  rw [Finset.sum_comm (f := fun i' j => if i' = i then A' i' j * T (pderiv (Sum.inr j) f) else 0)]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

theorem derForm_X_inr (A' : Matrix (Fin P) (Fin Q) ℂ) (x' : Ix P Q → ℂ)
    (T : MvPolynomial (Ix P Q) ℂ →+ ℂ) (j : Fin Q) (f : MvPolynomial (Ix P Q) ℂ) :
    derForm A' x' T (X (Sum.inr j) * f) = derForm A' x' (fun g => T (X (Sum.inr j) * g)) f +
      (x' (Sum.inr j) * T f + ∑ i, A' i j * T (pderiv (Sum.inl i) f)) := by
  simp only [derForm, pderiv_X_mul, map_add, apply_ite T, apply_ite (pderiv _), map_zero, mul_add,
    Finset.sum_add_distrib, mul_ite,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, reduceCtorEq, if_false, add_zero, Sum.inr.injEq]
  ring

def pair (F : Fock (Ix P Q)) (v : F.H) : MvPolynomial (Ix P Q) ℂ →+ ℂ where
  toFun f := inner ℂ (F.ι f) v
  map_zero' := by simp
  map_add' f g := by simp [inner_add_left]

theorem step {κ : Type} [Fintype κ] (A' : Matrix (Fin P) (Fin Q) ℂ) (x' : Ix P Q → ℂ)
    (T : ℝ → MvPolynomial (Ix P Q) ℂ → ℂ) (l : Ix P Q) (a : ℝ → ℂ) (b : ℝ → κ → ℂ) (a' : ℂ) (b' : κ → ℂ)
    (e : κ → Ix P Q) (ha : HasDerivAt a a' 0) (hb : ∀ k, HasDerivAt (fun t => b t k) (b' k) 0)
    (hU : ∀ t g, T t (X l * g) = a t * T t g + ∑ k, b t k * T t (pderiv (e k) g)) (f : MvPolynomial (Ix P Q) ℂ)
    (h0 : HasDerivAt (fun t => T t f) (derForm A' x' (T 0) f) 0)
    (h1 : ∀ m, HasDerivAt (fun t => T t (pderiv m f)) (derForm A' x' (T 0) (pderiv m f)) 0) :
    HasDerivAt (fun t => T t (X l * f)) (derForm A' x' (fun g => T 0 (X l * g)) f +
      (a' * T 0 f + ∑ k, b' k * T 0 (pderiv (e k) f))) 0 := by
  rw [derForm_comb A' x' (T 0) _ (a 0) (b 0) e (hU 0)]
  simp only [hU]
  refine ((ha.fun_mul h0).fun_add (HasDerivAt.fun_sum (u := Finset.univ)
    fun k _ => (hb k).fun_mul (h1 (e k)))).congr_deriv ?_
  rw [Finset.sum_add_distrib]
  ring

theorem hasDerivAt_inner_gauss : ∀ (P Q : ℕ) (F : Fock (Ix P Q)) (A : ℝ → Matrix (Fin P) (Fin Q) ℂ) (x : ℝ → Ix P Q → ℂ) (v : ℝ → F.H) (A' : Matrix (Fin P) (Fin Q) ℂ) (x' : Ix P Q → ℂ), (∀ t, HasCoeff F (v t) (expPS (gaussPoly (A t) (x t)))) → (∀ i j, HasDerivAt (fun t => A t i j) (A' i j) 0) → (∀ l, HasDerivAt (fun t => x t l) (x' l) 0) → ∀ f : MvPolynomial (Ix P Q) ℂ, HasDerivAt (fun t => inner ℂ (F.ι f) (v t)) (∑ i, ∑ j, A' i j * inner ℂ (F.ι (MvPolynomial.pderiv (Sum.inl i) (MvPolynomial.pderiv (Sum.inr j) f))) (v 0) + ∑ l, x' l * inner ℂ (F.ι (MvPolynomial.pderiv l f)) (v 0)) 0 := by
  intro P Q F A x v A' x' hv hA hx f
  change HasDerivAt (fun t => pair F (v t) f) (derForm A' x' (pair F (v 0)) f) 0
  have key : ∀ (N : ℕ) (α : Ix P Q →₀ ℕ), α.degree ≤ N → ∀ c : ℂ,
      HasDerivAt (fun t => pair F (v t) (monomial α c)) (derForm A' x' (pair F (v 0)) (monomial α c)) 0 := by
    have h0 : ∀ c : ℂ, HasDerivAt (fun t => pair F (v t) (monomial 0 c))
        (derForm A' x' (pair F (v 0)) (monomial 0 c)) 0 := fun c => by
      have e : ∀ t, pair F (v t) (monomial 0 c) = (starRingEnd ℂ) c := fun t => by
        have e1 : (monomial 0 c : MvPolynomial (Ix P Q) ℂ) = c • monomial 0 1 := by
          rw [smul_monomial, smul_eq_mul, mul_one]
        change inner ℂ (F.ι (monomial 0 c)) (v t) = _
        rw [e1, map_smul, inner_smul_left, hv t 0]
        simp [expPS, MvPowerSeries.coeff_apply]
      simp only [e]
      refine (hasDerivAt_const _ _).congr_deriv ?_
      simp [derForm]
    intro N
    induction N with
    | zero =>
      intro α hα c
      obtain rfl : α = 0 := (Finsupp.degree_eq_zero_iff α).1 (Nat.le_zero.1 hα)
      exact h0 c
    | succ N ih =>
      intro α hα c
      by_cases hz : α = 0
      · subst hz; exact h0 c
      obtain ⟨l, hl⟩ : ∃ l, α l ≠ 0 := by
        by_contra hh
        push Not at hh
        exact hz (Finsupp.ext hh)
      obtain ⟨β, rfl⟩ : ∃ β, α = Finsupp.single l 1 + β :=
        exists_add_of_le (Finsupp.single_le_iff.2 (Nat.pos_of_ne_zero hl))
      have hβ : β.degree ≤ N := by
        rw [map_add, Finsupp.degree_single] at hα
        omega
      have e : (monomial (Finsupp.single l 1 + β) c : MvPolynomial (Ix P Q) ℂ) = X l * monomial β c := by
        rw [X, monomial_mul, one_mul]
      have h1 : ∀ m, HasDerivAt (fun t => pair F (v t) (pderiv m (monomial β c)))
          (derForm A' x' (pair F (v 0)) (pderiv m (monomial β c))) 0 := fun m => by
        rw [pderiv_monomial]
        exact ih _ ((Finsupp.degree_mono tsub_le_self).trans hβ) _
      rw [e]
      rcases l with i | j
      · rw [derForm_X_inl]
        exact step A' x' (fun t => pair F (v t)) _ (fun t => x t (Sum.inl i)) (fun t j => A t i j) _ _ Sum.inr
          (hx _) (hA i) (fun t => (GlobalTheory.T.gaussianVector_annihilator_equations P Q F _ _ _ (hv t)).1 i) _ (ih _ hβ c) h1
      · rw [derForm_X_inr]
        exact step A' x' (fun t => pair F (v t)) _ (fun t => x t (Sum.inr j)) (fun t i => A t i j) _ _ Sum.inl
          (hx _) (fun i => hA i j) (fun t => (GlobalTheory.T.gaussianVector_annihilator_equations P Q F _ _ _ (hv t)).2 j) _ (ih _ hβ c) h1
  induction f using MvPolynomial.induction_on' with
  | monomial α c => exact key _ α le_rfl c
  | add f g hf hg =>
    simp only [map_add]
    refine (hf.fun_add hg).congr_deriv ?_
    simp only [derForm, map_add, mul_add, Finset.sum_add_distrib]
    ring

end GlobalTheory.OscPairDer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermRe
section
noncomputable section

namespace GlobalTheory.Mem.SRe.ColRe

open Formalism.BasicNotions Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.SRe NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (Z : New D)

set_option maxHeartbeats 4000000 in

def hermRe (H : Formalism.L2.Herm.ColsHermS D) : Formalism.L2.Herm.ColsHermS (reD D Z) := by kcopy H

end GlobalTheory.Mem.SRe.ColRe

end
end

