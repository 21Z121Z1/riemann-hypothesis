import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1489
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1553
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1537
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1322

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSymplecticFormEqOrientedHomSymplecticForm
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilSchrodinger

theorem cA_eq_sigR (D : D7) (z : AE D) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig z = Formalism.L2.Theta.cA D z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add a b ha hb => rw [map_add, map_add, ha, hb]

theorem triple_sum_comm_reverse {ι κ μ M : Type} [Fintype ι] [Fintype κ] [Fintype μ] [AddCommMonoid M] (f : ι → κ → μ → M) :
    ∑ i, ∑ k, ∑ l, f i k l = ∑ l, ∑ k, ∑ i, f i k l := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun k _ => Finset.sum_comm]
  exact Finset.sum_comm

theorem symp_eq_symplO : ∀ (D : D7) (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
    ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
    ∀ x y : Formalism.IndefR.Datum.WO S T,
      GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB) x y =
        Formalism.IndefR.Datum.symplO S T x y := by
  intro D S T JA JB ξ hA hB x y
  have hB' : ∀ j l, ξ * incM D.host.F JB j l = incA D D.host.xi0 * incA D (S.gram⁻¹ j l) := by
    intro j l
    have h1 := congrFun (congrFun hB j) l
    rw [Matrix.smul_apply, smul_eq_mul] at h1
    rw [h1]
    show inclR (F := D.host.F) (AF D.host.F) (D.host.xi0 * S.gram⁻¹ j l) = _
    exact map_mul _ _ _
  have hA' : ∀ i k, incM D.host.F JA i k = incA D (T.gram k i) := by
    intro i k; subst hA; rfl
  unfold GlobalTheory.WeilM.symp GlobalTheory.WeilM.hTens Formalism.IndefR.Datum.symplO Formalism.IndefR.Datum.hO
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [triple_sum_comm_reverse]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  rw [hA', cA_eq_sigR]
  calc ξ * (x i j * incA D (T.gram k i) * incM D.host.F JB j l * Formalism.L2.Theta.cA D (y k l))
      = x i j * incA D (T.gram k i) * (ξ * incM D.host.F JB j l) * Formalism.L2.Theta.cA D (y k l) := by ring
    _ = _ := by rw [hB']; ring

end GlobalTheory.WeilSchrodinger

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationInvariantSchwartzUnique
section
open scoped FourierTransform SchwartzMap InnerProductSpace
open MeasureTheory

namespace GlobalTheory.TransInvSchwartz

theorem fourier_compSubConst {n : ℕ} (h : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (w ξ : EuclideanSpace ℝ (Fin n)) :
    𝓕 (SchwartzMap.compSubConstCLM ℂ w h) ξ = GlobalTheory.ArchSch.ech ⟪w, ξ⟫_ℝ * 𝓕 h ξ := by
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe, Real.fourier_eq', Real.fourier_eq', ← integral_const_mul]
  simp only [SchwartzMap.compSubConstCLM_apply, smul_eq_mul]
  rw [← integral_add_right_eq_self (fun v => Complex.exp (↑(-2 * Real.pi * ⟪v, ξ⟫_ℝ) * Complex.I) * h (v - w)) w]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [add_sub_cancel_right, GlobalTheory.ArchSch.ech, inner_add_left]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem eq_of_fourier_zero {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (μ : SchwartzMap V ℂ →L[ℂ] ℂ)
    (hμ : ∀ (a : V) (f g : SchwartzMap V ℂ), ⇑g = (fun x => f (x + a)) → μ g = μ f)
    (f g : SchwartzMap V ℂ)
    (hfg : 𝓕 (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) (toEuclidean (E := V)).symm f) 0 =
      𝓕 (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) (toEuclidean (E := V)).symm g) 0) :
    μ f = μ g := by
  set T := toEuclidean (E := V)
  set C := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) T.symm with hC
  let Ci := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) T
  have hCi : ∀ h, Ci (C h) = h := fun h => by ext x; simp [Ci, C]
  let Fe := SchwartzMap.fourierTransformCLE ℂ (E := 𝓢(EuclideanSpace ℝ (Fin (Module.finrank ℝ V)), ℂ))
  have hFe : ∀ h, Fe h = 𝓕 h := fun h => rfl
  let ℓ : 𝓢(EuclideanSpace ℝ (Fin (Module.finrank ℝ V)), ℂ) →L[ℂ] ℂ :=
    μ.comp (Ci.comp (Fe.symm : _ →L[ℂ] _))
  have hℓ : ∀ h, ℓ (𝓕 (C h)) = μ h := fun h => by
    show μ (Ci (Fe.symm (Fe (C h)))) = μ h
    rw [ContinuousLinearEquiv.symm_apply_apply, hCi]
  have hinv : ∀ L : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) →ₗ[ℝ] ℝ, ∀ F G : 𝓢(EuclideanSpace ℝ (Fin (Module.finrank ℝ V)), ℂ),
      ⇑G = (fun x => GlobalTheory.ArchSch.ech (L x) * F x) → ℓ G = ℓ F := by
    intro L F G hG
    set w := (InnerProductSpace.toDual ℝ _).symm (LinearMap.toContinuousLinearMap L)
    have hw : ∀ x, L x = ⟪w, x⟫_ℝ := fun x => by
      rw [InnerProductSpace.toDual_symm_apply]; rfl
    set h := Fe.symm F
    have hF : 𝓕 h = F := Fe.apply_symm_apply F
    have hG' : Fe (SchwartzMap.compSubConstCLM ℂ w h) = G := by
      ext ξ
      rw [hFe, fourier_compSubConst, hG, ← hF]
      simp only [hw]
    show μ (Ci (Fe.symm G)) = μ (Ci (Fe.symm F))
    rw [← hG', ContinuousLinearEquiv.symm_apply_apply]
    apply hμ (-T.symm w)
    ext x
    simp only [Ci, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply]
    rw [SchwartzMap.compSubConstCLM_apply, map_add, map_neg, ContinuousLinearEquiv.apply_symm_apply, sub_eq_add_neg]
  have := GlobalTheory.T.schwartz_functional_depends_on_value_at_zero ℓ hinv (𝓕 (C f)) (𝓕 (C g)) hfg
  rwa [hℓ, hℓ] at this

theorem dim_le_one : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (μ μ' : SchwartzMap V ℂ →L[ℂ] ℂ),
    (∀ (a : V) (f g : SchwartzMap V ℂ), ⇑g = (fun x => f (x + a)) → μ g = μ f) →
    (∀ (a : V) (f g : SchwartzMap V ℂ), ⇑g = (fun x => f (x + a)) → μ' g = μ' f) →
    μ ≠ 0 → ∃ c : ℂ, μ' = c • μ := by
  intro V _ _ _ μ μ' hμ hμ' h0
  set C := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) (toEuclidean (E := V)).symm with hC
  let Fe := SchwartzMap.fourierTransformCLE ℂ (E := 𝓢(EuclideanSpace ℝ (Fin (Module.finrank ℝ V)), ℂ))
  let Φ : SchwartzMap V ℂ → ℂ := fun f => Fe (C f) 0
  have hΦs : ∀ (c : ℂ) f, Φ (c • f) = c * Φ f := fun c f => by
    show Fe (C (c • f)) 0 = c * Fe (C f) 0
    rw [map_smul, map_smul]; rfl
  obtain ⟨f₀, hf₀⟩ : ∃ f₀, μ f₀ ≠ 0 := by
    by_contra hc; push_neg at hc; exact h0 (ContinuousLinearMap.ext hc)
  have hΦ0 : Φ f₀ ≠ 0 := by
    intro hz
    apply hf₀
    rw [eq_of_fourier_zero μ hμ f₀ 0 (by
      show Φ f₀ = Fe (C 0) 0
      rw [hz]; simp), map_zero]
  have hrep : ∀ ν : SchwartzMap V ℂ →L[ℂ] ℂ,
      (∀ (a : V) (f g : SchwartzMap V ℂ), ⇑g = (fun x => f (x + a)) → ν g = ν f) →
      ∀ f, ν f = (Φ f / Φ f₀) * ν f₀ := fun ν hν f => by
    rw [eq_of_fourier_zero ν hν f ((Φ f / Φ f₀) • f₀) (by
      show Φ f = Φ ((Φ f / Φ f₀) • f₀)
      rw [hΦs, div_mul_cancel₀ _ hΦ0]), map_smul, smul_eq_mul]
  refine ⟨μ' f₀ / μ f₀, ContinuousLinearMap.ext fun f => ?_⟩
  rw [ContinuousLinearMap.smul_apply, hrep μ' hμ' f, hrep μ hμ f, smul_eq_mul]
  field_simp

end GlobalTheory.TransInvSchwartz
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldingSectionsFiniteType
section
set_option autoImplicit false

namespace GlobalTheory.DegCmp

open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Indef.Tree
open GlobalTheory.FlagTan GlobalTheory.FlatLine
open scoped ENNReal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem fChart_exists_val {h : GenFrEx Xo c} (C : Reg.FChart h) {e : Formalism.L2.Pj.Ix Dw → ℤ} {f : Rul Xo c}
    (hf : f ∈ secZ Xo c e) : ∃ b : C.R, (b : Om C.Z) = ((∏ i, C.t i ^ e i : (Om C.Z)ˣ) : Om C.Z) * genVal C.Z f ∧
      ∀ (S : Type) [CommRing S] [Algebra c.F S] (ψ : C.R →ₐ[c.F] S) (z : FrPt Xo c S), FrMap ψ C.y z →
        evR Xo c f z = ψ b := by
  have hL : Reg.EvLaws Xo c := (Reg.evLaws_genFr_atlas E H Dw l Xo c).1
  obtain ⟨q, χ, y₀, hy₀⟩ := hL.test C.R C.y
  refine ⟨χ (f q y₀), ?_, fun S _ _ ψ z hz => ?_⟩
  · rw [genVal_apply h, evC, ← evR_frBor hf C.bor,
      evR_eq hf.1 (frMap_comp (χ := C.R.val.comp χ) hy₀ C.gen fun _ => rfl)]
    rfl
  · rw [evR_eq hf.1 (frMap_comp (χ := ψ.comp χ) hy₀ hz fun _ => rfl), AlgHom.comp_apply]

theorem genVal_idem_self (Z : Comp Xo c) : genVal Z (idem Z) = 1 := by
  have h : GenFrEx Xo c := (Reg.genFrEx_and_genFromTest E H Dw l Xo c).1
  rw [genVal_apply h, evC]
  exact evR_idem (liesOn_genFr h Z) (fromTest_of_isLocalRing _)

theorem fChart_evR_idem {h : GenFrEx Xo c} (C : Reg.FChart h) {S : Type} [CommRing S] [Algebra c.F S]
    {ψ : C.R →ₐ[c.F] S} {z : FrPt Xo c S} (hz : FrMap ψ C.y z) : evR Xo c (idem C.Z) z = 1 := by
  obtain ⟨b, hb, hb'⟩ := fChart_exists_val C (idem_mem_secZ C.Z)
  have : b = 1 := Subtype.ext (by simpa [genVal_idem_self] using hb)
  rw [hb' S ψ z hz, this, map_one]

theorem exists_fChart (h : GenFrEx Xo c) (Z : Comp Xo c) : ∃ C : Reg.FChart h, C.Z = Z := by
  obtain ⟨C, ψ, z, t', hz, hb⟩ := (Reg.evLaws_genFr_atlas E H Dw l Xo c).2.2.2 h (Om Z) (genFr h Z)
  refine ⟨C, by_contra fun hne => ?_⟩
  have h1 : evR Xo c (idem C.Z) (genFr h Z) = 0 := evC_eq_zero h (Ne.symm hne) (idem_mem_suppOn C.Z)
  rw [evR_frBor (idem_mem_secZ C.Z) hb, fChart_evR_idem C hz] at h1
  simp at h1

theorem exists_chart_read_at_frames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (σ : c.F →+* ℂ) (U : Unf Xo c σ r), IsUnf U → ∀ Z : Comp Xo c, ∃ (R : Subalgebra c.F (Om Z)) (_ : Algebra.FiniteType c.F R) (t : Formalism.L2.Pj.Ix Dw → (Om Z)ˣ), (∀ (e : Formalism.L2.Pj.Ix Dw → ℤ), ∀ f ∈ secZ Xo c e, ((∏ i, t i ^ e i : (Om Z)ˣ) : Om Z) * genVal Z f ∈ R) ∧ ∀ φ : R →+* ℂ, φ.comp (algebraMap c.F R) = σ → ∃ z ∈ framesOn U Z, ∃ s : Formalism.L2.Pj.Ix Dw → ℂˣ, ∀ (e : Formalism.L2.Pj.Ix Dw → ℤ), ∀ f ∈ secZ Xo c e, ∀ b : R, (b : Om Z) = ((∏ i, t i ^ e i : (Om Z)ˣ) : Om Z) * genVal Z f → φ b = ((∏ i, s i ^ e i : ℂˣ) : ℂ) * rdU U f z.1 z.2 := by
  intro E _ _ _ H Dw l Xo c r σ U hU Z
  have h : GenFrEx Xo c := (Reg.genFrEx_and_genFromTest E H Dw l Xo c).1
  obtain ⟨C, rfl⟩ := exists_fChart h Z
  haveI := C.sm
  refine ⟨C.R, inferInstance, C.t, fun e f hf => ?_, fun φ hφ => ?_⟩
  · obtain ⟨b, hb, -⟩ := fChart_exists_val C hf
    exact hb ▸ b.2
  · haveI : IsLocalRing (CAt σ) := inferInstanceAs (IsLocalRing ℂ)
    let ψ : C.R →ₐ[c.F] CAt σ := { (φ : C.R →+* CAt σ) with commutes' := fun a => DFunLike.congr_fun hφ a }
    obtain ⟨z, hz⟩ := exists_frMap ψ C.y
    obtain ⟨k, x, s, hs⟩ := hU.2.2.1 z
    have key : ∀ (e : Formalism.L2.Pj.Ix Dw → ℤ), ∀ f ∈ secZ Xo c e,
        toC (σ := σ) (evR Xo c f z) = ((∏ i, (show ℂˣ from s i) ^ e i : ℂˣ) : ℂ) * rdU U f k x.1 := fun e f hf => by
      simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, x.2, dif_pos]
      exact evR_frBor (S := CAt σ) hf hs
    refine ⟨⟨k, x.1⟩, by_contra fun hn => ?_, s, fun e f hf b hb => ?_⟩
    · have h1 := key 0 _ (idem_mem_secZ C.Z)
      rw [rdU_eq_zero U (idem_mem_suppOn C.Z) hn, mul_zero, fChart_evR_idem C hz] at h1
      exact one_ne_zero (α := ℂ) h1
    · obtain ⟨b', hb', h2⟩ := fChart_exists_val C hf
      obtain rfl : b = b' := Subtype.ext (hb.trans hb'.symm)
      exact (h2 _ ψ z hz).symm.trans (key e f hf)

end GlobalTheory.DegCmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentBlockTriangularNilpotent
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

noncomputable section

namespace GlobalTheory.LeviHC.UnipFrame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem incM_mul' {l m k : ℕ} (A : Matrix (Fin l) (Fin m) E) (B : Matrix (Fin m) (Fin k) E) :
    incM F (A * B) = incM F A * incM F B := by
  unfold incM
  exact Matrix.map_mul (f := (inclR (F := F) (E := E) (AF F) : E →+* AE F E))

theorem incM_one' {m : ℕ} : incM F (1 : Matrix (Fin m) (Fin m) E) = 1 := by
  unfold incM
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem mem_unip_of_strictBlockTri : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n n₁ : ℕ) (Y : Spc F E n) (H : Plane E n n₁) (R : Matrix (Fin (1 + n₁ + 1)) (Fin n) E), frame H * R = 1 → R * frame H = 1 →
    ∀ u : UA σ Y.J, (∀ i j, blk n₁ j < blk n₁ i + 1 → (incM F R * (mat u - 1 : Matrix (Fin n) (Fin n) (AE F E)) * incM F (frame H) :
        Matrix (Fin (1 + n₁ + 1)) (Fin (1 + n₁ + 1)) (AE F E)) i j = 0) →
      u ∈ unip σ Y H := by
  intro F E _ _ _ _ _ σ n n₁ Y H R hQR hRQ u hW
  set Wm : Matrix (Fin (1 + n₁ + 1)) (Fin (1 + n₁ + 1)) (AE F E) :=
    incM F R * (mat u - 1 : Matrix (Fin n) (Fin n) (AE F E)) * incM F (frame H) with hWm
  have hQ : incM F (frame H) * incM F R = 1 := by rw [← incM_mul', hQR, incM_one']
  have key : (mat u - 1 : Matrix (Fin n) (Fin n) (AE F E)) * incM F (frame H) = incM F (frame H) * Wm := by
    rw [hWm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQ, Matrix.one_mul]
  have hmv : ∀ v, mat u *ᵥ (incM F (frame H) *ᵥ v) = incM F (frame H) *ᵥ v + incM F (frame H) *ᵥ (Wm *ᵥ v) := by
    intro v
    have e : mat u = 1 + (mat u - 1 : Matrix (Fin n) (Fin n) (AE F E)) := by abel
    rw [e, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec, key, ← Matrix.mulVec_mulVec]
  set x0 : Fin (1 + n₁ + 1) := Fin.castAdd 1 (Fin.castAdd n₁ 0) with hx0
  have hx : incV F H.x = incM F (frame H) *ᵥ Pi.single x0 1 := by
    ext r
    rw [Matrix.mulVec_single]
    simp [incV, incM, hx0, frame_alt]
  have hWx : Wm *ᵥ Pi.single x0 1 = 0 := by
    ext i
    simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Pi.zero_apply]
    apply hW
    rw [hx0, block_matrix_mulVec_basis]
    omega
  apply Subgroup.subset_closure
  refine ⟨?_, fun z => ⟨∑ k, Wm x0 (mid k) * z k, ?_⟩⟩
  · rw [hx, hmv, hWx, Matrix.mulVec_zero, add_zero]
  · let vz : Fin (1 + n₁ + 1) → AE F E := Fin.addCases (Fin.addCases (fun _ => 0) fun k => z k) fun _ => 0
    have hι : incM F H.ι *ᵥ z = incM F (frame H) *ᵥ vz := by
      ext r
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_add, vz, Fin.addCases_left, Fin.addCases_right, mul_zero,
        Finset.sum_const_zero, zero_add, add_zero]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [incM, frame]
    have hWz : Wm *ᵥ vz = (∑ k, Wm x0 (mid k) * z k) • Pi.single x0 1 := by
      have hs : ∀ i, (Wm *ᵥ vz) i = ∑ k, Wm i (mid k) * z k := by
        intro i
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_add, vz, Fin.addCases_left, Fin.addCases_right, mul_zero,
          Finset.sum_const_zero, zero_add, add_zero]
        rfl
      ext i
      rw [hs]
      induction i using Fin.addCases with
      | left i =>
        induction i using Fin.addCases with
        | left a =>
          have ha : a = 0 := Subsingleton.elim _ _
          subst ha
          simp [hx0]
        | right k' =>
          have hne : (Fin.castAdd 1 (Fin.natAdd 1 k') : Fin (1 + n₁ + 1)) ≠ x0 := by
            rw [hx0]; intro h; have := congrArg Fin.val h; simp at this
          rw [Pi.smul_apply, Pi.single_eq_of_ne hne, smul_zero]
          refine Finset.sum_eq_zero fun k _ => ?_
          rw [hW, zero_mul]
          show blk n₁ (mid k) < blk n₁ (mid k') + 1
          rw [blk_mid, blk_mid]
          omega
      | right a =>
        have hne : (Fin.natAdd (1 + n₁) a : Fin (1 + n₁ + 1)) ≠ x0 := by
          rw [hx0]; intro h; have := congrArg Fin.val h; (simp at this) <;> omega
        rw [Pi.smul_apply, Pi.single_eq_of_ne hne, smul_zero]
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [hW, zero_mul]
        rw [blk_mid, blk_y]
        omega
    rw [hι, hmv, hWz, Matrix.mulVec_smul, ← hx]

end GlobalTheory.LeviHC.UnipFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryPairOfTransposedGramInverseGram
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilSchrodinger

theorem matchPair_cA_eq_sigR (D : D7) (x : AE D) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig x = sigR (AF D.host.F) D.sp.cm.sig x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA, sigR]
  | add x y hx hy => simp_all

theorem matchPair_inv_transpose {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
    (Bm Bi P Q Cm Ci : Matrix n n R) (hBB : Bm * Bi = 1) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hCC : Ci * Cm = 1) (hb : Bmᵀ * P * Cm = P) : Ci * Q * Biᵀ = Q := by
  have e1 : Biᵀ * Bmᵀ = 1 := by rw [← Matrix.transpose_mul, hBB, Matrix.transpose_one]
  have e2 : P * Cm = Biᵀ * P := by
    calc P * Cm = (Biᵀ * Bmᵀ) * P * Cm := by rw [e1, Matrix.one_mul]
      _ = Biᵀ * (Bmᵀ * P * Cm) := by simp only [Matrix.mul_assoc]
      _ = Biᵀ * P := by rw [hb]
  have e3 : Cm * Q = Q * Biᵀ := by
    calc Cm * Q = (Q * P) * Cm * Q := by rw [hQP, Matrix.one_mul]
      _ = Q * (P * Cm) * Q := by simp only [Matrix.mul_assoc]
      _ = Q * Biᵀ * (P * Q) := by rw [e2]; simp only [Matrix.mul_assoc]
      _ = Q * Biᵀ := by rw [hPQ, Matrix.mul_one]
  calc Ci * Q * Biᵀ = Ci * (Q * Biᵀ) := Matrix.mul_assoc _ _ _
    _ = Ci * (Cm * Q) := by rw [e3]
    _ = Q := by rw [← Matrix.mul_assoc, hCC, Matrix.one_mul]

theorem matchPair_map_cA (D : D7) {n m : ℕ} (M : Matrix (Fin n) (Fin m) (AE D)) :
    M.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) = M.map (sigR (AF D.host.F) D.sp.cm.sig) := by
  ext i j; exact matchPair_cA_eq_sigR D (M i j)

theorem matchPair_memT (D : D7) (T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (hA : JA = T.gramᵀ)
    (a : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA)) : (a.1 : GL (Fin T.rank) (AE D)) ∈ HR (AF D.host.F) D.sp.cm.sig T.gram := by
  have ha : a.1.1ᵀ * incM D.host.F JA * a.1.1.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) = incM D.host.F JA := a.2
  show Formalism.UG.cT _ _ * _ * _ = _
  have := congrArg Matrix.transpose ha
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hA] at this
  unfold Formalism.UG.cT JR
  rw [← matchPair_map_cA]
  have e : (incM D.host.F T.gramᵀ)ᵀ = incM D.host.F T.gram := by
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, Matrix.transpose_map]
  rw [e] at this
  exact (Matrix.mul_assoc _ _ _).trans this

theorem matchPair_keeps_inv_gram (D : D7) (S : HSp D) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (ξ : AF D.host.F ⊗[D.host.F] D.host.E)
    (hB : ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹)) (b : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB)) :
    b.1.1ᵀ * incM D.host.F S.gram⁻¹ * b.1.1.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) = incM D.host.F S.gram⁻¹ := by
  have hb : b.1.1ᵀ * incM D.host.F JB * b.1.1.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) = incM D.host.F JB := b.2
  have hxi : IsUnit (incA D D.host.xi0) := (isUnit_iff_ne_zero.2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)).map _
  have hsc : (incM D.host.F (D.host.xi0 • S.gram⁻¹) : Matrix (Fin S.rank) (Fin S.rank) (AE D)) =
      (incA D D.host.xi0 : AE D) • (incM D.host.F S.gram⁻¹ : Matrix (Fin S.rank) (Fin S.rank) (AE D)) := by
    ext i j
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, incA]
  have t1 : ∀ (r : AE D) (X Y : Matrix (Fin S.rank) (Fin S.rank) (AE D)), X * (r • Y) = r • (X * Y) :=
    fun r X Y => Matrix.mul_smul X r Y
  have t2 : ∀ (r : AE D) (X Y : Matrix (Fin S.rank) (Fin S.rank) (AE D)), (r • X) * Y = r • (X * Y) :=
    fun r X Y => Matrix.smul_mul r X Y
  have e1 := congrArg (fun M => ξ • M) hb
  rw [← t2, ← t1, hB, hsc] at e1
  have e2 : b.1.1ᵀ * ((incA D D.host.xi0 : AE D) • incM D.host.F S.gram⁻¹) * b.1.1.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) =
      (incA D D.host.xi0 : AE D) • (b.1.1ᵀ * incM D.host.F S.gram⁻¹ * b.1.1.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig)) := by
    rw [t1, t2]
  rw [e2] at e1
  exact hxi.smul_left_cancel.1 e1

set_option maxHeartbeats 1000000 in

theorem matchPair_memS (D : D7) (S : HSp D) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (ξ : AF D.host.F ⊗[D.host.F] D.host.E)
    (hB : ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹)) (b : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB)) :
    ∃ G : GL (Fin S.rank) (AE D), G.1 = (b⁻¹).1.1ᵀ ∧ G ∈ HR (AF D.host.F) D.sp.cm.sig S.gram := by
  have hBB : b.1.1 * (b⁻¹).1.1 = 1 := Units.mul_inv b.1
  have hBB' : (b⁻¹).1.1 * b.1.1 = 1 := Units.inv_mul b.1
  have hdet : IsUnit S.gram.det := (Formalism.L2.Theta.gram_det_ne S).isUnit
  have hPQ : incM D.host.F S.gram⁻¹ * incM D.host.F S.gram = 1 := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hQP : incM D.host.F S.gram * incM D.host.F S.gram⁻¹ = 1 := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hdet,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hCC : (b⁻¹).1.1.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) * b.1.1.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) = 1 := by
    have := map_mul ((GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig).toRingHom.mapMatrix :
      Matrix (Fin S.rank) (Fin S.rank) (AE D) →+* Matrix (Fin S.rank) (Fin S.rank) (AE D)) (b⁻¹).1.1 b.1.1
    rw [hBB', map_one] at this
    exact this.symm
  have key := matchPair_inv_transpose _ _ _ _ _ _ hBB hPQ hQP hCC (matchPair_keeps_inv_gram D S JB ξ hB b)
  refine ⟨⟨(b⁻¹).1.1ᵀ, b.1.1ᵀ, by rw [← Matrix.transpose_mul, hBB, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, hBB', Matrix.transpose_one]⟩, rfl, ?_⟩
  show Formalism.UG.cT _ _ * _ * _ = _
  unfold Formalism.UG.cT JR
  rw [← matchPair_map_cA, Matrix.transpose_map, Matrix.transpose_transpose]
  exact key

theorem match_pair : ∀ (D : D7) (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
    ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
    ∀ (a : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA))
      (b : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB)),
      ∃ (g : GA D S) (h : GA D T), mt T h = a.1.1 ∧ mt S g = (b⁻¹).1.1ᵀ := by
  intro D S T JA JB ξ hA hB a b
  obtain ⟨G, hG, hGm⟩ := matchPair_memS D S JB ξ hB b
  exact ⟨⟨G, hGm⟩, ⟨a.1, matchPair_memT D T JA hA a⟩, rfl, hG⟩

end GlobalTheory.WeilSchrodinger

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversalEnvelopingLineDerivatives
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

namespace GlobalTheory.LeviHC.WordAlg

theorem adjoin_word : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (w : InfinitePlace F) (τ : EmbOver E w) (D : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (SmG σ J)), IsDer σ J τ D →
    ∀ u ∈ Algebra.adjoin ℂ (Set.range D), ∃ z : List (ℝ → GAd σ J) →₀ ℂ,
      (∀ l ∈ z.support, ∀ γ ∈ l, IsRealLine σ J γ) ∧ ∀ f : SmG σ J, dop z f.1 = (u f).1 := by
  intro F E _ _ _ _ _ σ h n J hJ w τ D hD u hu
  classical
  induction hu using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨X, rfl⟩ := hx
    obtain ⟨γ₁, γ₂, e1, e2, e3⟩ := exists_lines h hJ τ X
    generalize (1 / 2 : ℂ) • (X - adj (J.map τ.1) X) = X₁ at e1 e3
    generalize (-Complex.I / 2 : ℂ) • (X + adj (J.map τ.1) X) = X₂ at e2 e3
    have hX : D X = D X₁ + Complex.I • D X₂ := by rw [← map_smul, ← map_add, ← e3]
    refine ⟨Finsupp.single [γ₁] 1 + Finsupp.single [γ₂] Complex.I, fun l hl γ hγ => ?_, fun f => ?_⟩
    · rcases Finset.mem_union.1 (Finsupp.support_add hl) with hl | hl <;>
        obtain rfl := Finset.mem_singleton.1 (Finsupp.support_single_subset hl) <;>
        obtain rfl := List.mem_singleton.1 hγ
      exacts [e1.isRealLine h, e2.isRealLine h]
    · rw [dop_add_comb, dop_single, dop_single]
      rw [hX, LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul, hD.2 _ _ e1 f,
        hD.2 _ _ e2 f]
      funext g
      simp
  | algebraMap c =>
    refine ⟨Finsupp.single [] c, fun l hl γ hγ => ?_, fun f => ?_⟩
    · obtain rfl := Finset.mem_singleton.1 (Finsupp.support_single_subset hl)
      simp at hγ
    rw [dop_single]
    funext g
    simp [Algebra.algebraMap_eq_smul_one]
  | add x y _ _ hx hy =>
    obtain ⟨z, hz, ez⟩ := hx
    obtain ⟨z', hz', ez'⟩ := hy
    refine ⟨z + z', fun l hl γ hγ => ?_, fun f => ?_⟩
    · rcases Finset.mem_union.1 (Finsupp.support_add hl) with hl | hl
      exacts [hz l hl γ hγ, hz' l hl γ hγ]
    · rw [dop_add_comb, ez, ez', LinearMap.add_apply, Submodule.coe_add]
  | mul x y _ _ hx hy =>
    obtain ⟨z, hz, ez⟩ := hx
    obtain ⟨z', hz', ez'⟩ := hy
    refine ⟨wordMul z z', fun m hm γ hγ => ?_, fun f => ?_⟩
    · obtain ⟨l, hl, l', hl', rfl⟩ := mem_support_wordMul hm
      rcases List.mem_append.1 hγ with h' | h'
      exacts [hz l hl γ h', hz' l' hl' γ h']
    · obtain ⟨-, h2⟩ := GlobalTheory.UAut.DopComp.dop_dop σ J f.1 f.2 z z' hz hz'
      rw [← h2, ez', ez (y f), Module.End.mul_apply]

end GlobalTheory.LeviHC.WordAlg
end

