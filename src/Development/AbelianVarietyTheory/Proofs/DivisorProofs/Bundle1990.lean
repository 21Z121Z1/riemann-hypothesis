import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1979
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1842
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1980
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1958
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1974
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairFirstConjEqSumCosetIndicators
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1848
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1681
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1776
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1840
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1839
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1757
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1866
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1742
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1810
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1771
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import CompanionTheory.EightfoldTheory.ZeroLevelTheory.LocalLanglands.Imports
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0253
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0702
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0794
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0730
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0802
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0729
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0750
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0793
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0809
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0723
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0349
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0327
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0780
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1977
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1981
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0026
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1714
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1876
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1918
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1934
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1982

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerOperatorHeisenbergLawApplyStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergIntertwiner_eq_twisted_weilOperator : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' →
    ∀ (K : GL (Fin a') (Fv F Bs.v₁) →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.V'.J),
    (∀ g, K g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ Γ.V' (evFin F Bs.v₁) ∧
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (K g)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW Bs.τ₁) = g.val ∧
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (K g)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (Bs.τ₁.comp σ)) =
        (Γ.V'.J.map Bs.τ₁)⁻¹ * ((g⁻¹ : GL _ _).val)ᵀ * Γ.V'.J.map Bs.τ₁) →
    ∀ (S : GL (Fin a') (Fv F Bs.v₁) → ((Fin a' × Fin (a + a') → Fv F Bs.v₁) → ℂ) → (Fin a' × Fin (a + a') → Fv F Bs.v₁) → ℂ),
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, S g φ ∈ GlobalTheory.WeilM.SB _) →
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ' ∈ GlobalTheory.WeilM.SB _, ∀ c : ℂ, S g (c • φ + φ') = c • S g φ + S g φ') →
    (∀ g g', ∀ φ ∈ GlobalTheory.WeilM.SB _, S (g * g') φ = S g (S g' φ)) →
    (∀ φ ∈ GlobalTheory.WeilM.SB _, S 1 φ = φ) →
    (∀ g (γ : Matrix (Fin a') (Fin (a + a')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F Bs.v₁) γ →
      ∀ φ ∈ GlobalTheory.WeilM.SB _,
        S g (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) φ) =
          GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁)
            (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (K g, (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.W.J)) γ)) (S g φ)) →
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ μ : @Measure (Fin a' × Fin (a + a') → Fv F Bs.v₁) (borel _),
      @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∫⁻ y, ‖S g φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ) →
    ∃ ν α : (Fv F Bs.v₁)ˣ →* ℂˣ, (∀ x, ‖(ν x : ℂ)‖ = 1) ∧
      ∀ ι, Γ.M'.IsLinBar Bs.ψ Bs.τ₁ 1 1 ι → ∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (S g φ) = omB ν α g 1 (ι φ) := by
  first | exact @GlobalTheory.LinModelLocal.exists_omB_of_linBar | exact GlobalTheory.LinModelLocal.exists_omB_of_linBar | (intros; apply GlobalTheory.LinModelLocal.exists_omB_of_linBar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSubmoduleEqTopOfGaussianMemDerivStableStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzSubmodule_eq_top_of_gaussian_mem_derivStable : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (N : Submodule ℂ (SchwartzMap V ℂ))
    (g : SchwartzMap V ℂ) (Q : V →L[ℝ] V →L[ℝ] ℂ) (c : ℝ), 0 < c → (∀ x, c * ‖x‖ ^ 2 ≤ (Q x x).re) →
    (∀ x, g x = Complex.exp (-(Q x x))) → g ∈ N →
    (∀ (v : V) (f f₁ : SchwartzMap V ℂ), f ∈ N → (∀ x, f₁ x = fderiv ℝ (⇑f) x v) → f₁ ∈ N) →
    (∀ (ℓ : V →L[ℝ] ℝ) (f f₁ : SchwartzMap V ℂ), f ∈ N → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ N) →
    Dense (N : Set (SchwartzMap V ℂ)) := by
  first | exact @GlobalTheory.SchwartzGaussDense.dense_of_gaussian_mem | exact GlobalTheory.SchwartzGaussDense.dense_of_gaussian_mem | (intros; apply GlobalTheory.SchwartzGaussDense.dense_of_gaussian_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SoTypeStableArchimedeanStatement
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.so_type_stable_archimedean : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ g' ∈ UAt σ G.V' (evI F), ∀ h ∈ UAt σ G.W (evI F), ∀ Φ' ∈ G.M'.So B.ψ B.τ₁,
      om' (g', h) Φ' ∈ G.M'.So B.ψ B.τ₁ := by
  first | exact @GlobalTheory.ThK.so_stable_arch | exact GlobalTheory.ThK.so_stable_arch | (intros; apply GlobalTheory.ThK.so_stable_arch <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabAtPair
section
noncomputable section

namespace GlobalTheory.ThK.LemF.QuotInv

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {R : Type} [Zero R]

def hAd (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (z y : Fin n → AE F E) : AE F E :=
  z ⬝ᵥ (incM F J *ᵥ fun i => cA σ (y i))

theorem cA_cA {σ : E →ₐ[F] E} (hσ : ∀ e, σ (σ e) = e) (z : AE F E) : cA σ (cA σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => exact congrArg (a ⊗ₜ[F] ·) (hσ e)
  | add x y hx hy => rw [map_add, map_add, hx, hy]

variable (F E) in

def vecAt (m : ℕ) (ev : AF F → R) : AddSubgroup (Fin m → AE F E) where
  carrier := {w | At ev w}
  zero_mem' := fun u _ => smul_zero u
  add_mem' := fun {a b} ha hb u hu => by rw [smul_add, ha u hu, hb u hu, add_zero]
  neg_mem' := fun {a} ha u hu => by rw [smul_neg, ha u hu, neg_zero]

def skewAt (σ : E →ₐ[F] E) (ev : AF F → R) : AddSubgroup (AE F E) where
  carrier := {c | At ev c ∧ cA σ c = -c}
  zero_mem' := ⟨fun u _ => smul_zero u, by simp⟩
  add_mem' := fun {a b} ha hb =>
    ⟨fun u hu => by rw [smul_add, ha.1 u hu, hb.1 u hu, add_zero], by rw [map_add, ha.2, hb.2, neg_add]⟩
  neg_mem' := fun {a} ha => ⟨fun u hu => by rw [smul_neg, ha.1 u hu, neg_zero], by rw [map_neg, ha.2]⟩

def vecAtSmul {m : ℕ} {ev : AF F → R} (s : AE F E) : vecAt F E m ev →+ vecAt F E m ev where
  toFun w := ⟨s • w.1, fun u hu => by rw [smul_comm, w.2 u hu, smul_zero]⟩
  map_zero' := Subtype.ext (smul_zero s)
  map_add' a b := Subtype.ext (smul_add s a.1 b.1)

def normSmul {σ : E →ₐ[F] E} {ev : AF F → R} (hσ : ∀ e, σ (σ e) = e) (s : AE F E) : skewAt σ ev →+ skewAt σ ev where
  toFun c := ⟨(s * cA σ s) * c.1, fun u hu => by rw [← mul_smul_comm, c.2.1 u hu, mul_zero], by
    rw [map_mul, map_mul, cA_cA hσ, c.2.2]; ring⟩
  map_zero' := Subtype.ext (mul_zero _)
  map_add' a b := Subtype.ext (mul_add _ a.1 b.1)

variable (σ) in

def stabAtPair {n : ℕ} (X : Spc F E n) (ev : AF F → R) (x y : Fin n → E) : Subgroup (stabAt σ X ev x) where
  carrier := {q | mat q.1.1 *ᵥ incV F y = incV F y}
  one_mem' := by
    show mat (1 : UA σ X.J) *ᵥ incV F y = incV F y
    rw [GlobalTheory.StabHaar.mat_one, Matrix.one_mulVec]
  mul_mem' := by
    intro g h hg hh
    show mat (g.1.1 * h.1.1) *ᵥ incV F y = incV F y
    rw [GlobalTheory.StabHaar.mat_mul, ← Matrix.mulVec_mulVec]
    rw [show mat h.1.1 *ᵥ incV F y = incV F y from hh]
    exact hg
  inv_mem' := by
    intro g hg
    show mat g.1.1⁻¹ *ᵥ incV F y = incV F y
    have hg' : mat g.1.1 *ᵥ incV F y = incV F y := hg
    conv_lhs => rw [← hg']
    rw [Matrix.mulVec_mulVec, GlobalTheory.StabHaar.mat_inv_mul, Matrix.one_mulVec]

variable (σ) in

def nMat {n m : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E) (ι : Matrix (Fin n) (Fin m) E)
    (w : Fin m → AE F E) (c : AE F E) : Matrix (Fin n) (Fin n) (AE F E) :=
  1 + Matrix.vecMulVec (incM F ι *ᵥ w + c • incV F x) (incM F J *ᵥ fun i => cA σ (incV F x i)) -
    Matrix.vecMulVec (incV F x) (incM F J *ᵥ fun i => cA σ ((incM F ι *ᵥ w) i))

theorem nMat_mulVec (σ : E →ₐ[F] E) {n m : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E)
    (ι : Matrix (Fin n) (Fin m) E) (w : Fin m → AE F E) (c : AE F E) (z : Fin n → AE F E) :
    nMat σ J x ι w c *ᵥ z = z + hAd σ J z (incV F x) • (incM F ι *ᵥ w + c • incV F x) -
      hAd σ J z (incM F ι *ᵥ w) • incV F x := by
  have key : ∀ (p r : Fin n → AE F E), Matrix.vecMulVec p r *ᵥ z = (z ⬝ᵥ r) • p := fun p r => by
    funext i
    simp only [Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [nMat, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, key, hAd]

end GlobalTheory.ThK.LemF.QuotInv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairFirstConjEqSumCosetIndicatorsStatement
section
open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardPairFirst_conj_eq_sum_cosetIndicators : ∀ {D : D7} (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d), a ≤ d → ∀ (e : AE D) (𝔪 : Ideal (𝓞 D.host.E)), GoodMod e 𝔪 →
  ∀ ν : (AE D)ˣ →* Circle, KillsCong ν 𝔪 → ∀ β : GL (Fin S.rank) (EAf D), IsIntM β.val → IsIntM (β⁻¹).val →
  ∀ R : Finset (Formalism.MainNotions.StandardLatticesGL3.GA D a), (∀ r ∈ R, r ∈ intG D a) → (∀ k ∈ intG D a, ∃! r, r ∈ R ∧ CongOne D 𝔪 (r⁻¹ * k)) →
  ∀ z : Formalism.MainNotions.StandardLatticesGL3.GA D a → Matrix (Fin d) (Fin a) D.host.E, (∀ r ∈ R, IsIntE (z r) ∧ Approx 𝔪 0 r (z r)) →
  (fun w => starRingEnd ℂ (stdFst ν e 𝔪 S T β 1 w)) =
    starRingEnd ℂ (unitChar ν e β.val) • ∑ r ∈ R, unitChar ν e (matE r) • cosInd e 𝔪 hS hT (z r) := by
  first | exact @GlobalTheory.StdExpand.conj_stdFst_eq_sum | exact GlobalTheory.StdExpand.conj_stdFst_eq_sum | (intros; apply GlobalTheory.StdExpand.conj_stdFst_eq_sum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardThetaDatumPresentationLevelNorm
section
noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.FunObj.StdDatum

theorem pres_stdSum : ∀ (D : D7) (δ t0 : ℂ), Crv D ⊤ δ → ∀ {a d : ℕ} (e0 : VC D a d → ℂ), oddE0 D ⊤ δ t0 a d e0 → a ≤ d → ∀ (W : WeilO D ⊤ δ a d e0) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → IsCoprime 𝔪 (D.host.conj • 𝔪) → IsCoprime 𝔪 D.host.𝔟 → (∀ u, IntU D u → (u : AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → W.chV'.f u = 1) → ∀ R : Finset (GA D a), (∀ r ∈ R, r ∈ intG D a) → (∀ k ∈ intG D a, ∃! r, r ∈ R ∧ CongOne D 𝔪 (r⁻¹ * k)) → (∀ k ∈ intG D a, W.Om k 1 (stdSum W 𝔪 0 R) = stdSum W 𝔪 0 R) → Pres D ⊤ δ (Ideal.absNorm 𝔪) e0 (stdSum W 𝔪 0 R) := by
  intro D δ t0 hc a d e0 hv had W 𝔪 h𝔪 hco hb _hchar R hR huniq _hfix
  have he : e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d) := hv.1
  have hN0 : 0 < Ideal.absNorm 𝔪 := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 h𝔪)
  have hidx := GlobalTheory.T.index_standard_inf_skewThetaLattice_eq_absNorm_pow D δ hc 𝔪 h𝔪 hco a d
  haveI hfin : Finite (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d) ⧸
      (La0 D (tor0 D ⊤ δ) a d).addSubgroupOf (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d))) :=
    AddSubgroup.index_ne_zero_iff_finite.1 (by rw [hidx]; positivity)
  letI : Fintype (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d) ⧸
      (La0 D (tor0 D ⊤ δ) a d).addSubgroupOf (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d))) := Fintype.ofFinite _
  have wsm : ∀ (x : VC D a d) (c : ℂ) (G : VC D a d → ℂ), Wd D (tor0 D ⊤ δ) x (c • G) = c • Wd D (tor0 D ⊤ δ) x G := by
    intro x c G; funext z; simp only [Wd, U, Pi.smul_apply, smul_eq_mul]; ring
  have hr : ∀ i : R, ∃ (c : ℂ) (x : Matrix (Fin d) (Fin a) D.host.E), (∃ m : ℕ, 0 < m ∧ c ^ m = 1) ∧
      pt D (tor0 D ⊤ δ) δ x ∈ La0 D (tor0 D ⊤ δ) a d ∧
      (∀ i' j, (x.map (inc D) - (unitBlock D 0 a d).map (inc D) *
        ((((i : GA D a)⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i' j ∈ hatId D 𝔪) ∧
      W.Om i 1 (cosetV D δ 𝔪 0 a d e0) = ((Real.sqrt ((Ideal.absNorm 𝔪 : ℝ) ^ (a * d)) : ℂ))⁻¹ •
        (c • Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ x)
          (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0)) := by
    intro i
    obtain ⟨c, hcm, hce⟩ := GlobalTheory.T.weilOperator_integral_point_vacuum_rootOfUnity_smul D δ hc e0 he W i (hR i i.2)
    obtain ⟨x, hx, hxc, hom⟩ := GlobalTheory.T.weilAction_cosetVector_eq_translate_unitVector D δ hc e0 he W 𝔪 h𝔪 i (hR i i.2)
    refine ⟨c, x, hcm, hx, hxc, ?_⟩
    rw [hom, GlobalTheory.T.weil_integralPoint_skewLatticeUnitVector_same_eigen D δ hc e0 he W 𝔪 h𝔪 i (hR i i.2) c hce, wsm]
  choose c x hcm hx hxc hom using hr
  choose χ hχ using fun i : R => GlobalTheory.T.exists_addChar_thetaCommutatorPhase_skewLattice D δ hc 𝔪 (pt D (tor0 D ⊤ δ) δ (x i)) (hx i)
  have hone : ∀ k : GA D a, CongOne D 𝔪 (k⁻¹ * k) := by
    intro k i' j
    rw [inv_mul_cancel]
    simp
  have hinj : Function.Injective χ := by
    intro i j hij
    have hk : ∀ y ∈ La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d),
        Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (x i)) y =
          Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (x j)) y := by
      intro y hy
      rw [← hχ i ⟨y, hy⟩, ← hχ j ⟨y, hy⟩, hij]
    have h1 := GlobalTheory.T.stabilizer_congruent_of_commutatorPhase_eq D δ hc 𝔪 h𝔪 hco hb had i j (hR i i.2) (hR j j.2) (x i) (x j) (hx i) (hx j) (hxc i) (hxc j) hk
    exact Subtype.ext ((huniq j (hR j j.2)).unique ⟨i.2, h1⟩ ⟨j.2, hone j⟩)
  have hcard : Fintype.card R ≤ Ideal.absNorm 𝔪 ^ (a * d) := by
    rw [Fintype.card_coe]
    refine (GlobalTheory.T.card_principalCongruence_transversal_le_absNorm_pow D 𝔪 h𝔪 a R hR huniq).trans (Nat.pow_le_pow_right hN0 ?_)
    rw [pow_two]; exact Nat.mul_le_mul_left a had
  obtain ⟨rr, hrr, hint, hρ⟩ := GlobalTheory.T.sum_norm_sq_le_of_rootOfUnity_addChar_combination (Ideal.absNorm 𝔪) (a * d) c χ hN0 hcm hinj
    (by rw [← hidx, AddSubgroup.index_eq_card, Nat.card_eq_fintype_card]) hcard
  choose z hz hzN using fun q : (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d) ⧸
      (La0 D (tor0 D ⊤ δ) a d).addSubgroupOf (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d))) =>
    GlobalTheory.T.skewIdealLattice_point_rational_normKills D δ hc 𝔪 h𝔪 _ (Quotient.out q).2
  set e := Fintype.equivFin (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d) ⧸
      (La0 D (tor0 D ⊤ δ) a d).addSubgroupOf (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)))
  refine ⟨_, fun i => rr (e.symm i), fun i => z (e.symm i), fun i => hzN _, fun i => hint _, fun ρ => ?_, ?_⟩
  · rw [e.symm.sum_comp (fun q => ‖ρ (rr q)‖)]; exact hρ ρ
  funext y
  rw [e.symm.sum_comp (fun q => ((rr q : Qbar) : ℂ) * Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (z q)) e0 y)]
  simp only [stdSum, Finset.sum_apply]
  rw [← Finset.sum_coe_sort R]
  simp only [hom, Pi.smul_apply, smul_eq_mul, GlobalTheory.T.standardLattice_translate_unitVector_vacuum_expansion D δ hc 𝔪 h𝔪 e0 he _ (hx _), hidx,
    finsum_eq_sum_of_fintype, hrr, ← hz]
  have hs : ((Real.sqrt ((Ideal.absNorm 𝔪 : ℝ) ^ (a * d)) : ℂ))⁻¹ *
      ((Real.sqrt (((Ideal.absNorm 𝔪 ^ (a * d) : ℕ) : ℝ)) : ℂ))⁻¹ = (((Ideal.absNorm 𝔪 : ℂ)) ^ (a * d))⁻¹ := by
    have h1 : (((Ideal.absNorm 𝔪 ^ (a * d) : ℕ) : ℝ)) = (Ideal.absNorm 𝔪 : ℝ) ^ (a * d) := by push_cast; rfl
    rw [h1, ← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    push_cast; rfl
  have hχq : ∀ (i : R) q, χ i q = Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (x i))
      ((Quotient.out q : La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) : VC D a d) := by
    intro i q
    rw [← hχ i, QuotientAddGroup.out_eq']
  simp only [hχq, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun i _ => ?_
  rw [← hs]; ring

end GlobalTheory.FunObj.StdDatum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameWeilDeligneUnderIdentityRelation
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.TameTransport in
theorem GlobalTheory.LocLanglands.isTameWD_of_wdRel_refl : ∀ (E E' Ω : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω] [Algebra E Ω] [Algebra E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (w' : HeightOneSpectrum (𝓞 E')) (h : IsPlaceOver A w) (h' : IsPlaceOver A w') (j : E →+* E') (i : w.adicCompletion E ≃+* w'.adicCompletion E'), GlobalTheory.LocLanglands.PlaceIso A w A w' (RingEquiv.refl Ω) j i → ∀ (y : WD h) (y' : WD h'), WDRel (RingEquiv.refl Ω) y y' → IsTameWD y → IsTameWD y' := by
  intro E E' Ω _ _ _ _ _ _ _ _ _ A w w' h h' j i hP y y' hrel hy
  obtain ⟨n, b, b', hb, hb', -, hρ⟩ := hrel
  obtain ⟨m, a, ha, hwild⟩ := hy
  obtain ⟨e, he, -⟩ := GlobalTheory.WeilDeligne.WD.mk_eq_mk.mp (ha.trans hb.symm)
  obtain ⟨c, hc, -⟩ := GlobalTheory.T.place_over_transport_ring_iso E Ω A w h E' Ω A w' h' (RingEquiv.refl Ω) j i hP
  refine ⟨n, b', hb', fun σ' hσ' => ?_⟩
  have hr : WeilRel (RingEquiv.refl Ω) (c.symm σ') σ' := (hc (c.symm σ') σ').mpr (by simp)
  have hσ : Formalism.MainNotions.BlochKatoReduction.IsWild A ((c.symm σ' : Weil h) : G E Ω) :=
    isWild_of_rel (φ := RingEquiv.refl Ω) (fun _ => Iff.rfl) (fun z => ?_) hσ'
  · rw [← hρ _ σ' hr]
    refine LinearMap.ext fun v => ?_
    obtain ⟨u, rfl⟩ := e.surjective v
    rw [← he, hwild _ hσ]
    rfl
  · have := hr z
    simpa using this.symm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftEqIntegralRouteKernelFubiniStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLift_eq_integral_routeKernel_fubini : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (hWC : GlobalTheory.SquareSt.WeilConvergence) (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree) (hP : GlobalTheory.Published.CuspDecayBound) {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (hT : SquareTriple W t i j)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ')
    (F : Fn G (.grid i (j + 1))) (hF : IsAutFunSm W.θ _ F) (hFc : IsCuspFun _ F) (hFl : G.IsListed W.θ _ F) (hA : TotConv W M _ Θ F) (g₁ : GA D (G.V (.grid (i + 1) j))),
    (∀ᵐ g ∂(M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1))),
      IntegrableOn (kerBig W Θ g g₁) (M.fd (.grid (i + 1) (j + 1))) (M.ν (.grid (i + 1) (j + 1)))) ∧
    liftT W M (routeBig t i j) Θ F g₁ = ∫ g in M.fd (.grid i (j + 1)), F g * ∫ u in M.fd (.grid (i + 1) (j + 1)),
      kerBig W Θ g g₁ u ∂M.ν (.grid (i + 1) (j + 1)) ∂M.ν (.grid i (j + 1)) := by
  first | exact @GlobalTheory.BigRoute.lift_eq_integral_kerBig | exact GlobalTheory.BigRoute.lift_eq_integral_kerBig | (intros; apply GlobalTheory.BigRoute.lift_eq_integral_kerBig <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftRowFiresOfWeakCharacterisation
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem thetaLiftRow_fires_of_weakCharacterisation : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → R.toRealDat.ExAt → A3.A.v0 = InfinitePlace.mk D.what₂.embLL → ∀ (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : RecTie.TopMultH R.toRealDat) (hinj : ∀ i t, Function.Injective (R.toRealDat.extV i t)) (IL : RecTie.LiftIds (RecTie.toLiftReal R.toRealDat F.lv2 tupT hm hTop hinj)), RecTie.ThetaFireRow (RecTie.toLiftReal R.toRealDat F.lv2 tupT hm hTop hinj) IL := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hC e hv tupT hm hTop hinj IL
  exact GlobalTheory.T.thetaFiringRow_at_concreteLifts R.toRealDat F.lv2 tupT hm hTop hinj hC.base e hv IL

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeriesFactorizableRestriction
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Classical

noncomputable section
namespace GlobalTheory.VacFactor

theorem pure_update_smul {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f : SInf F κ)
    (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) (w : Pl F) (r : ℂ) (h : (κ → Fv F w) → ℂ)
    (hφ : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers F} 1) :
    pure f (Function.update φ w (r • h)) = pure (r • f) (Function.update φ w h) := by
  funext x
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
  rw [GlobalTheory.PureFactor.finprod_update φ w (r • h) hφ x, GlobalTheory.PureFactor.finprod_update φ w h hφ x]
  simp only [SchwartzMap.smul_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem tens_smul {F : Type} [Field F] [NumberField F] {R κ : Type} (ev : AF F → R) (c : ℂ) (g : (κ → R) → ℂ)
    (r : (κ → AF F) → ℂ) : tens ev (c • g) r = c • tens ev g r := by
  funext x
  simp [tens, mul_assoc]

theorem std_of_off {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (vac φ : ∀ v : Pl F, (κ → Fv F v) → ℂ)
    (hvac : ∀ᶠ v in Filter.cofinite, vac v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers F} 1)
    (U : Finset (Pl F)) (h : ∀ v, v ∉ U → φ v = vac v) :
    ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers F} 1 := by
  filter_upwards [hvac, U.finite_toSet.compl_mem_cofinite] with v h1 h2
  rw [h v h2, h1]

theorem factor : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (S : Finset (Pl F)) (f : SInf F (Fin a' × Fin (a + a'))) (φ : ∀ w : Pl F, (Fin a' × Fin (a + a') → Fv F w) → ℂ),
    (∀ w, φ w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) → (∀ w, w ∉ S → φ w = G.M'.vac w) →
    ∀ Ψ ∈ schA F (Fin a' × Fin (a + a')),
    (∀ w, w ∉ S → ∀ γ ∈ latAtV G.V' G.W w, ∀ c : ℂ,
      G.M'.co.rho B.ψ γ (pure f φ) = c • pure f φ → G.M'.co.rho B.ψ γ Ψ = c • Ψ) →
    ∃ (m : ℕ) (f' : Fin m → SInf F (Fin a' × Fin (a + a'))) (φ' : Fin m → ∀ w : Pl F, (Fin a' × Fin (a + a') → Fv F w) → ℂ),
      (∀ i w, φ' i w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) ∧ (∀ i w, w ∉ S → φ' i w = G.M'.vac w) ∧
      Ψ = ∑ i, pure (f' i) (φ' i) := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT S f φ hφSB hφvac Ψ hΨ hyp
  have hvstd := hT.geo.hM'.std
  have hvSB : ∀ v, G.M'.vac v ∈ SB (Fin a' × Fin (a + a') → Fv F v) := fun v => (hT.geo.hM'.vac v).1
  have hyp' : ∀ w, w ∉ S → ∀ γ ∈ latAtV G.V' G.W w, ∀ c : ℂ,
      Acts (evFin F w) (G.M'.co.rho B.ψ γ) (G.M'.vac w) (c • G.M'.vac w) → G.M'.co.rho B.ψ γ Ψ = c • Ψ := by
    intro w hw γ hγ c hc
    have hstd := std_of_off G.M'.vac φ hvstd S hφvac
    obtain ⟨r, hr1, hr2⟩ := GlobalTheory.PureFactor.exists_rest_factor w f φ hstd
    have e : pure f φ = tens (evFin F w) (G.M'.vac w) r := by
      rw [hr2, ← hφvac w hw, Function.update_eq_self]
    refine hyp w hw γ hγ c ?_
    have hR : Rest (evFin F w) (G.M'.vac w) r := ⟨hr1, e ▸ GlobalTheory.TensUniq.pure_mem_schA f φ hφSB hstd⟩
    rw [e, hc r hR, tens_smul]
  obtain ⟨T, m, f₀, φ₀, hSB₀, hstd₀, hsum₀⟩ := GlobalTheory.T.adelic_schwartz_finite_pure_tensors F _ Ψ hΨ
  have hfin : {v | ¬ G.M'.vac v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers F} 1}.Finite :=
    Filter.eventually_cofinite.1 hvstd
  have key : ∀ U : Finset (Pl F), ∀ (f : Fin m → SInf F (Fin a' × Fin (a + a')))
      (φ : Fin m → ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ),
      (∀ i v, φ i v ∈ SB (Fin a' × Fin (a + a') → Fv F v)) → (∀ i v, v ∉ S → v ∉ U → φ i v = G.M'.vac v) →
      Ψ = ∑ i, pure (f i) (φ i) →
      ∃ (f' : Fin m → SInf F (Fin a' × Fin (a + a'))) (φ' : Fin m → ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ),
        (∀ i v, φ' i v ∈ SB (Fin a' × Fin (a + a') → Fv F v)) ∧ (∀ i v, v ∉ S → φ' i v = G.M'.vac v) ∧
        Ψ = ∑ i, pure (f' i) (φ' i) := by
    intro U
    induction U using Finset.induction_on with
    | empty => exact fun f φ h1 h2 h3 => ⟨f, φ, h1, fun i v hv => h2 i v hv (Finset.notMem_empty v), h3⟩
    | insert w U hwU ih =>
      intro f φ h1 h2 h3
      by_cases hwS : w ∈ S
      · refine ih f φ h1 (fun i v hv hvU => h2 i v hv ?_) h3
        rw [Finset.mem_insert]
        rintro (rfl | h)
        exacts [hv hwS, hvU h]
      · have hstd : ∀ i, ∀ᶠ v in Filter.cofinite,
            φ i v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers F} 1 := fun i =>
          std_of_off G.M'.vac (φ i) hvstd (S ∪ insert w U) fun v hv =>
            h2 i v (fun h => hv (Finset.mem_union_left _ h)) (fun h => hv (Finset.mem_union_right _ h))
        obtain ⟨g, hgSB, hgE, hgsum⟩ := GlobalTheory.T.triple_lattice_invariant_schwartz_global hP F E σ B a a' G X om om' hT w Ψ hΨ (hyp' w hwS) m f φ h1 hstd h3
        choose r hr using fun i => GlobalTheory.T.triple_lattice_invariant_schwartz_local hP F E σ B a a' G X om om' hT w (g i) (hgSB i) (hgE i)
        refine ih (fun i => r i • f i) (fun i => Function.update (φ i) w (G.M'.vac w)) (fun i v => ?_)
          (fun i v hv hvU => ?_) ?_
        · by_cases hvw : v = w
          · subst hvw
            rw [Function.update_self]
            exact hvSB _
          · rw [Function.update_of_ne hvw]
            exact h1 i v
        · by_cases hvw : v = w
          · subst hvw
            rw [Function.update_self]
          · rw [Function.update_of_ne hvw]
            refine h2 i v hv ?_
            rw [Finset.mem_insert]
            rintro (h | h)
            exacts [hvw h, hvU h]
        · rw [hgsum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hr i, pure_update_smul _ _ _ _ _ (hstd i)]
  obtain ⟨f', φ', h1, h2, h3⟩ := key (T ∪ hfin.toFinset) f₀ φ₀ hSB₀ (fun i v _ hv => by
    rw [hstd₀ i v (fun h => hv (Finset.mem_union_left _ h))]
    by_contra hne
    exact hv (Finset.mem_union_right _ (hfin.mem_toFinset.2 fun h => hne h.symm))) hsum₀
  exact ⟨m, f', φ', h1, h2, h3⟩

end GlobalTheory.VacFactor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationUnitaryEquivStatement
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_representation_unitary_equiv : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ → M.IsWeil B.ψ χX χW om →
    ∀ g ∈ UAt σ X (evI F), ∀ h ∈ UAt σ W (evI F), ∃ T : SInf F (Fin n × Fin d) ≃ₗ[ℂ] SInf F (Fin n × Fin d),
      (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (g, h)) f (T f)) ∧
      ∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (g⁻¹, h⁻¹)) f (T.symm f) := by
  first | exact @GlobalTheory.RealConjFac.main | exact GlobalTheory.RealConjFac.main | (intros; apply GlobalTheory.RealConjFac.main <;> assumption)
end

