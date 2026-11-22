import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1913
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1904
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1129
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1406
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1809
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1793
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1892
import ReciprocityTheory.GeneralLinearIntegers.AlgebraMapIntMemOint
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1883
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1906
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledCoordsThetaTransformProductEqTensorConj
section
namespace DoublingThetaSums
section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.DblTheta

section Gen

variable {R : Type} [CommRing R] [Invertible (2 : R)]

theorem schr_boxFun_elim (ψ : AddChar R ℂ) {κ κ' : Type} [Fintype κ] [Fintype κ'] (x₁ y₁ : κ → R) (x₂ y₂ : κ' → R)
    (φ₁ : (κ → R) → ℂ) (φ₂ : (κ' → R) → ℂ) :
    GlobalTheory.WeilM.schr ψ (Sum.elim x₁ x₂, Sum.elim y₁ y₂) (GlobalTheory.WeilM.boxFun φ₁ φ₂) =
      GlobalTheory.WeilM.boxFun (GlobalTheory.WeilM.schr ψ (x₁, y₁) φ₁) (GlobalTheory.WeilM.schr ψ (x₂, y₂) φ₂) := by
  funext z
  have e₁ : (z + Sum.elim x₁ x₂) ∘ Sum.inl = z ∘ Sum.inl + x₁ := rfl
  have e₂ : (z + Sum.elim x₁ x₂) ∘ Sum.inr = z ∘ Sum.inr + x₂ := rfl
  have e₃ : z ⬝ᵥ Sum.elim y₁ y₂ + ⅟(2 : R) * (Sum.elim x₁ x₂ ⬝ᵥ Sum.elim y₁ y₂) =
      ((z ∘ Sum.inl) ⬝ᵥ y₁ + ⅟(2 : R) * (x₁ ⬝ᵥ y₁)) + ((z ∘ Sum.inr) ⬝ᵥ y₂ + ⅟(2 : R) * (x₂ ⬝ᵥ y₂)) := by
    simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Function.comp_apply]
    ring
  simp only [GlobalTheory.WeilM.schr, GlobalTheory.WeilM.boxFun, e₁, e₂, e₃]
  rw [AddChar.map_add_eq_mul]
  ring

end Gen

section Sums

variable (F : Type) [Field F] [NumberField F]

theorem thetaSum_boxFun {κ κ' : Type} [Fintype κ] [Fintype κ'] {A : (κ → AdeleRing (𝓞 F) F) → ℂ}
    {B : (κ' → AdeleRing (𝓞 F) F) → ℂ} (hA : A ∈ GlobalTheory.WeilM.schA F κ) (hB : B ∈ GlobalTheory.WeilM.schA F κ') :
    GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.boxFun A B) = GlobalTheory.WeilM.thetaSum F A * GlobalTheory.WeilM.thetaSum F B := by
  unfold GlobalTheory.WeilM.thetaSum
  rw [tsum_mul_tsum_of_summable_norm (GlobalTheory.WeilM.summable_norm_of_mem_schA F hA)
    (GlobalTheory.WeilM.summable_norm_of_mem_schA F hB), ← (Equiv.sumArrowEquivProdArrow κ κ' F).tsum_eq]
  exact tsum_congr fun ξ => rfl

theorem thetaSum_schr_neg [Invertible (2 : AdeleRing (𝓞 F) F)] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (hu : ∀ a, ‖ψ a‖ = 1) {κ : Type} [Fintype κ] (x y : κ → AdeleRing (𝓞 F) F)
    (φ : (κ → AdeleRing (𝓞 F) F) → ℂ) :
    GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (x, -y) φ) =
      starRingEnd ℂ (GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (-x, -y) (fun u => starRingEnd ℂ (φ (-u))))) := by
  have hc : ∀ t, starRingEnd ℂ (ψ t) = ψ (-t) := fun t => by
    rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hu t)]
  have key : ∀ ξ : κ → F,
      GlobalTheory.WeilM.schr ψ (x, -y) φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) ((-ξ) i)) =
        starRingEnd ℂ (GlobalTheory.WeilM.schr ψ (-x, -y) (fun u => starRingEnd ℂ (φ (-u)))
          (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))) := by
    intro ξ
    have ha : (fun i => algebraMap F (AdeleRing (𝓞 F) F) ((-ξ) i)) =
        -(fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) := by
      funext i; simp
    rw [ha]
    generalize (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) = a
    simp only [GlobalTheory.WeilM.schr, map_mul, Complex.conj_conj, hc]
    have h1 : -a + x = -(a + -x) := by abel
    have h2 : -a ⬝ᵥ -y + ⅟(2 : AdeleRing (𝓞 F) F) * (x ⬝ᵥ -y) =
        -(a ⬝ᵥ -y + ⅟(2 : AdeleRing (𝓞 F) F) * (-x ⬝ᵥ -y)) := by
      simp only [neg_dotProduct, dotProduct_neg]
      ring
    rw [h1, h2]
  unfold GlobalTheory.WeilM.thetaSum
  calc _ = ∑' ξ : κ → F, GlobalTheory.WeilM.schr ψ (x, -y) φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) ((-ξ) i)) :=
        ((Equiv.neg (κ → F)).tsum_eq
          (fun ξ : κ → F => GlobalTheory.WeilM.schr ψ (x, -y) φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)))).symm
    _ = _ := tsum_congr key
    _ = _ := (Complex.conj_tsum _).symm

end Sums

theorem thetaTr_ddr_boxFun : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
      (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (κ : Type) [Fintype κ]
      (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
      ∀ φ₁ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ φ₂ ∈ GlobalTheory.WeilM.schA D.host.F κ,
        GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.DblSchr.ddr co) ψ (GlobalTheory.WeilM.boxFun φ₁ φ₂) =
          GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta S T (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ φ₁)
            (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ (fun x => starRingEnd ℂ (φ₂ (-x)))) := by
  intro D ψ hψ S T JA JB ξ κ _ co φ₁ h₁ φ₂ h₂
  funext x
  have he : (GlobalTheory.DblSchr.ddr co).e x =
      (Sum.elim (co.e (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resL S T x)).1 (co.e (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resR S T x)).1,
        Sum.elim (co.e (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resL S T x)).2 (-(co.e (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resR S T x)).2)) := rfl
  have hn : co.e (-GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resR S T x) =
      (-(co.e (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resR S T x)).1, -(co.e (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resR S T x)).2) := by
    rw [map_neg]; rfl
  have hs : ∀ (w : (κ → AF D.host.F) × (κ → AF D.host.F)) (φ : (κ → AF D.host.F) → ℂ),
      φ ∈ GlobalTheory.WeilM.schA D.host.F κ → GlobalTheory.WeilM.schr ψ w φ ∈ GlobalTheory.WeilM.schA D.host.F κ :=
    fun w φ hφ => GlobalTheory.SchrSchA.schr_mem_schA_of_isStdChar D ψ hψ κ w φ hφ
  simp only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta]
  rw [he, hn, schr_boxFun_elim, thetaSum_boxFun _ (hs _ _ h₁) (hs _ _ h₂),
    thetaSum_schr_neg _ ψ hψ.1.2.1]

end GlobalTheory.CompanionTheory.DblTheta

end

end

end DoublingThetaSums
section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.Adopt.doubledCoordsThetaTransform_product_eq_tensor_conj : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
      (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (κ : Type) [Fintype κ]
      (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
      ∀ φ₁ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ φ₂ ∈ GlobalTheory.WeilM.schA D.host.F κ,
        GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.DblSchr.ddr co) ψ (GlobalTheory.WeilM.boxFun φ₁ φ₂) =
          GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta S T (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ φ₁)
            (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ (fun x => starRingEnd ℂ (φ₂ (-x)))) := by
  first | exact @DoublingThetaSums.GlobalTheory.CompanionTheory.DblTheta.thetaTr_ddr_boxFun | exact DoublingThetaSums.GlobalTheory.CompanionTheory.DblTheta.thetaTr_ddr_boxFun | (intros; apply DoublingThetaSums.GlobalTheory.CompanionTheory.DblTheta.thetaTr_ddr_boxFun <;> assumption)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumHeisenbergEigenDoubledLattice
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.DblVacEigen

section Alg

variable {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

omit [DecidableEq α] in

theorem hTens_dbl (JA : Matrix α α E) (JB : Matrix β β E) (x₁ x₂ y₁ y₂ : Matrix α β E) :
    hTens c JA (dbl JB) (Matrix.fromCols x₁ x₂) (Matrix.fromCols y₁ y₂) = hTens c JA JB x₁ y₁ - hTens c JA JB x₂ y₂ := by
  simp only [hTens, dbl, Fintype.sum_sum_type, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Matrix.zero_apply, Matrix.neg_apply, mul_zero, zero_mul, add_zero, zero_add, mul_neg, neg_mul,
    Finset.sum_neg_distrib, Finset.sum_add_distrib, sub_eq_add_neg, Finset.sum_const_zero]

omit [DecidableEq α] [DecidableEq β] in

theorem hTens_transpose (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix β α E) :
    hTens c JA JB xᵀ yᵀ = hTens c JB JA x y := by
  unfold hTens
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.transpose_apply]
  ring

end Alg

end GlobalTheory.DblVacEigen

namespace GlobalTheory.DblVacEigen

variable {F : Type} [Field F] [NumberField F]

theorem dot_congr_at {κ : Type} [Fintype κ] (v : Pl F) {y : κ → AF F} (hy : At (evFin F v) y) {z z' : κ → AF F}
    (h : ∀ i, evFin F v (z i) = evFin F v (z' i)) : z ⬝ᵥ y = z' ⬝ᵥ y := by
  unfold dotProduct
  refine Finset.sum_congr rfl fun i _ => ?_
  have e := congrFun (hy (z i - z' i) (by rw [map_sub, h i, sub_self])) i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e
  rw [sub_mul] at e
  exact sub_eq_zero.mp e

theorem eigen_pointwise {κ : Type} [Fintype κ] (v : Pl F) (ψ : AddChar (AF F) ℂ) {φ : (κ → Fv F v) → ℂ}
    (hφ : φ ∈ SB (κ → Fv F v)) (p : (κ → AF F) × (κ → AF F)) (hp1 : At (evFin F v) p.1) (hp2 : At (evFin F v) p.2)
    (c : ℂ) (h : Acts (evFin F v) (schr ψ p) φ (c • φ)) (z : κ → AF F) :
    ψ (z ⬝ᵥ p.2 + ⅟(2 : AF F) * (p.1 ⬝ᵥ p.2)) * φ (fun i => evFin F v ((z + p.1) i)) =
      c * φ (fun i => evFin F v (z i)) := by
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest κ v
  have hr := hR φ hφ
  let Δ : κ → AF F := fun i => GlobalTheory.LatVac.liftV v (evFin F v (z i))
  have hΔ : At (evFin F v) Δ := fun u hu => funext fun i => GlobalTheory.LatVac.at_liftV v _ u hu
  have hevΔ : ∀ i, evFin F v (Δ i) = evFin F v (z i) := fun i => GlobalTheory.LatVac.evFin_liftV v _
  have e := congrFun (h R hr) Δ
  have hR2 : R Δ = R 0 := by simpa using hr.1 0 Δ hΔ
  have hR1 : R (Δ + p.1) = R 0 := by rw [hr.1 Δ p.1 hp1, hR2]
  simp only [schr, tens, Pi.smul_apply, smul_eq_mul] at e
  rw [hR1, hR2, dot_congr_at v hp2 hevΔ] at e
  have hev : (fun i => evFin F v ((Δ + p.1) i)) = fun i => evFin F v ((z + p.1) i) := by
    funext i; simp only [Pi.add_apply, map_add, hevΔ]
  have hev' : (fun i => evFin F v (Δ i)) = fun i => evFin F v (z i) := funext hevΔ
  rw [hev, hev'] at e
  exact mul_right_cancel₀ hR0 (by linear_combination e)

theorem acts_box {κ κ' : Type} [Fintype κ] [Fintype κ'] (v : Pl F) (ψ : AddChar (AF F) ℂ)
    {φ₁ : (κ → Fv F v) → ℂ} {φ₂ : (κ' → Fv F v) → ℂ} (X₁ Y₁ : κ → AF F)
    (X₂ Y₂ : κ' → AF F) (h11 : At (evFin F v) X₁) (h21 : At (evFin F v) X₂) (c₁ c₂ : ℂ)
    (h₁ : ∀ z, ψ (z ⬝ᵥ Y₁ + ⅟(2 : AF F) * (X₁ ⬝ᵥ Y₁)) * φ₁ (fun i => evFin F v ((z + X₁) i)) =
      c₁ * φ₁ (fun i => evFin F v (z i)))
    (h₂ : ∀ z, ψ (z ⬝ᵥ Y₂ + ⅟(2 : AF F) * (X₂ ⬝ᵥ Y₂)) * φ₂ (fun i => evFin F v ((z + X₂) i)) =
      c₂ * φ₂ (fun i => evFin F v (z i))) :
    Acts (evFin F v) (schr ψ (Sum.elim X₁ X₂, Sum.elim Y₁ Y₂)) (boxFun φ₁ φ₂)
      ((c₁ * c₂) • boxFun φ₁ φ₂) := by
  intro r hr
  have hX : At (evFin F v) (Sum.elim X₁ X₂ : κ ⊕ κ' → AF F) := by
    intro u hu; funext i
    cases i with
    | inl i => exact congrFun (h11 u hu) i
    | inr i => exact congrFun (h21 u hu) i
  funext x
  have hd1 : x ⬝ᵥ Sum.elim Y₁ Y₂ = (x ∘ Sum.inl) ⬝ᵥ Y₁ + (x ∘ Sum.inr) ⬝ᵥ Y₂ := by
    simp [dotProduct, Fintype.sum_sum_type]
  have hd2 : Sum.elim X₁ X₂ ⬝ᵥ Sum.elim Y₁ Y₂ = X₁ ⬝ᵥ Y₁ + X₂ ⬝ᵥ Y₂ :=
    by simp [dotProduct, Fintype.sum_sum_type]
  simp only [schr, tens, Pi.smul_apply, smul_eq_mul]
  rw [hr.1 x _ hX, hd1, hd2,
    show (x ∘ Sum.inl) ⬝ᵥ Y₁ + (x ∘ Sum.inr) ⬝ᵥ Y₂ + ⅟(2 : AF F) * (X₁ ⬝ᵥ Y₁ + X₂ ⬝ᵥ Y₂) =
      ((x ∘ Sum.inl) ⬝ᵥ Y₁ + ⅟(2 : AF F) * (X₁ ⬝ᵥ Y₁)) + ((x ∘ Sum.inr) ⬝ᵥ Y₂ + ⅟(2 : AF F) * (X₂ ⬝ᵥ Y₂))
      by ring, AddChar.map_add_eq_mul]
  have e1 := h₁ (x ∘ Sum.inl)
  have e2 := h₂ (x ∘ Sum.inr)
  simp only [boxFun, Function.comp_def, Pi.add_apply, Sum.elim_inl, Sum.elim_inr] at e1 e2 ⊢
  rw [show ∀ a e b f s : ℂ, a * e * ((b * f) * s) = (a * b) * (e * f) * s from fun _ _ _ _ _ => by ring, e1, e2]
  ring

end GlobalTheory.DblVacEigen

namespace GlobalTheory.DblVacEigen

theorem doubled_vac_eigen : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ (d' : Darboux (symp (cA σ) (-1 : AE F E) (incM F G.W.J) (incM F G.V.J)) (Fin a × Fin (a + a'))),
    (∀ x : Matrix (Fin a) (Fin (a + a')) (AE F E), d'.e xᵀ = G.M.co.e x) →
    ∀ (dd : Darboux (symp (cA σ) (-1 : AE F E) (incM F G.W.J) (dbl (incM F G.V.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')))),
    IsDblCoord (cA σ) (-1 : AE F E) (incM F G.W.J) (incM F G.V.J) d' dd →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) (G.M.vac v)
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (incM F G.W.J) γ γ) • G.M.vac v)) →
    (∀ w₁ ∈ latAtV G.V G.W v, ∀ w₂ ∈ latAtV G.V G.W v,
      Acts (evFin F v) (dd.rho B.ψ (Matrix.fromCols w₁ᵀ w₂ᵀ)) (boxFun (G.M.vac v) (fun x => star (G.M.vac v x)))
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.W.J) (dbl (incM F G.V.J))
          (Matrix.fromCols w₁ᵀ w₂ᵀ) (Matrix.fromCols w₁ᵀ w₂ᵀ)) • (boxFun (G.M.vac v) (fun x => star (G.M.vac v x))))) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w _ _ d' hd' dd hdd θ _ hvac w₁ hw₁ w₂ hw₂
  have hSB := (hT.geo.hM.vac v).1
  have hψ : ∀ t, ‖B.ψ t‖ = 1 := GlobalTheory.StdCharWeilDatum.norm_psi hT.base.std
  have hstar : ∀ t, star (B.ψ t) = B.ψ (-t) := by
    intro t
    rw [AddChar.map_neg_eq_inv, Complex.inv_def, Complex.normSq_eq_norm_sq, hψ t]
    simp
  have hAt : ∀ γ ∈ latAtV G.V G.W v, At (evFin F v) γ := (GlobalTheory.LatVac.latAtV_at_stable G.V G.W v).1
  have hco : ∀ γ ∈ latAtV G.V G.W v, At (evFin F v) (G.M.co.e γ).1 ∧ At (evFin F v) (G.M.co.e γ).2 := by
    intro γ hγ
    have e : ∀ u, evFin F v u = 0 → u • G.M.co.e γ = 0 := fun u hu => by
      rw [← map_smul, hAt γ hγ u hu, map_zero]
    exact ⟨fun u hu => congrArg Prod.fst (e u hu), fun u hu => congrArg Prod.snd (e u hu)⟩
  have h1 := eigen_pointwise v B.ψ hSB (G.M.co.e w₁) (hco w₁ hw₁).1 (hco w₁ hw₁).2 _ (hvac w₁ hw₁)
  have h2 := eigen_pointwise v B.ψ hSB (G.M.co.e w₂) (hco w₂ hw₂).1 (hco w₂ hw₂).2 _ (hvac w₂ hw₂)
  have h2' : ∀ z, B.ψ (z ⬝ᵥ (-(G.M.co.e w₂).2) + ⅟(2 : AF F) * ((G.M.co.e w₂).1 ⬝ᵥ (-(G.M.co.e w₂).2))) *
      (fun x => star (G.M.vac v x)) (fun i => evFin F v ((z + (G.M.co.e w₂).1) i)) =
      star (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (incM F G.W.J) w₂ w₂)) * (fun x => star (G.M.vac v x)) (fun i => evFin F v (z i)) := by
    intro z
    have e := congrArg star (h2 z)
    simp only [star_mul, hstar] at e
    rw [hstar, show z ⬝ᵥ (-(G.M.co.e w₂).2) + ⅟(2 : AF F) * ((G.M.co.e w₂).1 ⬝ᵥ (-(G.M.co.e w₂).2)) =
      -(z ⬝ᵥ (G.M.co.e w₂).2 + ⅟(2 : AF F) * ((G.M.co.e w₂).1 ⬝ᵥ (G.M.co.e w₂).2)) by
        rw [dotProduct_neg, dotProduct_neg]; ring]
    linear_combination e
  have hbox := acts_box v B.ψ (φ₁ := G.M.vac v) (φ₂ := fun x => star (G.M.vac v x)) (G.M.co.e w₁).1 (G.M.co.e w₁).2 (G.M.co.e w₂).1 (-(G.M.co.e w₂).2)
    (hco w₁ hw₁).1 (hco w₂ hw₂).1 _ _ h1 h2'
  have hrho : dd.rho B.ψ (Matrix.fromCols w₁ᵀ w₂ᵀ) = schr B.ψ (Sum.elim (G.M.co.e w₁).1 (G.M.co.e w₂).1,
      Sum.elim (G.M.co.e w₁).2 (-(G.M.co.e w₂).2)) := by
    rw [Darboux.rho, hdd, hd', hd']
  have hS : symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.W.J) (dbl (incM F G.V.J))
      (Matrix.fromCols w₁ᵀ w₂ᵀ) (Matrix.fromCols w₁ᵀ w₂ᵀ) = symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (incM F G.W.J) w₁ w₁ - symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (incM F G.W.J) w₂ w₂ := by
    unfold symp
    rw [hTens_dbl, hTens_transpose, hTens_transpose, mul_sub, map_sub]
  have hc : B.ψ (⅟(2 : AF F) * (symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (incM F G.W.J) w₁ w₁ - symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (incM F G.W.J) w₂ w₂)) = B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (incM F G.W.J) w₁ w₁) * star (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (incM F G.W.J) w₂ w₂)) := by
    rw [hstar, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  rw [hrho, hS, hc]
  exact hbox

end GlobalTheory.DblVacEigen

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumTwistedVacuumConditionDoubledLattic
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.DblVacLine

theorem norm_psiAt_le {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) (v : Pl F)
    (y : Fv F v) : ‖GlobalTheory.LatVac.psiAt ψ v y‖ ≤ 1 := by
  have hc := GlobalTheory.SchrSB.continuous_psiAt ψ hψ v
  have hK := (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v).image
    (f := fun t : Fv F v => ‖GlobalTheory.LatVac.psiAt ψ v (y * t)‖) ((hc.comp (continuous_const.mul continuous_id)).norm)
  obtain ⟨C, hC⟩ := hK.bddAbove
  by_contra h
  push_neg at h
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C h
  have hle : ‖GlobalTheory.LatVac.psiAt ψ v y‖ ^ n ≤ C := by
    refine hC ⟨(n : Fv F v), natCast_mem _ n, ?_⟩
    show ‖GlobalTheory.LatVac.psiAt ψ v (y * (n : Fv F v))‖ = _
    rw [mul_comm, ← nsmul_eq_mul, AddChar.map_nsmul_eq_pow, norm_pow]
  linarith

theorem norm_psiAt {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) (v : Pl F)
    (y : Fv F v) : ‖GlobalTheory.LatVac.psiAt ψ v y‖ = 1 := by
  have h1 := norm_psiAt_le ψ hψ v y
  have h2 := norm_psiAt_le ψ hψ v (-y)
  have h3 : ‖GlobalTheory.LatVac.psiAt ψ v y‖ * ‖GlobalTheory.LatVac.psiAt ψ v (-y)‖ = 1 := by
    rw [← norm_mul, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one, norm_one]
  nlinarith [norm_nonneg (GlobalTheory.LatVac.psiAt ψ v y), norm_nonneg (GlobalTheory.LatVac.psiAt ψ v (-y))]

theorem star_psiAt {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) (v : Pl F)
    (y : Fv F v) : star (GlobalTheory.LatVac.psiAt ψ v y) = GlobalTheory.LatVac.psiAt ψ v (-y) := by
  rw [AddChar.map_neg_eq_inv]
  refine eq_inv_of_mul_eq_one_left ?_
  rw [Complex.star_def, Complex.conj_mul', norm_psiAt ψ hψ v y]
  simp

theorem symp_dbl_fromCols {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E)
    (w₁ w₂ : Matrix α β E) :
    symp (R := R) c ξ JA (dbl JB) (Matrix.fromCols w₁ w₂) (Matrix.fromCols w₁ w₂) =
      symp (R := R) c ξ JA JB w₁ w₁ - symp (R := R) c ξ JA JB w₂ w₂ := by
  unfold symp
  rw [← map_sub, ← mul_sub]
  congr 2
  unfold hTens
  simp only [dbl, Fintype.sum_sum_type, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Matrix.zero_apply, Matrix.neg_apply, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add, mul_neg,
    neg_mul, Finset.sum_neg_distrib]
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, sub_eq_add_neg]

theorem at_symp_self {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n d : ℕ} (JA : Matrix (Fin n) (Fin n) (AE F E)) (JB : Matrix (Fin d) (Fin d) (AE F E))
    (ξ : AE F E) (v : Pl F) {w : Matrix (Fin n) (Fin d) (AE F E)} (hw : At (evFin F v) w) :
    At (evFin F v) (symp (R := AF F) (cA σ) ξ JA JB w w) := by
  intro u hu
  have h1 := GlobalTheory.LatVac.symp_smul_smul σ JA JB ξ u 1 w w
  have h0 := GlobalTheory.LatVac.symp_smul_smul σ JA JB ξ 0 1 w w
  rw [hw u hu, mul_one] at h1
  rw [zero_smul, zero_mul, zero_mul] at h0
  rw [smul_eq_mul, ← h1, h0]

end GlobalTheory.DblVacLine

namespace GlobalTheory.DblVacLine

theorem dbl_vac_acts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (dd : Darboux (symp (cA σ) (-1) (incM F G.V'.J) (dbl (incM F G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a'))), IsDblCoord (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) G.M'.co dd →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    (∀ γ ∈ latAtV G.V' G.W v, Acts (evFin F v) (G.M'.co.rho B.ψ γ) (G.M'.vac v)
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) γ γ) • (G.M'.vac v))) →
    (∀ w₁ ∈ latAtV G.V' G.W v, ∀ w₂ ∈ latAtV G.V' G.W v,
      Acts (evFin F v) (dd.rho B.ψ (Matrix.fromCols w₁ w₂)) (boxFun (G.M'.vac v) (fun x => star (G.M'.vac v x)))
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (dbl (incM F G.W.J))
          (Matrix.fromCols w₁ w₂) (Matrix.fromCols w₁ w₂)) • (boxFun (G.M'.vac v) (fun x => star (G.M'.vac v x))))) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v dd hdd θ hθ hvac w₁ hw₁ w₂ hw₂
  have hψc : Continuous B.ψ := hT.base.std.1
  have hSB : G.M'.vac v ∈ SB _ := (hT.geo.hM'.vac v).1
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest (F := F) (Fin a' × Fin (a + a')) v
  have hat := (GlobalTheory.LatVac.latAtV_at_stable G.V' G.W v).1
  have hloc : ∀ w ∈ latAtV G.V' G.W v, ∀ ξ, GlobalTheory.LatVac.psiAt B.ψ v (ξ ⬝ᵥ (GlobalTheory.LatVac.locCo G.M'.co v w).2 +
        (2 : Fv F v)⁻¹ * ((GlobalTheory.LatVac.locCo G.M'.co v w).1 ⬝ᵥ (GlobalTheory.LatVac.locCo G.M'.co v w).2)) *
      G.M'.vac v (ξ + (GlobalTheory.LatVac.locCo G.M'.co v w).1) =
        B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) w w) *
          G.M'.vac v ξ := fun w hw ξ =>
    GlobalTheory.LatVac.heis_at_local_identity v G.M'.co B.ψ w _ _ (hat w hw) (hvac w hw) R (hR _ hSB) 0 hR0 ξ
  have hatd : At (evFin F v) (Matrix.fromCols w₁ w₂) := by
    intro u hu
    have h1 := hat w₁ hw₁ u hu
    have h2 := hat w₂ hw₂ u hu
    ext i j
    rcases j with j | j
    · simpa using congrFun (congrFun h1 i) j
    · simpa using congrFun (congrFun h2 i) j
  have key := GlobalTheory.VacBridge.rho_acts_locCo dd B.ψ v _ hatd (boxFun (G.M'.vac v) (fun x => star (G.M'.vac v x)))

  set x₁ := (GlobalTheory.LatVac.locCo G.M'.co v w₁).1 with hx₁
  set y₁ := (GlobalTheory.LatVac.locCo G.M'.co v w₁).2 with hy₁
  set x₂ := (GlobalTheory.LatVac.locCo G.M'.co v w₂).1 with hx₂
  set y₂ := (GlobalTheory.LatVac.locCo G.M'.co v w₂).2 with hy₂
  have hdl : GlobalTheory.LatVac.locCo dd v (Matrix.fromCols w₁ w₂) = (Sum.elim x₁ x₂, Sum.elim y₁ (-y₂)) := by
    simp only [hx₁, hx₂, hy₁, hy₂, GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hdd w₁ w₂]
    ext k <;> rcases k with k | k <;> simp
  set s₁ := symp (R := AF F) (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) w₁ w₁ with hs₁
  set s₂ := symp (R := AF F) (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) w₂ w₂ with hs₂
  have hb : At (evFin F v) (⅟(2 : AF F) * s₂) :=
    GlobalTheory.VacIndic.at_mul_left (at_symp_self σ _ _ _ v (hat w₂ hw₂))
  have hstarg : star (B.ψ (⅟(2 : AF F) * s₂)) = B.ψ (-(⅟(2 : AF F) * s₂)) := by
    have hb' : At (evFin F v) (-(⅟(2 : AF F) * s₂)) := fun u hu => by rw [smul_neg, hb u hu, neg_zero]
    rw [GlobalTheory.VacIndic.psi_of_at B.ψ hb, GlobalTheory.VacIndic.psi_of_at B.ψ hb', map_neg, ← GlobalTheory.LatVac.psiAt_apply,
      ← GlobalTheory.LatVac.psiAt_apply, star_psiAt B.ψ hψc v]
  have hcd : B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (dbl (incM F G.W.J))
      (Matrix.fromCols w₁ w₂) (Matrix.fromCols w₁ w₂)) = B.ψ (⅟(2 : AF F) * s₁) * star (B.ψ (⅟(2 : AF F) * s₂)) := by
    rw [symp_dbl_fromCols, ← hs₁, ← hs₂, hstarg, mul_sub, sub_eq_add_neg, AddChar.map_add_eq_mul]
  have e : GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (Matrix.fromCols w₁ w₂))
      (boxFun (G.M'.vac v) (fun x => star (G.M'.vac v x))) =
      B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (dbl (incM F G.W.J))
        (Matrix.fromCols w₁ w₂) (Matrix.fromCols w₁ w₂)) • boxFun (G.M'.vac v) (fun x => star (G.M'.vac v x)) := by
    funext x
    rw [hdl, hcd]
    simp only [GlobalTheory.WeilM.schr, boxFun, Pi.smul_apply, smul_eq_mul, invOf_eq_inv]
    have hA : x ⬝ᵥ Sum.elim y₁ (-y₂) + (2 : Fv F v)⁻¹ * (Sum.elim x₁ x₂ ⬝ᵥ Sum.elim y₁ (-y₂)) =
        ((x ∘ Sum.inl) ⬝ᵥ y₁ + (2 : Fv F v)⁻¹ * (x₁ ⬝ᵥ y₁)) +
          -((x ∘ Sum.inr) ⬝ᵥ y₂ + (2 : Fv F v)⁻¹ * (x₂ ⬝ᵥ y₂)) := by
      simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Function.comp_apply, Pi.neg_apply,
        mul_neg, Finset.sum_neg_distrib]
      ring
    have h1 : (x + Sum.elim x₁ x₂) ∘ Sum.inl = x ∘ Sum.inl + x₁ := by funext i; simp
    have h2 : (x + Sum.elim x₁ x₂) ∘ Sum.inr = x ∘ Sum.inr + x₂ := by funext i; simp
    rw [hA, AddChar.map_add_eq_mul, ← star_psiAt B.ψ hψc v, h1, h2]
    have l1 := hloc w₁ hw₁ (x ∘ Sum.inl)
    have l2 := congrArg star (hloc w₂ hw₂ (x ∘ Sum.inr))
    rw [star_mul', star_mul'] at l2
    linear_combination (star (GlobalTheory.LatVac.psiAt B.ψ v ((x ∘ Sum.inr) ⬝ᵥ y₂ + (2 : Fv F v)⁻¹ * (x₂ ⬝ᵥ y₂))) *
      star (G.M'.vac v (x ∘ Sum.inr + x₂))) * l1 + (B.ψ (⅟(2 : AF F) * s₁) * G.M'.vac v (x ∘ Sum.inl)) * l2
  rw [← e]
  exact key

end GlobalTheory.DblVacLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBottomInfinityExponentsGapLargeGridsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bottomInfinityExponents_gap_largeGrids : GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m), ∃ a b : D.what₂.Tau → ℚ, ∀ (t : T) (τ : D.what₂.Tau), HasInfExp D (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) τ (a τ) ∧ HasInfExp D (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) τ (b τ) ∧ 2 * (a τ - b τ) < -((SqNum.botBig D i j + SqNum.botSmall D i j : ℕ) : ℚ) := by
  first | exact @GlobalTheory.BotDict.bottom_infExp_gap | exact GlobalTheory.BotDict.bottom_infExp_gap | (intros; apply GlobalTheory.BotDict.bottom_infExp_gap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCovolumeCommonAdelicFixatorOfColumnsStatement
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteCovolume_common_adelicFixatorOfColumns : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ (π : Measure (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J))) (DM : Set (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J))), π.IsHaarMeasure → IsFundamentalDomain ((ratPts σ J).subgroupOf (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J))) DM π → π DM ≠ ⊤ := by
  first | exact @GlobalTheory.SphEis.finCovol_fixG | exact GlobalTheory.SphEis.finCovol_fixG | (intros; apply GlobalTheory.SphEis.finCovol_fixG <;> assumption)
end

