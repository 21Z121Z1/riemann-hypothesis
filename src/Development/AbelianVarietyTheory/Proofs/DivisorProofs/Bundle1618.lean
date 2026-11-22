import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1584
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1537

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformRationalTranslateQuasiInvariant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaQuasiRat

theorem schr_schr {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (w w' : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) :
    GlobalTheory.WeilM.schr ψ w (GlobalTheory.WeilM.schr ψ w' φ) =
      ψ (⅟(2 : R) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) • GlobalTheory.WeilM.schr ψ (w + w') φ := by
  funext x
  simp only [GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add, add_assoc, ← mul_assoc,
    ← AddChar.map_add_eq_mul, add_dotProduct, dotProduct_add]
  congr 2
  have h : ⅟(2 : R) * 2 = 1 := invOf_mul_self 2
  linear_combination (-(w.1 ⬝ᵥ w'.2)) * h

theorem thetaSum_smul' (F : Type) [Field F] [NumberField F] {κ : Type} (c : ℂ) (φ : (κ → AdeleRing (𝓞 F) F) → ℂ) :
    GlobalTheory.WeilM.thetaSum F (c • φ) = c * GlobalTheory.WeilM.thetaSum F φ := by
  simp only [GlobalTheory.WeilM.thetaSum, Pi.smul_apply, smul_eq_mul, tsum_mul_left]

theorem thetaSum_schr_rat (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : ∀ a : F, ψ (algebraMap F (AdeleRing (𝓞 F) F) a) = 1)
    {κ : Type} [Fintype κ] (y z : κ → F) (φ : (κ → AdeleRing (𝓞 F) F) → ℂ) :
    GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ
      (fun i => algebraMap F (AdeleRing (𝓞 F) F) (y i), fun i => algebraMap F (AdeleRing (𝓞 F) F) (z i)) φ) =
      GlobalTheory.WeilM.thetaSum F φ := by
  have h2 : ⅟(2 : AdeleRing (𝓞 F) F) = algebraMap F (AdeleRing (𝓞 F) F) (1 / 2) := by
    apply invOf_eq_right_inv
    rw [← map_ofNat (algebraMap F (AdeleRing (𝓞 F) F)) 2, ← map_mul]
    norm_num
  have key : ∀ ξ : κ → F, ψ ((fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) ⬝ᵥ
      (fun i => algebraMap F (AdeleRing (𝓞 F) F) (z i)) + ⅟(2 : AdeleRing (𝓞 F) F) *
      ((fun i => algebraMap F (AdeleRing (𝓞 F) F) (y i)) ⬝ᵥ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (z i)))) = 1 := by
    intro ξ
    have e : (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) ⬝ᵥ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (z i)) +
        ⅟(2 : AdeleRing (𝓞 F) F) * ((fun i => algebraMap F (AdeleRing (𝓞 F) F) (y i)) ⬝ᵥ
          (fun i => algebraMap F (AdeleRing (𝓞 F) F) (z i))) =
        algebraMap F (AdeleRing (𝓞 F) F) (ξ ⬝ᵥ z + 1 / 2 * (y ⬝ᵥ z)) := by
      simp only [dotProduct, map_add, map_mul, map_sum, h2]
    rw [e]
    exact hψ _
  unfold GlobalTheory.WeilM.thetaSum GlobalTheory.WeilM.schr
  simp only [key, one_mul]
  rw [← (Equiv.addRight y).tsum_eq (fun ξ : κ → F => φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)))]
  congr 1
  funext ξ
  congr 1
  funext i
  simp

end GlobalTheory.ThetaQuasiRat

namespace GlobalTheory.ThetaQuasiRat

theorem cA_apply (D : D7) (a : AF D.host.F ⊗[D.host.F] D.host.E) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig a = cA D a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => rfl
  | add a b ha hb => rw [map_add, map_add, ha, hb]

theorem symp_eq_symplO (D : D7) (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E)
    (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (hA : JA = T.gramᵀ)
    (hB : ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹)) (x y : Formalism.IndefR.Datum.WO S T) :
    GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB) x y =
      Formalism.IndefR.Datum.symplO S T x y := by
  unfold GlobalTheory.WeilM.symp Formalism.IndefR.Datum.symplO
  congr 1
  have hb : ∀ j l, ξ * incM D.host.F JB j l = incA D D.host.xi0 * incA D (S.gram⁻¹ j l) := fun j l => by
    have := congrFun (congrFun hB j) l
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    rw [this]
    simp [incM, Matrix.map_apply, Matrix.smul_apply, map_mul]
  have e : ∀ i j k l, ξ * (x i j * incM D.host.F JA i k * incM D.host.F JB j l * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig (y k l)) =
      incA D D.host.xi0 * (incA D (S.gram⁻¹ j l) * cA D (y k l) * incA D (T.gram k i) * x i j) := fun i j k l => by
    have h1 : incM D.host.F JA i k = incA D (T.gram k i) := by
      subst hA; rfl
    rw [cA_apply, h1]
    linear_combination (x i j * incA D (T.gram k i) * cA D (y k l)) * hb j l
  unfold GlobalTheory.WeilM.hTens Formalism.IndefR.Datum.hO
  simp only [Finset.mul_sum, e]
  symm
  calc _ = ∑ a, ∑ b, ∑ d, ∑ c, incA D D.host.xi0 *
        (incA D (S.gram⁻¹ a b) * cA D (y c b) * incA D (T.gram c d) * x d a) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ a, ∑ d, ∑ b, ∑ c, incA D D.host.xi0 *
        (incA D (S.gram⁻¹ a b) * cA D (y c b) * incA D (T.gram c d) * x d a) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ d, ∑ a, ∑ b, ∑ c, incA D D.host.xi0 *
        (incA D (S.gram⁻¹ a b) * cA D (y c b) * incA D (T.gram c d) * x d a) := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm

end GlobalTheory.ThetaQuasiRat

namespace GlobalTheory.ThetaQuasiRat

theorem thetaTr_ratW_add : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
      (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
      ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
      ∀ (κ : Type) [Fintype κ]
        (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
        (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
          co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
        ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (w : Formalism.IndefR.Datum.WO S T),
          GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ (ratW T S γ + w) = ψ (-(Formalism.IndefR.Datum.symplOH S T (ratW T S γ) w)) * GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ w := by
  intro D ψ hψ S T JA JB ξ hA hB κ _ co hrat Φ _ γ w
  obtain ⟨y, z, hyz⟩ := hrat γ
  have hγ : ratW T S γ = incM D.host.F γ := rfl
  have hform := co.form (incM D.host.F γ) w
  rw [symp_eq_symplO D S T JA JB ξ hA hB, hyz] at hform
  unfold GlobalTheory.WeilSchrodinger.thetaTr GlobalTheory.WeilM.Darboux.rho
  rw [map_add, hγ, hyz]
  set u : (κ → AF D.host.F) × (κ → AF D.host.F) :=
    (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i)) with hu
  set v := co.e w
  have law := schr_schr ψ u v Φ
  have hinv : ψ (-(⅟(2 : AF D.host.F) * (u.1 ⬝ᵥ v.2 - v.1 ⬝ᵥ u.2))) *
      ψ (⅟(2 : AF D.host.F) * (u.1 ⬝ᵥ v.2 - v.1 ⬝ᵥ u.2)) = 1 := by
    rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  have hsum : GlobalTheory.WeilM.schr ψ (u + v) Φ =
      ψ (-(⅟(2 : AF D.host.F) * (u.1 ⬝ᵥ v.2 - v.1 ⬝ᵥ u.2))) • GlobalTheory.WeilM.schr ψ u (GlobalTheory.WeilM.schr ψ v Φ) := by
    rw [law, smul_smul, hinv, one_smul]
  have h2 : ⅟(2 : AF D.host.F) = algebraMap D.host.F (AF D.host.F) (1 / 2) := by
    apply invOf_eq_right_inv
    rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]
    norm_num
  rw [hsum, thetaSum_smul', hu, thetaSum_schr_rat D.host.F ψ hψ.1.2.2.1 y z, ← hu,
    Formalism.IndefR.Datum.symplOH, hform, h2]

end GlobalTheory.ThetaQuasiRat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDegreeDensityPullbackEqNormSqDetMul
section
set_option autoImplicit false

noncomputable section

open Matrix
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open scoped ComplexConjugate

namespace GlobalTheory.CxForm

open Module

variable {K M : Type} [Field K] [AddCommGroup M] [Module K M]

theorem exterior_repr_univ_of_mem {N k : ℕ} (b : Basis (Fin N) K M) (hk : k ≠ N) {x : ExteriorAlgebra K M}
    (hx : x ∈ ⋀[K]^k M) : b.ExteriorAlgebra.repr x Finset.univ = 0 := by
  rw [Basis.ExteriorAlgebra, Basis.repr_reindex_apply]
  have h1 : (Set.powersetCard.prodEquiv.symm (Finset.univ : Finset (Fin N))).1 = N := by
    simp [Set.powersetCard.prodEquiv]
  rcases e : Set.powersetCard.prodEquiv.symm (Finset.univ : Finset (Fin N)) with ⟨j, a⟩
  rw [e] at h1
  exact DirectSum.IsInternal.collectedBasis_repr_of_mem_ne _ _ (fun h => hk (h.trans h1)) hx

theorem exterior_repr_univ_map {N : ℕ} (b : Basis (Fin N) K M) (f : M →ₗ[K] M) (x : ExteriorAlgebra K M) :
    b.ExteriorAlgebra.repr (ExteriorAlgebra.map f x) Finset.univ =
      LinearMap.det f * b.ExteriorAlgebra.repr x Finset.univ := by
  have key : ∀ s, b.ExteriorAlgebra.repr (ExteriorAlgebra.map f (b.ExteriorAlgebra s)) Finset.univ =
      LinearMap.det f * b.ExteriorAlgebra.repr (b.ExteriorAlgebra s) Finset.univ := by
    intro s
    by_cases hs : s = Finset.univ
    · subst hs
      set g : M [⋀^Fin N]→ₗ[K] K :=
        (Finsupp.lapply Finset.univ ∘ₗ b.ExteriorAlgebra.repr.toLinearMap).compAlternatingMap
          (ExteriorAlgebra.ιMulti K N) with hg
      have hb : ∀ w : Fin N → M, g w = b.ExteriorAlgebra.repr (ExteriorAlgebra.ιMulti K N w) Finset.univ := fun _ => rfl
      have he := AlternatingMap.eq_smul_basis_det b g
      rw [ExteriorAlgebra.basis_apply_ofCard _ (by simp : (Finset.univ : Finset (Fin N)).card = N)]
      dsimp only [ExteriorAlgebra.ιMulti_family]
      rw [ExteriorAlgebra.map_apply_ιMulti, ← hb, ← hb, he,
        AlternatingMap.smul_apply, AlternatingMap.smul_apply, Basis.det_comp, smul_eq_mul, smul_eq_mul]
      ring
    · have hc : s.card ≠ N := fun h => hs (Finset.eq_univ_of_card s (by simpa using h))
      rw [Basis.repr_self, Finsupp.single_apply, if_neg hs, mul_zero,
        ExteriorAlgebra.basis_apply]
      dsimp only [ExteriorAlgebra.ιMulti_family]
      rw [ExteriorAlgebra.map_apply_ιMulti]
      exact exterior_repr_univ_of_mem b hc (ExteriorAlgebra.ιMulti_range K _ ⟨_, rfl⟩)
  have := b.ExteriorAlgebra.ext
    (f₁ := Finsupp.lapply Finset.univ ∘ₗ b.ExteriorAlgebra.repr.toLinearMap ∘ₗ (ExteriorAlgebra.map f).toLinearMap)
    (f₂ := LinearMap.det f • (Finsupp.lapply Finset.univ ∘ₗ b.ExteriorAlgebra.repr.toLinearMap))
    (fun s => by simpa using key s)
  simpa using LinearMap.congr_fun this x

theorem det_pull_gen {n : ℕ} (L : V n →L[ℂ] V n) :
    LinearMap.det (Matrix.toLin' (fromBlocks (of fun b a => L (coordVec b) a) 0 0
      (of fun b a => conj (L (coordVec b) a)))) = ((‖L.det‖ ^ 2 : ℝ) : ℂ) := by
  rw [LinearMap.det_toLin', det_fromBlocks_zero₂₁]
  have hP : (of fun b a => L (coordVec b) a).det = L.det := by
    rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin n) ℂ).toBasis,
      ← det_transpose]
    congr 1
  have hQ : (of fun b a => conj (L (coordVec b) a)) = (starRingEnd ℂ).mapMatrix (of fun b a => L (coordVec b) a) := by
    ext i j; simp
  rw [hQ, ← RingHom.map_det, hP, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem dens_pull {n : ℕ} (L : V n →L[ℂ] V n) (ω : Alt n) :
    dens (pull L ω) = ((‖L.det‖ ^ 2 : ℝ) : ℂ) * dens ω := by
  simp only [dens, pull, bas]
  rw [exterior_repr_univ_map, det_pull_gen, mul_div_assoc]

end GlobalTheory.CxForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopPowerHermitianFormDensity
section
open GlobalTheory.CxForm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CxForm.DensPow

variable {n : ℕ}

theorem ι_mul_ι_mul_ι_mul_ι_left (u w w' : Fin n ⊕ Fin n → ℂ) :
    ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ w * (ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ w') = (0 : Alt n) := by
  have h := eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (R := ℂ) (M := Fin n ⊕ Fin n → ℂ) w u)
  calc _ = ExteriorAlgebra.ι ℂ u * (ExteriorAlgebra.ι ℂ w * ExteriorAlgebra.ι ℂ u) * ExteriorAlgebra.ι ℂ w' := by
          simp only [mul_assoc]
    _ = -(ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ w * ExteriorAlgebra.ι ℂ w') := by
          rw [h]; simp only [mul_neg, neg_mul, mul_assoc]
    _ = 0 := by rw [ExteriorAlgebra.ι_sq_zero]; simp

theorem ι_mul_ι_mul_ι_mul_ι_right (u u' w : Fin n ⊕ Fin n → ℂ) :
    ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ w * (ExteriorAlgebra.ι ℂ u' * ExteriorAlgebra.ι ℂ w) = (0 : Alt n) := by
  have h := eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (R := ℂ) (M := Fin n ⊕ Fin n → ℂ) w u')
  calc _ = ExteriorAlgebra.ι ℂ u * (ExteriorAlgebra.ι ℂ w * ExteriorAlgebra.ι ℂ u') * ExteriorAlgebra.ι ℂ w := by
          simp only [mul_assoc]
    _ = -(ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ u' * (ExteriorAlgebra.ι ℂ w * ExteriorAlgebra.ι ℂ w)) := by
          rw [h]; simp only [mul_neg, neg_mul, mul_assoc]
    _ = 0 := by rw [ExteriorAlgebra.ι_sq_zero]; simp

def row (a : Fin n) : (Fin n → ℂ) →ₗ[ℂ] Ev n where
  toFun w := ∑ b, w b • sym (a, b)
  map_add' v w := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c w := by simp [Finset.smul_sum, smul_smul]

theorem coe_row (a : Fin n) (w : Fin n → ℂ) :
    (row a w : Alt n) = dz a * ExteriorAlgebra.ι ℂ (∑ b, w b • Pi.single (Sum.inr b) (1 : ℂ)) := by
  simp [row, sym, dzb, Finset.mul_sum, mul_smul_comm]

theorem row_mul_row (a : Fin n) (w : Fin n → ℂ) : row a w * row a w = 0 := by
  apply Subtype.ext
  rw [Subalgebra.coe_mul, coe_row, dz]
  exact ι_mul_ι_mul_ι_mul_ι_left _ _ _

theorem row_mul_row_of_ne {a a' : Fin n} (w : Fin n → ℂ) : row a w * row a' w = 0 := by
  apply Subtype.ext
  rw [Subalgebra.coe_mul, coe_row, coe_row, dz, dz]
  exact ι_mul_ι_mul_ι_mul_ι_right _ _ _

def altRows (n : ℕ) : (Fin n → ℂ) [⋀^Fin n]→ₗ[ℂ] Ev n where
  toMultilinearMap := (MultilinearMap.mkPiAlgebra ℂ (Fin n) (Ev n)).compLinearMap row
  map_eq_zero_of_eq' v i j hij hne := by
    change ∏ a, row a (v a) = 0
    rw [← Finset.mul_prod_erase Finset.univ (fun a => row a (v a)) (Finset.mem_univ i),
      ← Finset.mul_prod_erase (Finset.univ.erase i) (fun a => row a (v a))
        (Finset.mem_erase.2 ⟨hne.symm, Finset.mem_univ j⟩), ← mul_assoc, hij, row_mul_row_of_ne, zero_mul]

theorem altRows_apply (v : Fin n → Fin n → ℂ) : altRows n v = ∏ a, row a (v a) := by
  first
  | rfl
  | simp only [altRows, AlternatingMap.coe_mk, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]

theorem alt_eq_det_smul {K M N : Type} [CommRing K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] {m : ℕ} (e : Module.Basis (Fin m) K M)
    (f : M [⋀^Fin m]→ₗ[K] N) (h : Fin m → M) : f h = e.det h • f e := by
  have key : f = (LinearMap.toSpanSingleton K N (f e)).compAlternatingMap e.det := by
    refine e.ext_alternating (fun v hv => ?_)
    have hb : Function.Bijective v := Finite.injective_iff_bijective.1 hv
    let σ : Equiv.Perm (Fin m) := Equiv.ofBijective v hb
    have hσ : (fun i => e (v i)) = (⇑e) ∘ ⇑σ := rfl
    rw [hσ, LinearMap.compAlternatingMap_apply, LinearMap.toSpanSingleton_apply,
      AlternatingMap.map_perm, AlternatingMap.map_perm, e.det_self, Units.smul_def,
      Units.smul_def, smul_one_smul]
  rw [DFunLike.congr_fun key h]
  rfl

theorem prod_row (H : Matrix (Fin n) (Fin n) ℂ) : ∏ a, row a (H a) = H.det • ∏ a, sym (a, a) := by
  have h1 : ∏ a, row a (H a) = altRows n (fun a b => H a b) := (altRows_apply _).symm
  rw [h1, alt_eq_det_smul (Pi.basisFun ℂ (Fin n)), Pi.basisFun_det, altRows_apply]
  congr 1
  refine Finset.prod_congr rfl fun a _ => ?_
  simp [row, Pi.single_apply]

theorem add_pow_of_mul_self {R : Type*} [CommRing R] {x : R} (hx : x * x = 0) (y : R) (m : ℕ) :
    (x + y) ^ (m + 1) = y ^ (m + 1) + ((m : R) + 1) * x * y ^ m := by
  induction m with
  | zero => simp [add_comm]
  | succ m ih =>
    rw [pow_succ, ih]
    push_cast
    linear_combination ((m : R) + 1) * y ^ m * hx

theorem sum_pow_card {R ι : Type*} [CommRing R] [DecidableEq ι] (f : ι → R) (hf : ∀ a, f a * f a = 0) (s : Finset ι) :
    (∀ m, (∑ a ∈ s, f a) ^ (s.card + 1 + m) = 0) ∧ (∑ a ∈ s, f a) ^ s.card = (s.card.factorial : R) * ∏ a ∈ s, f a := by
  induction s using Finset.induction_on with
  | empty => exact ⟨fun m => by simp, by simp⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    refine ⟨fun m => ?_, ?_⟩
    · rw [show s.card + 1 + 1 + m = (s.card + 1 + m) + 1 by omega, add_pow_of_mul_self (hf a),
        show s.card + 1 + m + 1 = s.card + 1 + (m + 1) by omega, ih.1, ih.1]
      simp
    · rw [add_pow_of_mul_self (hf a), show s.card + 1 = s.card + 1 + 0 by rfl, ih.1, ih.2, Nat.factorial_succ]
      push_cast
      ring

theorem dens_smul (c : ℂ) (x : Alt n) : dens (c • x) = c * dens x := by
  simp only [dens, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_div_assoc]

theorem vol_eq_smul_prod (n : ℕ) : vol n = (Complex.I / 2) ^ n • ∏ a, sym (a, a) := by
  simp only [vol, Algebra.smul_def, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    map_pow]

theorem dens_pow (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ) :
    GlobalTheory.CxForm.dens (((∑ a, ∑ b, H a b • GlobalTheory.CxForm.sym (a, b) : GlobalTheory.CxForm.Ev n) ^ n : GlobalTheory.CxForm.Ev n) :
      GlobalTheory.CxForm.Alt n) = (n.factorial : ℂ) * H.det / (Complex.I / 2) ^ n := by
  have hω : (∑ a, ∑ b, H a b • sym (a, b) : Ev n) = ∑ a, row a (H a) := by simp [row]
  have hp : (∑ a, row a (H a)) ^ n = (n.factorial : Ev n) * ∏ a, row a (H a) := by
    simpa using (sum_pow_card (fun a => row a (H a)) (fun a => row_mul_row a _) Finset.univ).2
  have hP : (n.factorial : Ev n) * ∏ a, row a (H a) = ((n.factorial : ℂ) * H.det) • ∏ a, sym (a, a) := by
    rw [prod_row, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  have h1 := dens_vol n
  rw [vol_eq_smul_prod, Subalgebra.coe_smul, dens_smul] at h1
  rw [hω, hp, hP, Subalgebra.coe_smul, dens_smul, div_eq_mul_inv, eq_inv_of_mul_eq_one_right h1]

end GlobalTheory.CxForm.DensPow

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionUnramifiedOfHasGoodReduction
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Published.AbVarRed

theorem torsionUnramified_of_hasGoodReduction : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] (V : ValuationSubring Ω),
    IsAbove R K V.toSubring → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], HasGoodReduction R K A →
    ∀ m : ℕ, (m : ResidueField R) ≠ 0 → TorsionUnramified A V m := by
  intro R K Ω _ _ _ _ _ _ _ _ V hV A _ _ hA m hm σ hσ x hx
  obtain ⟨G, _, hG, e, he⟩ := hA
  have : IsCommMonObj G := hG.comm
  have : Smooth G.hom := hG.smooth
  have : IsProper G.hom := hG.proper
  have : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  have hP : IsGrpPullback A G (spMap (algebraMap R K)) (e.inv.left ≫ pullback.fst G.hom (spMap (algebraMap R K))) :=
    ((isGrpPullback_of_iso e.symm).comp (isGrpPullback_pullback G (spMap (algebraMap R K)))).congr
      (Category.id_comp _) rfl
  set φ := e.inv.left ≫ pullback.fst G.hom (spMap (algebraMap R K)) with hφ

  let T0 : Over (Sp R) := Over.mk ((ptOver K Ω).hom ≫ spMap (algebraMap R K))
  let Φ : (ptOver K Ω ⟶ A) → (T0 ⟶ G) := fun y => Over.homMk (y.left ≫ φ) (by
    change (y.left ≫ φ) ≫ G.hom = (ptOver K Ω).hom ≫ spMap (algebraMap R K)
    rw [Category.assoc, hP.1.w, ← Category.assoc, Over.w y])
  have Φmul : ∀ y y', Φ (y * y') = Φ y * Φ y' := fun y y' =>
    Over.OverMorphism.ext (hP.2 (ptOver K Ω) y y' (Φ y) (Φ y') rfl rfl).symm
  let ΦM : (ptOver K Ω ⟶ A) →* (T0 ⟶ G) := MonoidHom.mk' Φ Φmul
  have Φinj : Function.Injective Φ := fun y y' h =>
    Over.OverMorphism.ext (hP.1.hom_ext (congrArg Over.Hom.left h) ((Over.w y).trans (Over.w y').symm))

  have hmemV : ∀ r : R, algebraMap K Ω (algebraMap R K r) ∈ V := fun r => by
    have : algebraMap R K r ∈ V.toSubring.comap (algebraMap K Ω) := by rw [hV]; exact ⟨r, rfl⟩
    exact this
  let rV : R →+* V := ((algebraMap K Ω).comp (algebraMap R K)).codRestrict V hmemV
  have hrV : (algebraMap V Ω).comp rV = (algebraMap K Ω).comp (algebraMap R K) := RingHom.ext fun _ => rfl

  obtain ⟨hσV, hσr⟩ := (mem_inertia_iff V σ).1 hσ
  have hmem : ∀ y ∈ V, σ y ∈ V := fun y hy => by
    have h := (ValuationSubring.smul_mem_pointwise_smul_iff (g := σ) (S := V) (x := y)).2 hy
    rw [hσV] at h
    exact h
  let σV : V →+* V := ((σ : Ω →+* Ω).comp (algebraMap V Ω)).codRestrict V fun y => hmem y y.2
  have F1 : (algebraMap V Ω).comp σV = (σ : Ω →+* Ω).comp (algebraMap V Ω) := RingHom.ext fun _ => rfl
  have F2 : σV.comp rV = rV := RingHom.ext fun r => Subtype.ext (σ.commutes (algebraMap R K r))
  have F3 : (residue V).comp σV = residue V := RingHom.ext fun y => by
    change residue V (σV y) = residue V y
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
    exact hσr y y.2

  have hE : ValuativeCriterion.Existence G.hom := by
    have h : (ValuativeCriterion.Existence ⊓ @QuasiCompact) G.hom := by
      rw [← UniversallyClosed.eq_valuativeCriterion]; infer_instance
    exact h.1
  let S : ValuativeCommSq G.hom := ⟨V, Ω, (Φ x).left, spMap rV, ⟨by
    change (x.left ≫ φ) ≫ G.hom = spMap (algebraMap V Ω) ≫ spMap rV
    rw [Category.assoc, hP.1.w, ← Category.assoc, Over.w x, GlobalTheory.RedPts.spMap_comp, hrV]
    exact GlobalTheory.RedPts.spMap_comp _ _⟩⟩
  obtain ⟨l, hl1, hl2⟩ := (hE S).exists_lift.some
  change spMap (algebraMap V Ω) ≫ l = x.left ≫ φ at hl1
  change l ≫ G.hom = spMap rV at hl2
  let P : Over (Sp R) := Over.mk (spMap rV)
  let a : P ⟶ G := Over.homMk l hl2
  let b : P ⟶ G := Over.homMk (spMap σV ≫ l) (by
    change (spMap σV ≫ l) ≫ G.hom = spMap rV
    rw [Category.assoc, hl2, GlobalTheory.RedPts.spMap_comp, F2])
  let u : T0 ⟶ P := Over.homMk (spMap (algebraMap V Ω)) (by
    change spMap (algebraMap V Ω) ≫ spMap rV = (ptOver K Ω).hom ≫ spMap (algebraMap R K)
    rw [GlobalTheory.RedPts.spMap_comp, hrV]
    exact (GlobalTheory.RedPts.spMap_comp _ _).symm)
  have hua : u ≫ a = Φ x := Over.OverMorphism.ext hl1
  have hub : u ≫ b = Φ (galPts A σ x) := Over.OverMorphism.ext (by
    change spMap (algebraMap V Ω) ≫ spMap σV ≫ l = (galPts A σ x).left ≫ φ
    rw [galPts_left, ← Category.assoc, GlobalTheory.RedPts.spMap_comp, F1, ← GlobalTheory.RedPts.spMap_comp, Category.assoc, hl1,
      Category.assoc])

  let Z : Over (Sp R) := Over.mk (spMap ((residue V).comp rV))
  let j : Z ⟶ P := Over.homMk (spMap (residue V)) (GlobalTheory.RedPts.spMap_comp _ _)
  have hjb : j ≫ b = j ≫ a := Over.OverMorphism.ext (by
    change spMap (residue V) ≫ spMap σV ≫ l = spMap (residue V) ≫ l
    rw [← Category.assoc, GlobalTheory.RedPts.spMap_comp, F3])
  have hdom : IsDominant (spMap (algebraMap V Ω)) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
      change RingHom.ker (algebraMap V Ω) ≤ _
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V Ω)]; exact bot_le)⟩
  have hu : Function.Injective (GlobalTheory.RedPts.precomp G u) := fun c d h => Over.OverMorphism.ext
    (ext_of_isDominant_of_isSeparated (X := Sp V) G.hom ((Over.w c).trans (Over.w d).symm)
      (spMap (algebraMap V Ω)) (congrArg Over.Hom.left h))
  have hz : (b * a⁻¹) ^ m = 1 := by
    apply hu
    rw [map_pow, map_one, map_mul, map_inv]
    change ((u ≫ b) * (u ≫ a)⁻¹) ^ m = 1
    rw [hua, hub]
    change (ΦM (galPts A σ x) * (ΦM x)⁻¹) ^ m = 1
    rw [← map_inv, ← map_mul, ← map_pow, mul_pow, inv_pow, ← map_pow, hx, map_one, inv_one, _root_.mul_one, map_one]
  have hjz : j ≫ (b * a⁻¹) = 1 := by
    rw [MonObj.comp_mul, GrpObj.comp_inv, hjb, mul_inv_cancel]
  have hn : IsUnit (m : V) := by
    have h1 : IsUnit (m : R) := by
      by_contra h
      apply hm
      rw [← map_natCast (residue R), residue_eq_zero_iff]
      exact h
    simpa using h1.map rV
  have h1 := GlobalTheory.RedPts.eq_one_of_pow_of_closedPoint G (spMap rV) hn (b * a⁻¹) hz j
    ⟨IsLocalRing.closedPoint _, IsLocalRing.comap_closedPoint (IsLocalRing.residue V)⟩ hjz
  have hba : b = a := mul_inv_eq_one.1 h1
  apply Φinj
  rw [← hub, ← hua, hba]

end GlobalTheory.Published.AbVarRed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentBlockTriangularNilpotentStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_block_triangular_nilpotent : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n n₁ : ℕ) (Y : Spc F E n) (H : Plane E n n₁) (R : Matrix (Fin (1 + n₁ + 1)) (Fin n) E), frame H * R = 1 → R * frame H = 1 →
    ∀ u : UA σ Y.J, (∀ i j, blk n₁ j < blk n₁ i + 1 → (incM F R * (mat u - 1 : Matrix (Fin n) (Fin n) (AE F E)) * incM F (frame H) :
        Matrix (Fin (1 + n₁ + 1)) (Fin (1 + n₁ + 1)) (AE F E)) i j = 0) →
      u ∈ unip σ Y H := by
  first | exact @GlobalTheory.LeviHC.UnipFrame.mem_unip_of_strictBlockTri | exact GlobalTheory.LeviHC.UnipFrame.mem_unip_of_strictBlockTri | (intros; apply GlobalTheory.LeviHC.UnipFrame.mem_unip_of_strictBlockTri <;> assumption)
end

