import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1388
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1368
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1429
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1427
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1440
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1390
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1441
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSplitFinMulSplitInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryToDoubledFirstFactorBigCellInertPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1406
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1442
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1421

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftSubmoduleComapStableSecondMember
section
noncomputable section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

namespace GlobalTheory.HoweD

theorem sumPl_single_add_smul {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)]
    [∀ i, Module ℂ (V i)] (L : ∀ w, Module.End ℂ (V w)) (a : ι → ℂ) (w : ι) (hL : ∀ v, v ≠ w → L v = 0) :
    sumPl (fun v => L v + a v • (1 : Module.End ℂ (V v))) =
      atPl w (L w) + (∑ v, a v) • (1 : Module.End ℂ (⨂[ℂ] i, V i)) := by
  have h : ∀ w, atPl w (L w + a w • (1 : Module.End ℂ (V w))) = atPl w (L w) + a w • (1 : Module.End ℂ (⨂[ℂ] i, V i)) := by
    intro w
    have e := (PiTensorProduct.mapMultilinear ℂ V V).map_update_add (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w (L w)
      (a w • LinearMap.id)
    have e2 := (PiTensorProduct.mapMultilinear ℂ V V).map_update_smul (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w (a w)
      LinearMap.id
    simp only [PiTensorProduct.mapMultilinear_apply, Function.update_eq_self, PiTensorProduct.map_id] at e e2
    simp only [atPl]
    rw [Module.End.one_eq_id, Module.End.one_eq_id, e, e2]
  have h0 : ∀ v, v ≠ w → atPl v (L v) = (0 : Module.End ℂ (⨂[ℂ] i, V i)) := by
    intro v hv
    rw [hL v hv]
    exact (PiTensorProduct.mapMultilinear ℂ V V).map_update_zero (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) v
  simp only [sumPl, h, Finset.sum_add_distrib, Finset.sum_smul]
  rw [Finset.sum_eq_single w (fun v _ hv => h0 v hv) (fun hw => absurd (Finset.mem_univ w) hw)]

theorem stab_comap_of_thetaSubInf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (om : Rep σ X W) (τ : ∀ w : InfinitePlace F, EmbOver E w) (P Q R S : InfinitePlace F → ℕ) (Φ : TensD F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)) (c : InfinitePlace F → ℂ) (N : Submodule ℂ (SInf F (Fin n × Fin d))), IsCMExt F E σ → GlobalTheory.Published.ThetaSubInf M ψ τ om N → ∀ C : ∀ w : InfinitePlace F, Matrix (Fin d) (Ix (R w) (S w)) ℂ, (∀ w, IsFrame (Complex.I • (incM F W.J).map (piInf (τ w))) (C w)) → ActsByD τ C (om.comp (MonoidHom.inr _ _)) Φ (fun w => fockAct2 (P w) (Q w) (R w) (S w)) c → ∀ w, GlobalTheory.HoweR.Stab (GlobalTheory.HoweR.actAt (V := fun w => Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)) w (fockAct2 (P w) (Q w) (R w) (S w))) (N.comap Φ) := by
  intro F E _ _ _ _ _ σ n d X W M ψ om τ P Q R S Φ c N hCM hN C hC hact w
  have key : ∀ Z ∈ upq (R w) (S w), ∀ y ∈ N.comap Φ,
      GlobalTheory.HoweR.actAt (V := fun w => Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)) w (fockAct2 (P w) (Q w) (R w) (S w)) Z y
        ∈ N.comap Φ := by
    intro Z hZ y hy
    set Y : ∀ v : InfinitePlace F, Mat (R v) (S v) := Pi.single w Z with hYdef
    have hYw : Y w = Z := by simp [hYdef]
    have hYv : ∀ v, v ≠ w → Y v = 0 := fun v hv => by simp [hYdef, Pi.single_eq_of_ne hv]
    have hY : ∀ v, Y v ∈ upq (R v) (S v) := by
      intro v
      by_cases hv : v = w
      · subst hv; rw [hYw]; exact hZ
      · rw [hYv v hv]; simp [upq]
    obtain ⟨γ, hγ, hgen⟩ := GlobalTheory.T.exists_oneParameterSubgroup_unitary_of_realPlace_lieAlg F E σ (Fin d) R S τ (incM F W.J) Complex.I C hCM hC Y hY
    have hSD := hact γ hγ Y hgen y
    have hD := (actsLaws F (Fin n × Fin d) _ _ (Φ y)).1 _ (fun t => map_zero _) hSD
    have hmem := hN.2.2.2.1 γ hγ (Φ y) hy _ hD
    rw [sumPl_single_add_smul (fun v => fockAct2 (P v) (Q v) (R v) (S v) (Y v)) (fun v => c v * (Y v).trace) w
      (fun v hv => by simp only [hYv v hv, map_zero]), hYw, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.one_apply, map_add, map_smul] at hmem
    exact (N.add_mem_iff_left (N.smul_mem _ hy)).1 hmem
  intro Z y hy
  obtain ⟨A, hA, B, hB, rfl⟩ := GlobalTheory.T.exists_indefiniteUnitaryLieAlg_add_I_smul_eq _ _ Z
  rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
  exact add_mem (key A hA y hy) (Submodule.smul_mem _ _ (key B hB y hy))

end GlobalTheory.HoweD

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftSubmoduleContainsFirstMemberCoinvariant
section
noncomputable section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

namespace GlobalTheory.HoweD

section Tensor

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

theorem coinv_atPl_tprod (w : ι) (L : Module.End ℂ (V w)) (f : ∀ i, V i) :
    atPl w L (PiTensorProduct.tprod ℂ f) = PiTensorProduct.tprod ℂ (Function.update f w (L (f w))) := by
  unfold atPl
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext i
  by_cases h : i = w
  · subst h
    simp
  · simp [Function.update_of_ne h]

theorem coinv_sumPl_tprod (w : ι) (L : ∀ i, Module.End ℂ (V i)) (hL : ∀ i, i ≠ w → L i = 0) (f : ∀ i, V i) :
    sumPl L (PiTensorProduct.tprod ℂ f) = PiTensorProduct.tprod ℂ (Function.update f w (L w (f w))) := by
  unfold sumPl
  rw [LinearMap.sum_apply, Finset.sum_eq_single w, coinv_atPl_tprod]
  · intro i _ hi
    rw [coinv_atPl_tprod, hL i hi, LinearMap.zero_apply, MultilinearMap.map_update_zero]
  · intro h
    exact absurd (Finset.mem_univ w) h

end Tensor

theorem tensAny_coinv_le_comap : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (om : Rep σ X W) (τ : ∀ w : InfinitePlace F, EmbOver E w) (P Q R S : InfinitePlace F → ℕ) (Φ : TensD F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)) (c : InfinitePlace F → ℂ) (N : Submodule ℂ (SInf F (Fin n × Fin d))), IsCMExt F E σ → GlobalTheory.Published.ThetaSubInf M ψ τ om N → LinearMap.range Φ = M.Pol ψ τ → ∀ A : ∀ w : InfinitePlace F, Matrix (Fin n) (Ix (P w) (Q w)) ℂ, (∀ w, IsFrame ((1 : ℂ) • (incM F X.J).map (piInf (τ w))) (A w)) → ActsByD τ A (om.comp (MonoidHom.inl _ _)) Φ (fun w => fockAct1 (P w) (Q w) (R w) (S w)) c → GlobalTheory.HoweR.tensAny (fun w => GlobalTheory.HoweR.coinv (P w) (Q w) (R w) (S w) (-c w)) ≤ N.comap Φ := by
  intro F E _ _ _ _ _ σ n d X W M ψ om τ P Q R S Φ c N hCM hN hr A hA hact
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, ⟨w, hw⟩, rfl⟩
  let e : Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w) →ₗ[ℂ] TensD F P Q R S := (PiTensorProduct.tprod ℂ).toLinearMap f w
  have he : ∀ g, e g = PiTensorProduct.tprod ℂ (Function.update f w g) := fun g => rfl
  have key : ∀ Z ∈ upq (P w) (Q w), ∀ g,
      fockAct1 (P w) (Q w) (R w) (S w) Z g - (-c w * Z.trace) • g ∈ (N.comap Φ).comap e := by
    intro Z hZ g
    let Y : ∀ i : InfinitePlace F, Mat (P i) (Q i) := Pi.single w Z
    have hY : ∀ i, Y i ∈ upq (P i) (Q i) := by
      intro i
      by_cases h : i = w
      · subst h
        simpa [Y] using hZ
      · simp [Y, Pi.single_eq_of_ne h, upq]
    obtain ⟨γ, hγ, hgen⟩ := GlobalTheory.T.exists_oneParameterSubgroup_unitary_of_realPlace_lieAlg F E σ (Fin n) P Q τ (incM F X.J) 1 A hCM hA Y hY
    have h1 := hact γ hγ Y hgen (e g)
    have h2 := (actsLaws F (Fin n × Fin d) _ _ 0).1 _ (fun t => map_zero _) h1
    have h3 := hN.2.1 γ hγ _ (hr ▸ LinearMap.mem_range_self Φ (e g)) _ h2
    rw [he, coinv_sumPl_tprod w _ (fun i hi => by simp [Y, Pi.single_eq_of_ne hi])] at h3
    rw [Submodule.mem_comap, Submodule.mem_comap, he]
    simpa [Y, sub_eq_add_neg] using h3
  have hle : GlobalTheory.HoweR.coinv (P w) (Q w) (R w) (S w) (-c w) ≤ (N.comap Φ).comap e := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨Z, g, rfl⟩
    obtain ⟨Z₁, h₁, Z₂, h₂, rfl⟩ := GlobalTheory.T.exists_indefiniteUnitaryLieAlg_add_I_smul_eq _ _ Z
    have h := Submodule.add_mem _ (key Z₁ h₁ g) (Submodule.smul_mem _ Complex.I (key Z₂ h₂ g))
    rw [SetLike.mem_coe]
    convert h using 1
    simp only [map_add, map_smul, Matrix.trace_add, Matrix.trace_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    module
  have h := hle hw
  rw [Submodule.mem_comap, he, Function.update_eq_self] at h
  exact h

end GlobalTheory.HoweD

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusMulVecX
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.LeviTorus

open Matrix

variable {R : Type} [CommRing R] {n m : ℕ}

def torusMat (c : R →+* R) (J : Matrix (Fin n) (Fin n) R) (X Y : Fin n → R) (t : Rˣ) : Matrix (Fin n) (Fin n) R :=
  1 + ((t : R) - 1) • vecMulVec X (J *ᵥ fun i => c (Y i)) + (1 - c (↑t⁻¹ : R)) • vecMulVec Y (J *ᵥ fun i => c (X i))

section
variable (c : R →+* R) (J : Matrix (Fin n) (Fin n) R) (X Y : Fin n → R)

theorem conj_mulVec (hJ : ∀ i j, c (J j i) = -J i j) (V : Fin n → R) (hc : ∀ r, c (c r) = r) :
    (fun i => c ((J *ᵥ fun k => c (V k)) i)) = -(V ᵥ* J) := by
  funext i
  simp only [mulVec, vecMul, dotProduct, map_sum, map_mul, hc, Pi.neg_apply]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hJ k i]; ring

theorem conj_dot (a b : Fin n → R) : c (a ⬝ᵥ b) = (fun i => c (a i)) ⬝ᵥ (fun i => c (b i)) := by
  simp [dotProduct, map_sum, map_mul]

theorem vmv_mulVec (u v w : Fin n → R) : vecMulVec u v *ᵥ w = (v ⬝ᵥ w) • u := by
  ext i
  simp [mulVec, dotProduct, vecMulVec, Finset.mul_sum, mul_comm, mul_left_comm]

end

section Props

variable {c : R →+* R} {J : Matrix (Fin n) (Fin n) R} {X Y : Fin n → R}
  (hc : ∀ r, c (c r) = r) (hJ : ∀ i j, c (J j i) = -J i j)
  (hXX : X ⬝ᵥ J *ᵥ (fun i => c (X i)) = 0) (hYY : Y ⬝ᵥ J *ᵥ (fun i => c (Y i)) = 0)
  (hXY : X ⬝ᵥ J *ᵥ (fun i => c (Y i)) = 1)
include hc hJ hXY

theorem dot_yx : Y ⬝ᵥ J *ᵥ (fun i => c (X i)) = -1 := by
  rw [dotProduct_mulVec]
  have h := conj_mulVec c J hJ Y hc
  rw [show Y ᵥ* J = -(fun i => c ((J *ᵥ fun k => c (Y k)) i)) by rw [h, neg_neg]]
  rw [neg_dotProduct, ← conj_dot, dotProduct_comm (J *ᵥ _) X, hXY, map_one]

omit hc hJ in
theorem torus_mulVec_x (t : Rˣ) (hXX : X ⬝ᵥ J *ᵥ (fun i => c (X i)) = 0) :
    torusMat c J X Y t *ᵥ X = (t : R) • X := by
  simp only [torusMat, add_mulVec, one_mulVec, smul_mulVec, vmv_mulVec]
  rw [dotProduct_comm (J *ᵥ _) X, dotProduct_comm (J *ᵥ _) X, hXY, hXX]
  module

theorem torus_mulVec_y (t : Rˣ) (hYY : Y ⬝ᵥ J *ᵥ (fun i => c (Y i)) = 0) :
    torusMat c J X Y t *ᵥ Y = c (↑t⁻¹ : R) • Y := by
  have hyx := dot_yx hc hJ hXY
  simp only [torusMat, add_mulVec, one_mulVec, smul_mulVec, vmv_mulVec]
  rw [dotProduct_comm (J *ᵥ _) Y, dotProduct_comm (J *ᵥ _) Y, hyx, hYY]
  module

theorem torus_mul_of (t : Rˣ) (A : Matrix (Fin n) (Fin m) R) (hu : (J *ᵥ fun i => c (Y i)) ᵥ* A = 0)
    (hw : (J *ᵥ fun i => c (X i)) ᵥ* A = 0) : torusMat c J X Y t * A = A := by
  have hz : ∀ v : Fin n → R, vecMulVec v (0 : Fin m → R) = 0 := fun v => by ext; simp [vecMulVec]
  simp only [torusMat, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, vecMulVec_mul, hu, hw, hz, smul_zero, add_zero]

theorem torus_mul_inv (t : Rˣ) (hXX : X ⬝ᵥ J *ᵥ (fun i => c (X i)) = 0)
    (hYY : Y ⬝ᵥ J *ᵥ (fun i => c (Y i)) = 0) : torusMat c J X Y t * torusMat c J X Y t⁻¹ = 1 := by
  have hyx := dot_yx hc hJ hXY
  have ht : (t : R) * (↑t⁻¹ : R) = 1 := Units.mul_inv t
  have hct : c (t : R) * c (↑t⁻¹ : R) = 1 := by rw [← map_mul, ht, map_one]
  simp only [torusMat, inv_inv, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul, vecMulVec_mul_vecMulVec]
  rw [dotProduct_comm (J *ᵥ fun i => c (Y i)) X, dotProduct_comm (J *ᵥ fun i => c (Y i)) Y,
    dotProduct_comm (J *ᵥ fun i => c (X i)) X, dotProduct_comm (J *ᵥ fun i => c (X i)) Y, hXY, hYY, hXX, hyx]
  simp only [vecMulVec_smul, vecMulVec_neg, zero_smul, vecMulVec_zero, smul_zero, add_zero, zero_add, one_smul, neg_smul, smul_neg,
    smul_smul]
  match_scalars <;> first | linear_combination ht | linear_combination -hct | ring1

theorem torus_unitary (t : Rˣ) (hXX : X ⬝ᵥ J *ᵥ (fun i => c (X i)) = 0)
    (hYY : Y ⬝ᵥ J *ᵥ (fun i => c (Y i)) = 0) :
    (torusMat c J X Y t)ᵀ * J * (torusMat c J X Y t).map c = J := by
  have hyx := dot_yx hc hJ hXY
  have ht : (t : R) * (↑t⁻¹ : R) = 1 := Units.mul_inv t
  have hct : c (t : R) * c (↑t⁻¹ : R) = 1 := by rw [← map_mul, ht, map_one]
  have hu := conj_mulVec c J hJ Y hc
  have hw := conj_mulVec c J hJ X hc
  have hmap : (torusMat c J X Y t).map c = 1 + c ((t : R) - 1) • vecMulVec (fun i => c (X i)) (-(Y ᵥ* J)) +
      c (1 - c (↑t⁻¹ : R)) • vecMulVec (fun i => c (Y i)) (-(X ᵥ* J)) := by
    rw [← hu, ← hw]
    ext i j
    by_cases h : i = j <;> simp [torusMat, Matrix.map_apply, vecMulVec_apply, one_apply, h]
  have htr : (torusMat c J X Y t)ᵀ = 1 + ((t : R) - 1) • vecMulVec (J *ᵥ fun i => c (Y i)) X +
      (1 - c (↑t⁻¹ : R)) • vecMulVec (J *ᵥ fun i => c (X i)) Y := by
    simp [torusMat, transpose_add, transpose_smul, transpose_vecMulVec]
  have d1 : (X ᵥ* J) ⬝ᵥ (fun i => c (X i)) = 0 := by rw [← dotProduct_mulVec]; exact hXX
  have d2 : (X ᵥ* J) ⬝ᵥ (fun i => c (Y i)) = 1 := by rw [← dotProduct_mulVec]; exact hXY
  have d3 : (Y ᵥ* J) ⬝ᵥ (fun i => c (X i)) = -1 := by rw [← dotProduct_mulVec]; exact hyx
  have d4 : (Y ᵥ* J) ⬝ᵥ (fun i => c (Y i)) = 0 := by rw [← dotProduct_mulVec]; exact hYY
  rw [hmap, htr]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
    vecMulVec_neg, Matrix.mul_neg, Matrix.neg_mul, smul_neg]
  simp only [vecMulVec_mul, mul_vecMulVec, vmv_mulVec, vecMul_vecMulVec, d1, d2, d3, d4, smul_vecMulVec, vecMulVec_smul,
    vecMulVec_neg, dotProduct_neg, dotProduct_smul, neg_dotProduct, smul_dotProduct]
  simp only [vecMulVec_smul, smul_vecMulVec, vecMulVec_neg, zero_smul, vecMulVec_zero, smul_zero, add_zero, zero_add, one_smul,
    neg_smul, smul_neg, smul_smul, neg_neg, map_sub, map_one, hc]
  match_scalars <;> first | linear_combination ht | linear_combination -ht | linear_combination hct |
    linear_combination -hct | ring1

end Props

end GlobalTheory.LeviTorus

namespace GlobalTheory.LeviTorus

open Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigma_invol {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2 τ, h.2.2.2 τ, star_star]

theorem cA_invol {σ : E →ₐ[F] E} (h : ∀ x, σ (σ x) = x) (a : AE F E) : cA σ (cA σ a) = a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [cA, h]
  | add a b ha hb => simp [map_add, ha, hb]

theorem cA_incl (σ : E →ₐ[F] E) (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [cA, inclR]

theorem form_incl (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    incV F x ⬝ᵥ incM F J *ᵥ (fun i => cA σ (incV F y i)) = inclR (F := F) (AF F) (form σ J x y) := by
  simp [form, incV, incM, cA_incl, dotProduct, mulVec, map_sum, map_mul]

theorem vecMul_incM (σ : E →ₐ[F] E) {n k : ℕ} (J : Matrix (Fin n) (Fin n) E) (A : Matrix (Fin n) (Fin k) E) (y : Fin n → E) :
    (incM F J *ᵥ fun i => cA σ (incV F y i)) ᵥ* incM F A =
      fun j => inclR (F := F) (AF F) (form σ J (A *ᵥ Pi.single j 1) y) := by
  funext j
  rw [← form_incl]
  simp only [vecMul, dotProduct, incV, incM, Matrix.map_apply, mulVec_single_one]
  exact Finset.sum_congr rfl fun k _ => by rw [mul_comm]; rfl

end GlobalTheory.LeviTorus

theorem GlobalTheory.LeviTorus.exists_levi : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ →
      ∀ t : (AE F E)ˣ, ∃ m : UA σ W.J, IsLevi (W₁ := W₁) H' t 1 m := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hA _ t
  have hσ := GlobalTheory.LeviTorus.sigma_invol hP.base.cm
  have hc : ∀ a : AE F E, (cA σ).toRingHom ((cA σ).toRingHom a) = a := GlobalTheory.LeviTorus.cA_invol hσ
  have hJ : ∀ i j, (cA σ).toRingHom (incM F W.J j i) = -incM F W.J i j := by
    intro i j
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, incM, Matrix.map_apply, GlobalTheory.LeviTorus.cA_incl, hP.skew.skew i j, map_neg]
  have hXX : incV F H'.x ⬝ᵥ incM F W.J *ᵥ (fun i => (cA σ).toRingHom (incV F H'.x i)) = 0 := by
    rw [show (fun i => (cA σ).toRingHom (incV F H'.x i)) = fun i => cA σ (incV F H'.x i) from rfl,
      GlobalTheory.LeviTorus.form_incl, hA.xx, map_zero]
  have hYY : incV F H'.y ⬝ᵥ incM F W.J *ᵥ (fun i => (cA σ).toRingHom (incV F H'.y i)) = 0 := by
    rw [show (fun i => (cA σ).toRingHom (incV F H'.y i)) = fun i => cA σ (incV F H'.y i) from rfl,
      GlobalTheory.LeviTorus.form_incl, hA.yy, map_zero]
  have hXY : incV F H'.x ⬝ᵥ incM F W.J *ᵥ (fun i => (cA σ).toRingHom (incV F H'.y i)) = 1 := by
    rw [show (fun i => (cA σ).toRingHom (incV F H'.y i)) = fun i => cA σ (incV F H'.y i) from rfl,
      GlobalTheory.LeviTorus.form_incl, hA.xy, map_one]
  have h01 := GlobalTheory.LeviTorus.torus_mul_inv hc hJ hXY t hXX hYY
  have h10 : GlobalTheory.LeviTorus.torusMat (cA σ).toRingHom (incM F W.J) (incV F H'.x) (incV F H'.y) t⁻¹ *
      GlobalTheory.LeviTorus.torusMat (cA σ).toRingHom (incM F W.J) (incV F H'.x) (incV F H'.y) t = 1 :=
    by simpa only [inv_inv] using GlobalTheory.LeviTorus.torus_mul_inv hc hJ hXY t⁻¹ hXX hYY
  refine ⟨⟨⟨GlobalTheory.LeviTorus.torusMat (cA σ).toRingHom (incM F W.J) (incV F H'.x) (incV F H'.y) t, _, h01, h10⟩, ?_⟩, ?_, ?_, ?_⟩
  · exact GlobalTheory.LeviTorus.torus_unitary hc hJ hXY t hXX hYY
  · exact GlobalTheory.LeviTorus.torus_mulVec_x hXY t hXX
  · exact GlobalTheory.LeviTorus.torus_mulVec_y hc hJ hXY t hYY
  · have hu : (incM F W.J *ᵥ fun i => (cA σ).toRingHom (incV F H'.y i)) ᵥ* incM F H'.ι = 0 := by
      rw [show (fun i => (cA σ).toRingHom (incV F H'.y i)) = fun i => cA σ (incV F H'.y i) from rfl,
        GlobalTheory.LeviTorus.vecMul_incM]
      funext j
      rw [(hA.orth _).2, map_zero]; rfl
    have hw : (incM F W.J *ᵥ fun i => (cA σ).toRingHom (incV F H'.x i)) ᵥ* incM F H'.ι = 0 := by
      rw [show (fun i => (cA σ).toRingHom (incV F H'.x i)) = fun i => cA σ (incV F H'.x i) from rfl,
        GlobalTheory.LeviTorus.vecMul_incM]
      funext j
      rw [(hA.orth _).1, map_zero]; rfl
    show GlobalTheory.LeviTorus.torusMat (cA σ).toRingHom (incM F W.J) (incV F H'.x) (incV F H'.y) t * incM F H'.ι =
      incM F H'.ι * 1
    rw [Matrix.mul_one]
    exact GlobalTheory.LeviTorus.torus_mul_of hc hJ hXY t _ hu hw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceEqualityOfGeomExpansion
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TraceEqTwo

theorem traceEq_of_geomExpansion : GeomExpansion → TraceEq := by
  intro hG D V lam S M T U μa μf μ _ _ fa ff hTD V' hr S' M' hlam' j hj μa' μ' _ _ fa' hR' hA'
  obtain ⟨-, hTU⟩ := GlobalTheory.T.testFunctions_transport_localLatticeIsometries D V V' hr j hj
  obtain ⟨T', U', hNF, hTF⟩ := hTU T U
  obtain ⟨hodd, hgap, hMl, hnf, hRP, hTA, hTFin⟩ := hTD
  set lam' : D.what₂.Tau → Fin V'.rank → ℤ := fun ρ i => lam ρ (i.cast hr) with hlamdef
  have hTD' : IsTestData V' lam' M' T' U' μa' (fun v => (μf v).map (j v)) μ' fa' (transfer j ff) := by
    refine ⟨hr ▸ hodd, ?_, hlam', hNF hnf, hR', hA', hTF μf ff hTFin⟩
    intro ρ i k hik
    have h := hgap ρ (i.cast hr) (k.cast hr) (by simpa using hik)
    simpa [hr, lam'] using h
  choose dta dtf dt hdt using fun (r : ℕ) (P : PPol D.sp.cm.sig r) => GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots.exists_isTorusMeas P
  obtain ⟨hFin, -, hTr⟩ := hG D V lam S M T U μa μf μ fa ff ⟨hodd, hgap, hMl, hnf, hRP, hTA, hTFin⟩
    (dta _) (dtf _) (dt _) (hdt _)
  obtain ⟨hFin', -, hTr'⟩ := hG D V' lam' S' M' T' U' μa' _ μ' fa' _ hTD' (dta _) (dtf _) (dt _) (hdt _)

  have gen : ∀ (r : ℕ) (h : r = V.rank),
      (∀ (P : PPol D.sp.cm.sig r) v, PhiOK (J := V.gram) (μf v) (dtf r P v) (ff v)) ∧
      ∑ᶠ P : PPol D.sp.cm.sig r, ((GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots.torVol P (dt r P)).toReal : ℂ) *
          (∏ᶠ v, Phi (J := V.gram) (μf v) (dtf r P v) (ff v)) *
          ∏ ρ : D.what₂.Tau, PhiReal P (embOverOf D ρ) (fun i => lam ρ (i.cast h)) (dta r P (placeOf D ρ)) =
        ∑ᶠ P, GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots.term V lam μf ff P (dta _ P) (dtf _ P) (dt _ P) := by
    intro r h
    subst h
    exact ⟨fun P v => (hFin P).2.1 v, rfl⟩
  refine ⟨_, hTr, ?_⟩
  convert hTr' using 1
  rw [← (gen _ hr).2]
  refine finsum_congr fun P => ?_
  unfold GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots.term
  congr 2
  refine finprod_congr fun v => ?_
  exact (GlobalTheory.T.stableOrbitalIntegral_preserved_latticeIsometry D V V' _ P v (j v) (hj v) (μf v) (dtf _ P v) (ff v) (hRP.2.1 v) ((hdt _ P).2.1 v) ((gen _ hr).1 P v) ((hFin' P).2.1 v)).symm

end GlobalTheory.TraceEqTwo

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralUnitGLEqHermitianLatticeCoStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedOrbitalIntegral_unitGL_eq_hermitianLatticeCount : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (a : ℕ) (B : GlobalTheory.UnitLemma.InvAlg K), B.P.Separable → ∀ (β : B.Aˣ) (ε : B.A), (ε = 1 ∨ ε = -1) → B.σ (β : B.A) = β * (ε * B.g) → ∀ (b : Module.Basis (Fin a) K.E B.A) (δ : GLw a w), (∀ i j, ((δ.val * GlobalTheory.Tw.Phi a (w.adicCompletion E))⁻¹)ᵀ i j = e (B.herm β (b i) (b j))) → twOrb (thL a w) (GlobalTheory.LFun.KGL w a) δ ((GlobalTheory.LFun.KGL w a : Set (GLw a w)).indicator 1) = ((GlobalTheory.UnitLemma.orbSum K.O B.T {L : Submodule K.O B.A | GlobalTheory.UnitLemma.IsLat K.O K.E L ∧ ∀ z, z ∈ L ↔ ∀ y ∈ L, B.herm β y z ∈ (algebraMap K.O K.E).range} (fun _ => 1) : ℚ) : ℂ) := by
  first | exact @GlobalTheory.TwOrbLat.twOrb_unit_eq_orbSum | exact GlobalTheory.TwOrbLat.twOrb_unit_eq_orbSum | (intros; apply GlobalTheory.TwOrbLat.twOrb_unit_eq_orbSum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFromBlocksNegOfDiagBasisTransportStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_fromBlocks_neg_of_diag_basis_transport : ∀ (A O : Type) [CommRing A] [CommRing O] (ι : O →ₙ+* A) (γ : A →+* A) (c : O →+* O) (n : ℕ)
    (P K : Matrix (Fin n) (Fin n) A) (JL : Matrix (Fin n) (Fin n) O),
    Function.Injective ι → (∀ x, γ (ι x) = ι (c x)) → Pᵀ * K * P.map γ = JL.map ι →
    ∀ (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) A) (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O),
    Mᵀ * Matrix.fromBlocks K 0 0 (-K) * M.map γ = Matrix.fromBlocks K 0 0 (-K) →
    M * Matrix.fromBlocks P 0 0 P = Matrix.fromBlocks P 0 0 P * G.map ι →
    Gᵀ * Matrix.fromBlocks JL 0 0 (-JL) * G.map c = Matrix.fromBlocks JL 0 0 (-JL) := by
  first | exact @GlobalTheory.fromBlocks_unitary_transfer | exact GlobalTheory.fromBlocks_unitary_transfer | (intros; apply GlobalTheory.fromBlocks_unitary_transfer <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeOperatorCommuteWeightVectorFunctionEStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryHeckeOperator_commute_weightVectorFunction_explicit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)) (f : ∀ w : Pl E, UL n w → ℂ) (F : finU E n → Module.Dual ℂ (Wsp lam)) (w : Wsp lam), hop S K' f (phiFun lam F w) = phiFun lam (hopM S lam K' f F) w := by
  first | exact @GlobalTheory.BCT.TrKer.hop_phiFun_comm | exact GlobalTheory.BCT.TrKer.hop_phiFun_comm | (intros; apply GlobalTheory.BCT.TrKer.hop_phiFun_comm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeOperatorVectorMemLevelFunctionsStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryHeckeOperatorVector_mem_levelFunctions : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → ∀ F ∈ vecM S lam K', hopM S lam K' f F ∈ vecM S lam K' := by
  first | exact @GlobalTheory.BCT.TrKer.HopStab.hopM_mem_vecM | exact GlobalTheory.BCT.TrKer.HopStab.hopM_mem_vecM | (intros; apply GlobalTheory.BCT.TrKer.HopStab.hopM_mem_vecM <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryToDoubledFirstFactorBigCellInertPlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryToDoubledFirstFactor_bigCell_inertPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v,
    (∃ M : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E), (1 + mat k) * M = 1 ∧ M * (1 + mat k) = 1 ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) →
    ∃ n ∈ GlobalTheory.InertDbl.NabD σ G.W v, ∃ p ∈ GlobalTheory.InertDbl.ParD σ G.W v, GlobalTheory.InertDbl.inlD σ G.W k = n * p := by
  first | exact @GlobalTheory.InertBigCell.inlD_bigCell | exact GlobalTheory.InertBigCell.inlD_bigCell | (intros; apply GlobalTheory.InertBigCell.inlD_bigCell <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightUpperUnitriangularIdempotentIndepCharacterStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_upperUnitriangularIdempotent_indep_character : ∀ (D : D7) (k : Fin 2) (ψ ψ' : AddChar (ZMod (D.host.g k)) ℂ), ψ ≠ 1 → ψ' ≠ 1 → ∀ f, wtOf D k (eUk D k ψ) f = wtOf D k (eUk D k ψ') f := by
  first | exact @GlobalTheory.BadCount.wtOf_eUk_indep | exact GlobalTheory.BadCount.wtOf_eUk_indep | (intros; apply GlobalTheory.BadCount.wtOf_eUk_indep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilSymplecticFormFrameCoordinatesEqLocalTraceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_symplectic_form_frame_coordinates_eq_local_trace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (v : Pl F) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σL : L →+* L) (q : ℕ) (δ : L) (ψL : AddChar L ℂ) (ι : L →+ AE F E),
      Formalism.UG.IsUnramInv ϖ σL q → (Valued.v δ = 1 ∧ σL δ = -δ) → Function.Injective ι → (∀ z : AE F E, At (evFin F v) z ↔ ∃ x, ι x = z) → (∀ x y, ι (x * y) = ι x * ι y) → (∀ x, ι (σL x) = cA σ (ι x)) →
      (∀ x, B.ψ (Algebra.trace (AF F) (AE F E) (ι x)) = ψL (x + σL x)) →
      ∀ (PV JS : GL (Fin n) L) (PW JT : GL (Fin d) L),
        ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = GlobalTheory.InertLocFrame.gram σL ι PV X.J →
        (JT : Matrix (Fin d) (Fin d) L) = -δ⁻¹ • (GlobalTheory.InertLocFrame.gram σL ι PW W.J)ᵀ →
        ∀ x y, B.ψ (⅟(2 : AF F) * symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)
            (GlobalTheory.InertLocFrame.xm ι PV PW x) (GlobalTheory.InertLocFrame.xm ι PV PW y)) =
          ψL ((GlobalTheory.Hk3.locH σL δ JS JT x y + σL (GlobalTheory.Hk3.locH σL δ JS JT x y)) / 2) := by
  first | exact @GlobalTheory.InertLocSymp.psi_symp_eq | exact GlobalTheory.InertLocSymp.psi_symp_eq | (intros; apply GlobalTheory.InertLocSymp.psi_symp_eq <;> assumption)
end

