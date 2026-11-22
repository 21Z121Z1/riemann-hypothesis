import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0749
import Formalism.LocalToGlobal.Columns.MtAdWt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0938
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0747
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0684
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAdmissibleFanOfCellMultOneCMField
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0742
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0733
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HodgeGramEqRiemann
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricUniformisationSmoothOnInterior
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0065
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0728
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0566
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0028
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0011
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0018
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MatchingMatricesOfBaseChangeRepresentation
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

open Formalism.L2.DIV GlobalTheory.CoefModel

namespace GlobalTheory.BcMatch

theorem bcmatch_main : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {K K' : Type} [Field K] [Field K'] (f : K →+* K') (e : K' →+* ℂ) {W₀ W W' : Type} [AddCommGroup W₀] [Module K W₀] [AddCommGroup W] [Module K' W] [AddCommGroup W'] [Module ℂ W'] (ρ₀ : Representation K (GQ L n) W₀) (ρ : Representation K' (GQ L n) W) (ρ' : Representation ℂ (GQ L n) W'), (∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (b₀ : Module.Basis ι K W₀) (b₁ : Module.Basis ι K' W), ∀ γ, LinearMap.toMatrix b₁ b₁ (ρ γ) = (LinearMap.toMatrix b₀ b₀ (ρ₀ γ)).map f) → GlobalTheory.LevCmp.WtMatch (e.comp f) ρ₀ ρ' → GlobalTheory.LevCmp.WtMatch e ρ ρ' := by
  intro L _ _ _ n K K' _ _ f e W₀ W W' _ _ _ _ _ _ ρ₀ ρ ρ' hb hm
  obtain ⟨ι, _, _, b₀, b₁, hb⟩ := hb
  obtain ⟨κ, _, _, c₀, c', hc⟩ := hm
  set P : Matrix ι κ K := b₀.toMatrix c₀ with hP
  set Q : Matrix κ ι K := c₀.toMatrix b₀ with hQ
  have hPQ : P * Q = 1 := Module.Basis.toMatrix_mul_toMatrix_flip b₀ c₀
  have hQP : Q * P = 1 := Module.Basis.toMatrix_mul_toMatrix_flip c₀ b₀
  have hPQf : P.map f * Q.map f = 1 := by rw [← Matrix.map_mul, hPQ, Matrix.map_one _ f.map_zero f.map_one]
  have hQPf : Q.map f * P.map f = 1 := by rw [← Matrix.map_mul, hQP, Matrix.map_one _ f.map_zero f.map_one]
  let std := Pi.basisFun K' κ
  let E : (κ → K') ≃ₗ[K'] W := LinearEquiv.ofLinear (Matrix.toLin std b₁ (P.map f)) (Matrix.toLin b₁ std (Q.map f))
    (by rw [← Matrix.toLin_mul, hPQf, Matrix.toLin_one])
    (by rw [← Matrix.toLin_mul, hQPf, Matrix.toLin_one])
  let d : Module.Basis κ K' W := std.map E
  have hd1 : b₁.toMatrix d = P.map f := by
    ext i j
    rw [Module.Basis.toMatrix_apply]
    have : d j = ∑ k, (P.map f) k j • b₁ k := by
      show E (std j) = _
      exact Matrix.toLin_self _ _ _ _
    rw [this, Module.Basis.repr_sum_self]
  have hd2 : d.toMatrix b₁ = Q.map f := by
    ext j i
    rw [Module.Basis.toMatrix_apply]
    simp [d, E, std, Matrix.toLin_self, Pi.single_apply]
  refine ⟨κ, inferInstance, inferInstance, d, c', fun γ => ?_⟩
  rw [hc γ, ← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix d b₁ d b₁ (ρ γ), hd1, hd2, hb γ,
    ← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix c₀ b₀ c₀ b₀ (ρ₀ γ), ← hP, ← hQ]
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_map, Matrix.map_map, Matrix.map_map]
  rfl

end GlobalTheory.BcMatch
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemParahoricOfScalarActionOnRamifiedParahoricFor
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.ParaRigid

theorem det_mem_of {K : Type} [Field K] (O : Subring K) {m : ℕ} (M : Matrix (Fin m) (Fin m) K)
    (hM : ∀ i j, M i j ∈ O) : M.det ∈ O := by
  have e : M = (Matrix.of fun i j => (⟨M i j, hM i j⟩ : O)).map O.subtype := by ext i j; rfl
  have h := RingHom.map_det O.subtype (Matrix.of fun i j => (⟨M i j, hM i j⟩ : O))
  rw [RingHom.mapMatrix_apply] at h
  rw [e, ← h]
  exact SetLike.coe_mem _

theorem inv_entry_mem {K : Type} [Field K] (O : Subring K) {m : ℕ} (x : GL (Fin m) K)
    (h1 : ∀ i j, x.1 i j ∈ O) (hd : (x.1.det)⁻¹ ∈ O) : ∀ i j, (x⁻¹).1 i j ∈ O := by
  intro i j
  rw [Matrix.coe_units_inv, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Matrix.adjugate_apply]
  refine O.mul_mem ?_ (det_mem_of O _ ?_)
  · rw [Ring.inverse_eq_inv']; exact hd
  · intro k l
    rw [Matrix.updateRow_apply]
    split_ifs
    · rw [Pi.single_apply]; split_ifs
      · exact O.one_mem
      · exact O.zero_mem
    · exact h1 k l

theorem mem_GLint_of {K : Type} [Field K] (O : Subring K) {m : ℕ} (x : GL (Fin m) K)
    (h1 : ∀ i j, x.1 i j ∈ O) (hd : (x.1.det)⁻¹ ∈ O) : x ∈ Formalism.UG.GLint (Fin m) O :=
  GlobalTheory.HeckeScalarSph.mem_GLint_iff.2 ⟨h1, inv_entry_mem O x h1 hd⟩

end GlobalTheory.ParaRigid

namespace GlobalTheory.ParaRigid

variable {K : Type} [Field K] {m : ℕ}

def colVecAt (j : Fin m) (t : K) : Matrix (Fin m) Unit K := Matrix.of fun i _ => if i = j then t else 0

def rowVecAt (K : Type) [Field K] (i : Fin m) : Matrix Unit (Fin m) K := Matrix.of fun _ j => if j = i then 1 else 0

def Gmat (h : Matrix (Fin m) (Fin m) K) (i0 j0 : Fin m) (t : K) : Matrix (Fin m) (Fin m) K :=
  1 + (h * colVecAt j0 t) * rowVecAt K i0

def Pmat (h : Matrix (Fin m) (Fin m) K) (i0 j0 : Fin m) (t : K) : Matrix (Fin m) (Fin m) K :=
  1 + colVecAt j0 t * (rowVecAt K i0 * h)

theorem det_G (h : Matrix (Fin m) (Fin m) K) (i0 j0 : Fin m) (t : K) :
    (Gmat h i0 j0 t).det = 1 + h i0 j0 * t := by
  rw [Gmat, Matrix.det_one_add_mul_comm, Matrix.det_unique]
  simp [colVecAt, rowVecAt, Matrix.mul_apply]
  done

theorem det_P (h : Matrix (Fin m) (Fin m) K) (i0 j0 : Fin m) (t : K) :
    (Pmat h i0 j0 t).det = 1 + h i0 j0 * t := by
  rw [Pmat, Matrix.det_one_add_mul_comm, Matrix.det_unique]
  simp [colVecAt, rowVecAt, Matrix.mul_apply]
  done

theorem G_apply (h : Matrix (Fin m) (Fin m) K) (i0 j0 : Fin m) (t : K) (i j : Fin m) :
    Gmat h i0 j0 t i j = (1 : Matrix (Fin m) (Fin m) K) i j + if j = i0 then h i j0 * t else 0 := by
  simp [Gmat, colVecAt, rowVecAt, Matrix.mul_apply]
  done

theorem P_apply (h : Matrix (Fin m) (Fin m) K) (i0 j0 : Fin m) (t : K) (i j : Fin m) :
    Pmat h i0 j0 t i j = (1 : Matrix (Fin m) (Fin m) K) i j + if i = j0 then t * h i0 j else 0 := by
  simp [Pmat, colVecAt, rowVecAt, Matrix.mul_apply]
  done

theorem conj_G (h h' : Matrix (Fin m) (Fin m) K) (hh : h' * h = 1) (i0 j0 : Fin m) (t : K) :
    h' * Gmat h i0 j0 t * h = Pmat h i0 j0 t := by
  simp only [Gmat, Pmat, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ← Matrix.mul_assoc, hh, Matrix.one_mul]

end GlobalTheory.ParaRigid

namespace GlobalTheory.ParaRigid

variable {K : Type} [Field K] {m : ℕ}

theorem detDD_G (h : Matrix (Fin m) (Fin m) K) (i0 j0 : Fin m) (t : K) (r : ℕ) (hi0 : r ≤ i0.val) :
    (Matrix.of fun a b : {x : Fin m // r ≤ x.val} => Gmat h i0 j0 t a.1 b.1).det = 1 + h i0 j0 * t := by
  have e : (Matrix.of fun a b : {x : Fin m // r ≤ x.val} => Gmat h i0 j0 t a.1 b.1) =
      1 + ((Matrix.of fun a (_ : Unit) => h a.1 j0 * t : Matrix {x : Fin m // r ≤ x.val} Unit K) *
        (Matrix.of fun (_ : Unit) b => if b = ⟨i0, hi0⟩ then 1 else 0 : Matrix Unit {x : Fin m // r ≤ x.val} K)) := by
    ext a b
    simp [G_apply, Matrix.one_apply, Matrix.mul_apply, Subtype.ext_iff]
  rw [e, Matrix.det_one_add_mul_comm, Matrix.det_unique]
  simp [Matrix.mul_apply]

theorem detDD_P (h : Matrix (Fin m) (Fin m) K) (i0 j0 : Fin m) (t : K) (r : ℕ) (hj0 : j0.val < r) :
    (Matrix.of fun a b : {x : Fin m // r ≤ x.val} => Pmat h i0 j0 t a.1 b.1).det = 1 := by
  have e : (Matrix.of fun a b : {x : Fin m // r ≤ x.val} => Pmat h i0 j0 t a.1 b.1) = 1 := by
    ext a b
    have ha : (a.1 : Fin m) ≠ j0 := fun e => by have := a.2; rw [e] at this; omega
    simp [P_apply, Matrix.one_apply, Subtype.ext_iff, ha]
  rw [e, Matrix.det_one]

end GlobalTheory.ParaRigid

namespace GlobalTheory.ParaRigid

theorem mem_para_of_eig : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (r : ℕ) (s : SplitPlace L) (V : Type) [AddCommGroup V] [Module ℂ V] (F : GAf L n → V) (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (a : s.v.adicCompletion (maximalRealSubfield L)), F ≠ 0 → Valued.v a = 1 → (∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ NG.ParaRT s r (s.loc n κ))) → (∀ κ : J, Eig F κ (χ κ : ℂˣ)) → (∀ κ (h : κ ∈ J), TrivOutside {s.v} κ → NG.detDD s r (s.loc n κ) = 1 → χ ⟨κ, h⟩ = 1) → (∀ κ (h : κ ∈ J), TrivOutside {s.v} κ → NG.detDD s r (s.loc n κ) = a → χ ⟨κ, h⟩ ≠ 1) → ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → (∃ c, Eig F κ c) → NG.ParaRT s r (s.loc n κ) := by
  intro L _ _ _ n r s V _ _ F J χ a hF ha hJ hEig h1 ha' κ hκU hκT hc
  obtain ⟨c, hc⟩ := hc
  classical
  set O := (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring with hO
  have hOv : ∀ x, x ∈ O ↔ Valued.v x ≤ 1 := fun x => by
    rw [hO, ValuationSubring.mem_toSubring, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
  have hint := (GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff s hκT).2 hκU
  refine ⟨hint, ?_⟩
  by_contra hcon
  push_neg at hcon
  obtain ⟨i0, j0, hi0, hj0, hv⟩ := hcon
  set h := s.loc n κ with hh
  have hent : ∀ i j, Valued.v (h.val i j) ≤ 1 := fun i j =>
    (hOv _).1 ((GlobalTheory.HeckeScalarSph.mem_GLint_iff.1 hint).1 i j)
  have hv1 : Valued.v (h.val i0 j0) = 1 := le_antisymm (hent i0 j0) hv
  have hne : h.val i0 j0 ≠ 0 := by
    intro e; rw [e, map_zero] at hv1; exact zero_ne_one hv1
  have ha0 : a ≠ 0 := by
    intro e; rw [e, map_zero] at ha; exact zero_ne_one ha
  set t := (a - 1) / h.val i0 j0 with ht
  have htv : Valued.v t ≤ 1 := by
    rw [ht, map_div₀, hv1, div_one]
    refine (Valuation.map_sub _ _ _).trans (max_le ha.le (by rw [map_one]))
  have hth : 1 + h.val i0 j0 * t = a := by rw [ht]; field_simp; ring
  have hdinv : a⁻¹ ∈ O := by rw [hOv, map_inv₀, ha, inv_one]
  have hone : ∀ i j, Valued.v ((1 : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j) ≤ 1 := by
    intro i j
    rw [Matrix.one_apply]; split_ifs
    · rw [map_one]
    · rw [map_zero]; exact zero_le'
  have hGint : ∀ i j, Gmat h.val i0 j0 t i j ∈ O := by
    intro i j
    rw [hOv, G_apply]
    refine (Valuation.map_add _ _ _).trans (max_le (hone i j) ?_)
    split_ifs
    · rw [map_mul]; exact mul_le_one' (hent _ _) htv
    · rw [map_zero]; exact zero_le'
  have hPint : ∀ i j, Pmat h.val i0 j0 t i j ∈ O := by
    intro i j
    rw [hOv, P_apply]
    refine (Valuation.map_add _ _ _).trans (max_le (hone i j) ?_)
    split_ifs
    · rw [map_mul]; exact mul_le_one' htv (hent _ _)
    · rw [map_zero]; exact zero_le'
  have hdG : (Gmat h.val i0 j0 t).det = a := by rw [det_G, hth]
  have hdP : (Pmat h.val i0 j0 t).det = a := by rw [det_P, hth]
  let Gg := Matrix.GeneralLinearGroup.mkOfDetNeZero (Gmat h.val i0 j0 t) (by rw [hdG]; exact ha0)
  have hGg : Gg.val = Gmat h.val i0 j0 t := rfl
  obtain ⟨g, ⟨hgT, hgl⟩, -⟩ := (GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s).2.2 Gg
  set p := κ⁻¹ * g * κ with hp
  have hpT : TrivOutside {s.v} p :=
    GlobalTheory.HeckeScalarSph.triv_mul (GlobalTheory.HeckeScalarSph.triv_mul (GlobalTheory.HeckeScalarSph.triv_inv hκT) hgT) hκT
  have hinv : (h⁻¹).val * h.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hpl : (s.loc n p).val = Pmat h.val i0 j0 t := by
    rw [hp, map_mul, map_mul, map_inv, hgl, ← hh, Units.val_mul, Units.val_mul, hGg]
    exact conj_G h.val (h⁻¹).val hinv i0 j0 t
  have hgl' : (s.loc n g).val = Gmat h.val i0 j0 t := by rw [hgl]; exact hGg
  have hgP : NG.ParaRT s r (s.loc n g) := by
    refine ⟨mem_GLint_of O _ (fun i j => by rw [hgl']; exact hGint i j) (by rw [hgl', hdG]; exact hdinv), ?_⟩
    intro i j hi hj
    have hji : j ≠ i0 := fun e => by rw [e] at hj; omega
    have hij : i ≠ j := fun e => by rw [e] at hi; omega
    rw [hgl', G_apply, if_neg hji, Matrix.one_apply_ne hij, add_zero, map_zero]
    exact zero_lt_one
  have hpP : NG.ParaRT s r (s.loc n p) := by
    refine ⟨mem_GLint_of O _ (fun i j => by rw [hpl]; exact hPint i j) (by rw [hpl, hdP]; exact hdinv), ?_⟩
    intro i j hi hj
    have hij0 : i ≠ j0 := fun e => by rw [e] at hi; omega
    have hij : i ≠ j := fun e => by rw [e] at hi; omega
    rw [hpl, P_apply, if_neg hij0, Matrix.one_apply_ne hij, add_zero, map_zero]
    exact zero_lt_one
  have hgJ : g ∈ J := (hJ g hgT).2 hgP
  have hpJ : p ∈ J := (hJ p hpT).2 hpP
  have hχg : χ ⟨g, hgJ⟩ ≠ 1 := ha' g hgJ hgT (by unfold NG.detDD; simp only [hgl']; rw [detDD_G _ _ _ _ r hi0, hth])
  have hχp : χ ⟨p, hpJ⟩ = 1 := h1 p hpJ hpT (by unfold NG.detDD; simp only [hpl]; rw [detDD_P _ _ _ _ r hj0])
  have eg := hEig ⟨g, hgJ⟩
  have ep := hEig ⟨p, hpJ⟩
  rw [hχp] at ep
  have hkp : κ * p = g * κ := by rw [hp]; group
  obtain ⟨x0, hx0⟩ : ∃ x, F x ≠ 0 := by
    by_contra hn; push_neg at hn; exact hF (funext hn)
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hx0
    have := hc (x0 * κ⁻¹)
    rwa [inv_mul_cancel_right, zero_smul] at this
  have key : ∀ x, c • ((χ ⟨g, hgJ⟩ : ℂˣ) : ℂ) • F x = c • F x := by
    intro x
    have e1 := hc (x * g)
    have e2 := ep (x * κ)
    rw [eg x] at e1
    rw [mul_assoc, hkp, ← mul_assoc, e1, hc x] at e2
    simpa using e2
  apply hχg
  have k0 := key x0
  rw [smul_smul, ← sub_eq_zero, ← sub_smul, smul_eq_zero] at k0
  rcases k0 with k0 | k0
  · apply Units.ext
    have : c * (((χ ⟨g, hgJ⟩ : ℂˣ) : ℂ) - 1) = 0 := by rw [mul_sub, mul_one]; exact k0
    rcases mul_eq_zero.1 this with h' | h'
    · exact absurd h' hc0
    · simpa [sub_eq_zero] using h'
  · exact absurd k0 hx0

end GlobalTheory.ParaRigid
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MumfordGoodGrowthBoundFrameChangeOrthogonalSummaStatement
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordGoodGrowthBound_frameChange_orthogonalSummands : ∀ (n g : ℕ) (S : Finset (Fin n)) (W : Set (ReciprocityTheory.L2DbarEstimates.V n)) (G₀ : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin g) (Fin g) ℂ) (c : ℝ) (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (m : ι → ℕ) (Q : ∀ τ : ι, ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin (m τ)) (Fin g) ℂ) (r : ℝ), IsOpen W → 0 < r → (∀ τ i k, DifferentiableOn ℂ (fun u => Q τ u i k) (Metric.ball 0 r)) → Fintype.card (Σ τ, Fin (m τ)) = g → LinearIndependent ℂ (fun p : Σ τ, Fin (m τ) => Q p.1 0 p.2) → (∀ v ∈ W, (G₀ v).det ≠ 0 ∧ (∀ i k, ContDiffAt ℝ 2 (fun u => G₀ u i k) v) ∧ GlobalTheory.GoodMetric.GoodBound S c N G₀ v) → (∀ v ∈ W, ∀ τ τ', τ ≠ τ' → Q τ v * G₀ v * (Q τ' v)ᴴ = 0) → ∃ r' : ℝ, 0 < r' ∧ ∃ (c' : ℝ) (N' : ℕ), ∀ v ∈ W, ‖v‖ < r' → ∀ τ, GlobalTheory.GoodMetric.GoodBound S c' N' (fun u => Q τ u * G₀ u * (Q τ u)ᴴ) v := by
  first | exact @GlobalTheory.FrameGood.frame_summands_goodBound | exact GlobalTheory.FrameGood.frame_summands_goodBound | (intros; apply GlobalTheory.FrameGood.frame_summands_goodBound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NatCardTorsionQuotSpanDvdOfRangeSubsetStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.natCard_torsion_quot_span_dvd_of_range_subset' : ∀ (L : Type) [AddCommGroup L] {m n : ℕ} (δ : Fin m → L) (γ : Fin n → L), LinearIndependent ℤ δ →
    Set.range γ ⊆ Set.range δ →
    Nat.card (Submodule.torsion ℤ (L ⧸ Submodule.span ℤ (Set.range γ))) ∣
      Nat.card (Submodule.torsion ℤ (L ⧸ Submodule.span ℤ (Set.range δ))) := by
  first | exact @GlobalTheory.natCard_torsion_quot_span_dvd_of_range_subset | exact GlobalTheory.natCard_torsion_quot_span_dvd_of_range_subset | (intros; apply GlobalTheory.natCard_torsion_quot_span_dvd_of_range_subset <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyAgreeRealOfReadGalois
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.HeightCounting.Up.RealOfReading

open Formalism.BasicNotions.TH

namespace GlobalTheory.HeightCounting.Up.StandardFrameAgreement

theorem stdFrame_iff {D : D7} {V : HSp D} {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n) :
    R3.StdFrame hF P ↔ GlobalTheory.NJoin.StdFrame hF P := by
  have key : ∀ {E : Type} [Field E] [NumberField E] {F1 F2 : Subfield E} (h : F1 = F2),
      R3.swapCast h = principalLevelFrame.tensCastR h := by
    intro E _ _ F1 F2 h
    subst h
    rfl
  unfold R3.StdFrame GlobalTheory.NJoin.StdFrame principalLevelFrame.StdPsi
  rw [key hF]

set_option maxHeartbeats 1000000 in

theorem agree_of_layer : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ T w Z Wt _ t nch n c => ∀ (hC : t.r.z.R.C = TC.cf w.I w.l Z) (Xd : DivX (w.D Z)) (E : EigIdx (w.D Z) Xd) (labPi : E.Pi → (famR (w.st Z) w.I t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr).A.fam.base.Ix) hb htup hg hf, Nonempty (GlobalTheory.NJoin.Agree (realOfRead t.r.z.R.toRealDat t.r.z.F.lv2 t.r.Y n.tp hC Xd E labPi hb htup hg hf) c.a.all.gal.mt (realOfRead t.r.z.R.toRealDat t.r.z.F.lv2 t.r.Y n.tp hC Xd E labPi hb htup hg hf).rep) := by
  intro _ hL
  refine ⟨1, one_pos, fun eps C8 C5 c6 Cb _ _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C _ _ _ =>
    ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨0, fun K _ _ _ _ _ _ => ?_⟩⟩⟩⟩⟩
  refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, by simp, by simp, fun B f T _ _ _ _ => ?_⟩
  intro _ w Z Wt p0 t nch n xd c hNE _ _ hC Xd E labPi hb htup hg hf
  obtain ⟨m⟩ := hNE
  have ad := m.ad
  refine ⟨⟨t.r.Y.hF, ad.PV, fun j => (stdFrame_iff _ _).1 (ad.std j), fun j => (stdFrame_iff _ _).1 (t.r.Y.stdPsi.2 j),
    fun _ => 1, ?_, fun μ hμ j => (ad.eW μ hμ j).symm, ?_, ?_, fun σ => ?_⟩⟩
  · intro j h
    simp only [inv_one, one_mul, mul_one]
    exact ad.rat j h
  · intro μ hμ j h γ hγ he v
    have he' := he
    simp only [inv_one, one_mul, mul_one] at he'
    have key := ad.wt μ hμ j h γ hγ he' ((ad.eW μ hμ j).symm v)
    refine (LinearEquiv.symm_apply_eq _).2 ?_
    refine Eq.trans ?_ key.symm
    exact congrArg _ (LinearEquiv.apply_symm_apply _ v).symm
  · intro μ hμ j x h
    refine (LinearEquiv.eq_symm_apply _).2 ?_
    refine (ad.read μ hμ j x h).trans ?_
    simp only [inv_one, one_mul]
    rfl
  · exact Formalism.L2.NG.IsoRep.refl _

end GlobalTheory.HeightCounting.Up.StandardFrameAgreement
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormalisedReadingsRelatedLocalizedAdelicDataStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.Fin3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedReadings_related_localizedAdelicData : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (L : LocAll (lay0 (Dof x))) (m : Moved (oL x L)), m.z = datL x L → m.Coh → ∀ (s : Side0 (oL x L)) (r : ReadPk m s), r.Pin → ∀ Y : YT x L s.p0, HEq Y r.Y → YRel L Y := by
  first | exact @GlobalTheory.HeightCounting.Fin3.yRel_of_pin | exact GlobalTheory.HeightCounting.Fin3.yRel_of_pin | (intros; apply GlobalTheory.HeightCounting.Fin3.yRel_of_pin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrthonormalFramesLieCoordinatesUnitary
section
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.ShFam
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam

theorem lie_coord_unitary : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ r}, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (k : U.Comp) (x x₁ : (U.X k).dom), IsOrth (U.X k) x.1 → IsOrth (U.X k) x₁.1 → (U.un k x₁).x = (U.un k x).x → ∀ (τ : E →+* ℂ) (T : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ), (∀ b, Formalism.L2.Pj.IsCombAt (U.un k x).x ((U.un k x).u τ) (show Fin (Dw.mult τ) → CAt σ from fun b' => (T b' b : ℂ)) ((U.un k x₁).u τ b)) → Tᴴ * T = 1 := by
  classical
  intro E _ _ _ H Dw l Xo c σ r U hσ hU k x x₁ hx hx₁ e τ T hT
  obtain ⟨W⟩ := GlobalTheory.ArcQ.nonempty_unfWit_of_isUnf E H Dw l Xo c σ r _ hU
  obtain ⟨d, hd0, hd⟩ := GlobalTheory.HodgeSmooth.exists_diag_riem hσ hU W
  obtain ⟨Hm, -, -, hH⟩ := (W.period k x₁).2.2.2.2
  obtain ⟨hPx, hv⟩ := W.lie k x₁
  have h1 := hd k x₁ hx₁ (W.ik k) (W.Pm k x₁) (W.period k x₁) Hm hH hPx.symm τ _ ((U.un k x₁).u τ) 1 (hv τ)
    (fun b => by
      convert GlobalTheory.isCombAt_single_of_isTanAt (U.un k x₁).x ((U.un k x₁).u τ) ((U.un k x₁).tan τ) b using 1
      show (fun b' => (1 : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ) b' b) = Pi.single b 1
      funext b'
      rw [Matrix.one_apply, Pi.single_apply])
  have h2 := hd k x hx (W.ik k) (W.Pm k x₁) (W.period k x₁) Hm hH (hPx.symm.trans e) τ _ ((U.un k x₁).u τ) T
    (hv τ) hT
  have h3 : d k τ • (Tᴴ * T) = d k τ • (1 : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ) := by
    rw [← h2, h1, conjTranspose_one, Matrix.mul_one]
  exact smul_right_injective _ (hd0 k τ) h3

end GlobalTheory.ShFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodMapMemberEqFramePeriodMapLinearChange
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

namespace GlobalTheory.PointLift

open ReciprocityTheory.ChartRestriction.G.FD

theorem pm_lift_pointwise : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (W : GlobalTheory.ArcQ.UnfWit U), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → Function.Injective W.ik → ∀ (k : U.Comp) (Q : (W.F.Di (W.ik k)).La →+ (Fin W.g → ℂ)), IsPeriod (W.F.Di (W.ik k)) (fun j => Formalism.L2.PjFree.relab c σ (W.e j).1) Q → ∀ q : FrPt Xo c (Formalism.L2.Pj.CAt σ), W.F.u (W.ik k) Q = q.x → ∃ x' : (U.X k).dom, (U.un k x').x = q.x ∧ ∃ h : (Fin W.g → ℂ) ≃ₗ[ℂ] (Fin W.g → ℂ), ∀ a, Q a = h (W.Pm k x' a) := by
  intro E _ _ _ H Dw l Xo c σ r U W hσ hU hinj k Q hQ q hq
  obtain ⟨k₁, x₁, t, hB⟩ := hU.2.2.1 q
  have hx₁ : (U.un k₁ x₁).x = W.F.u (W.ik k₁) (W.Pm k₁ x₁) := (W.lie k₁ x₁).1
  have hk : k₁ = k := hinj (W.F.disj _ _ _ _ (W.period k₁ x₁) hQ (by rw [← hx₁, ← hB.1, hq]))
  subst hk
  obtain ⟨gam, h, hEF, -, -, hgh⟩ := (W.F.fibre _ Q (W.Pm k₁ x₁) hQ (W.period k₁ x₁)).1
    (by rw [hq, ← hx₁, hB.1])
  let φL : (W.F.Di (W.ik k₁)).La →ₗ[𝓞 E] (Fin r → E) := (U.X k₁).Λ.subtype ∘ₗ (W.φ k₁).toLinearMap
  have hφi : Function.Injective φL := (U.X k₁).Λ.injective_subtype.comp (W.φ k₁).injective
  have hrange : Set.range φL = ((U.X k₁).Λ : Set (Fin r → E)) := by
    ext v
    constructor
    · rintro ⟨a, rfl⟩
      exact (W.φ k₁ a).2
    · intro hv
      exact ⟨(W.φ k₁).symm ⟨v, hv⟩, by simp [φL]⟩
  have hspan : Submodule.span E (Set.range φL) = ⊤ := by rw [hrange]; exact (U.X k₁).Λ_span
  have hcc : cc (-(U.X k₁).ξ0) = -(-(U.X k₁).ξ0) := by
    have h0 := (U.X k₁).ξ0_im
    unfold cc at h0 ⊢
    rw [map_neg, h0]
  have hl : Function.Injective φL ∧ Submodule.span E (Set.range φL) = ⊤ ∧
      (∀ a b, cc ((U.X k₁).Gm a b) = (U.X k₁).Gm b a) ∧ (U.X k₁).Gm.det ≠ 0 ∧
      ∀ x y, (((W.F.Di (W.ik k₁)).EF x y : ℤ) : ℚ) =
        Algebra.trace ℚ E (-(U.X k₁).ξ0 * herm (U.X k₁).Gm (φL x) (φL y)) :=
    ⟨hφi, hspan, (U.X k₁).Gm_herm, (U.X k₁).Gm_det, fun x y => W.iso k₁ x y⟩
  obtain ⟨γ, hγh, hγφ⟩ := GlobalTheory.IsoExt.exists_unitary_of_isometry E H _ _ r (-(U.X k₁).ξ0) (U.X k₁).Gm φL φL gam
    hcc hl hl hEF
  have hinv : ∀ v : Fin r → E, ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ
      ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have hinv' : ∀ v : Fin r → E, (γ : Matrix (Fin r) (Fin r) E) *ᵥ
      (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hγi : IsUStab (U.X k₁).Gm (U.X k₁).Λ γ⁻¹ := by
    refine ⟨fun u v => ?_, fun v => ⟨fun hv => ?_, fun hv => ?_⟩⟩
    · rw [← hγh, hinv', hinv']
    · obtain ⟨b, hb⟩ : v ∈ Set.range φL := by rw [hrange]; exact hv
      have e : ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v = φL (gam.symm b) := by
        rw [← hb, ← LinearEquiv.apply_symm_apply gam b, hγφ, hinv, LinearEquiv.apply_symm_apply]
      rw [e]
      exact (W.φ k₁ (gam.symm b)).2
    · obtain ⟨a, ha⟩ : _ ∈ Set.range φL := by rw [hrange]; exact hv
      have e : v = φL (gam a) := by rw [hγφ, ha, hinv']
      rw [e]
      exact (W.φ k₁ (gam a)).2
  let x' : (U.X k₁).dom := ⟨lact γ⁻¹ x₁.1, GlobalTheory.MajInv.lact_mem_dom _ hγi x₁.2⟩
  have hPm : ∀ a, W.Pm k₁ x' a = W.Pm k₁ x₁ (gam a) := by
    intro a
    funext j
    rw [W.Pm_eq, W.Pm_eq]
    have e : (W.φ k₁ a : Fin r → E) = ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ
        (W.φ k₁ (gam a) : Fin r → E) := by
      change φL a = _ *ᵥ φL (gam a)
      rw [hγφ, hinv]
    rw [e]
    exact GlobalTheory.CongrOrbit.perFr_lact _ _ _ hγi.1 _ _ _
  have hQx : ∀ a, W.Pm k₁ x' a = h (Q a) := fun a => by rw [hPm, hgh]
  have hu : W.F.u (W.ik k₁) Q = W.F.u (W.ik k₁) (W.Pm k₁ x') :=
    (W.F.fibre _ Q (W.Pm k₁ x') hQ (W.period k₁ x')).2
      ⟨LinearEquiv.refl _ _, h, fun a b => rfl, fun a _ => ⟨0, by simp⟩, fun a => ⟨0, by simp⟩,
        fun a => hQx a⟩
  refine ⟨x', by rw [(W.lie k₁ x').1, ← hu, hq], h.symm, fun a => ?_⟩
  rw [hQx, LinearEquiv.symm_apply_apply]

end GlobalTheory.PointLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowDepthOfPrimitiveStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.row_depth_of_primitive : PrN → AllSt fun _ _ _ _ _ _ x => RowDepth (Dof x) (repOf x.r.Y) := by
  first | exact @GlobalTheory.RowDepthTrue.rowDepth_allSt | exact GlobalTheory.RowDepthTrue.rowDepth_allSt | (intros; apply GlobalTheory.RowDepthTrue.rowDepth_allSt <;> assumption)
end

