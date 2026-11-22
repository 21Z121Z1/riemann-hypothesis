import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0273
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0266
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientHeightLowerBoundShortIsotropicVector
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0271
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0267
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0277
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0025
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0155
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0071
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0008
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0040
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0268
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetEqOfColsUnit
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.Chamber GlobalTheory.AdelicU GlobalTheory.TruncKer GlobalTheory.Orb
open Finset
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GramJacobi

theorem det_eq_of_cols_unit {n R : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (M : Matrix n n R) (p : n → Prop) [DecidablePred p]
    (h : ∀ i j, ¬ p j → M i j = (1 : Matrix n n R) i j) :
    M.det = (M.toSquareBlockProp p).det := by
  rw [← Matrix.det_transpose, Matrix.twoBlockTriangular_det (Matrix.transpose M) p]
  · have h1 : ((Matrix.transpose M).toSquareBlockProp fun i => ¬ p i) = 1 := by
      ext i j
      simp only [Matrix.toSquareBlockProp, Matrix.toBlock, Matrix.transpose_apply,
        Matrix.submatrix_apply]
      rw [h _ _ i.2, Matrix.one_apply, Matrix.one_apply]
      by_cases hij : i = j
      · subst hij; simp
      · rw [if_neg hij, if_neg (fun e => hij (Subtype.ext e.symm))]
    rw [h1, Matrix.det_one, mul_one, ← Matrix.det_transpose]
    rfl
  · intro i hi j hj
    rw [Matrix.transpose_apply, h _ _ hi, Matrix.one_apply_ne]
    rintro rfl
    exact hi hj

theorem jacobi_minor {n R : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (G H : Matrix n n R) (hHG : H * G = 1) (p : n → Prop) [DecidablePred p] :
    (H.toSquareBlockProp fun i => ¬ p i).det * G.det = (G.toSquareBlockProp p).det := by
  have hGH : G * H = 1 := mul_eq_one_comm.mp hHG
  let N : Matrix n n R := Matrix.of fun i j => if p j then (1 : Matrix n n R) i j else H i j
  have hN : N.det = (H.toSquareBlockProp fun i => ¬ p i).det := by
    rw [Matrix.twoBlockTriangular_det N p]
    · have h1 : N.toSquareBlockProp p = 1 := by
        ext i j
        simp only [N, Matrix.toSquareBlockProp, Matrix.toBlock, Matrix.submatrix_apply,
          Matrix.of_apply, if_pos j.2]
        rw [Matrix.one_apply, Matrix.one_apply]
        by_cases hij : i = j
        · subst hij; simp
        · rw [if_neg hij, if_neg (fun e => hij (Subtype.ext e))]
      have h2 : (N.toSquareBlockProp fun i => ¬ p i) = H.toSquareBlockProp fun i => ¬ p i := by
        ext i j
        simp only [N, Matrix.toSquareBlockProp, Matrix.toBlock, Matrix.submatrix_apply,
          Matrix.of_apply, if_neg j.2]
      rw [h1, h2, Matrix.det_one, one_mul]
    · intro i hi j hj
      simp only [N, Matrix.of_apply, if_pos hj]
      rw [Matrix.one_apply_ne]
      rintro rfl
      exact hi hj
  have hGN : (G * N).det = (G.toSquareBlockProp p).det := by
    rw [det_eq_of_cols_unit (G * N) p]
    · have : (G * N).toSquareBlockProp p = G.toSquareBlockProp p := by
        ext i j
        simp only [Matrix.toSquareBlockProp, Matrix.toBlock, Matrix.submatrix_apply,
          Matrix.mul_apply, N, Matrix.of_apply, if_pos j.2, Matrix.one_apply, mul_ite, mul_one,
          mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [this]
    · intro i j hj
      rw [← hGH]
      simp only [Matrix.mul_apply, N, Matrix.of_apply, if_neg hj]
  rw [← hN, mul_comm, ← Matrix.det_mul, hGN]

end GlobalTheory.GramJacobi

namespace GlobalTheory.GramJacobi

end GlobalTheory.GramJacobi

namespace GlobalTheory

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelParamShiftedWeightOfCoverDisc
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

noncomputable section

namespace GlobalTheory.ArchRec.Direct

def barRev {n : ℕ} (g : Mn n) : Mn n := (g.map (starRingEnd ℂ)).submatrix Fin.rev Fin.rev

theorem barRev_barRev {n : ℕ} (g : Mn n) : barRev (barRev g) = g := by
  ext i j
  simp [barRev]

theorem barRev_mul {n : ℕ} (g h : Mn n) : barRev (g * h) = barRev g * barRev h := by
  ext i j
  simp only [barRev, Matrix.submatrix_apply, Matrix.map_apply, Matrix.mul_apply, map_sum, map_mul]
  exact (Fintype.sum_equiv Fin.revPerm _ _ (fun x => by simp [Fin.revPerm_apply])).symm

theorem barRev_one {n : ℕ} : barRev (1 : Mn n) = 1 := by
  ext i j
  by_cases h : i = j
  · subst h; simp [barRev]
  · have h' : i.rev ≠ j.rev := fun h'' => h (Fin.rev_injective h'')
    simp [barRev, Matrix.one_apply, h, h']

theorem barRev_conjTranspose {n : ℕ} (g : Mn n) : barRev gᴴ = (barRev g)ᴴ := by
  ext i j
  simp [barRev, Matrix.conjTranspose_apply]

theorem barRev_Jm {n : ℕ} (ε : Fin n → Bool) : barRev (Formalism.REAL.Jm ε) = Formalism.REAL.Jm (fun a => ε a.rev) := by
  ext i j
  by_cases h : i = j
  · subst h
    by_cases hε : ε i.rev <;> simp [barRev, Formalism.REAL.Jm, hε]
  · have h' : i.rev ≠ j.rev := fun h'' => h (Fin.rev_injective h'')
    simp [barRev, Formalism.REAL.Jm, Matrix.diagonal_apply, h, h']

theorem barRev_mem_K {n : ℕ} {ε : Fin n → Bool} {g : Mn n} (hg : g ∈ Formalism.REAL.Kset ε) :
    barRev g ∈ Formalism.REAL.Kset (fun a => ε a.rev) := by
  simp only [Formalism.REAL.Kset, Set.mem_setOf_eq] at hg ⊢
  obtain ⟨hu, hc⟩ := hg
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff] at hu ⊢
    rw [Matrix.star_eq_conjTranspose, ← barRev_conjTranspose, ← barRev_mul, ← Matrix.star_eq_conjTranspose, hu,
      barRev_one]
  · rw [← barRev_Jm, ← barRev_mul, hc, barRev_mul]

theorem isKFin_barRev {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool)
    (σ : Mn n → (H →L[ℂ] H)) (x : H) :
    IsKFin (fun a => ε a.rev) (fun g => σ (barRev g)) x ↔ IsKFin ε σ x := by
  have hK : ∀ g ∈ Formalism.REAL.Kset (fun a => ε a.rev), barRev g ∈ Formalism.REAL.Kset ε := by
    intro g hg
    simpa only [Fin.rev_rev] using barRev_mem_K hg
  simp only [IsKFin, IsKStableOn]
  constructor
  · rintro ⟨S, hS, hx, hst⟩
    refine ⟨S, hS, hx, fun g hg v hv => ?_⟩
    simpa only [barRev_barRev] using hst (barRev g) (barRev_mem_K hg) v hv
  · rintro ⟨S, hS, hx, hst⟩
    exact ⟨S, hS, hx, fun g hg v hv => hst (barRev g) (hK g hg) v hv⟩

theorem isEnum_rev {n : ℕ} {S : SPar} {lam : Fin n → ℝ} {ε : Fin n → Bool} (h : IsEnum S lam ε) :
    IsEnum (dualPar S) (fun a => -lam a.rev) (fun a => ε a.rev) := by
  obtain ⟨hanti, r, hr, hS⟩ := h
  refine ⟨fun a b hab => ?_, fun a => -r a.rev, fun a => by simp [hr], ?_⟩
  · have hba : b.rev < a.rev := Fin.rev_lt_rev.mpr hab
    simpa using hanti hba
  · rw [show dualPar S = S.image fun x => (-x.1, x.2) from rfl, hS, Finset.image_image]
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a.rev, by simp⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a.rev, rfl⟩

theorem Jm_rev {n : ℕ} (ε : Fin n → Bool) :
    Formalism.REAL.Jm (fun a => ε a.rev) = (Formalism.REAL.Jm ε).submatrix Fin.revPerm Fin.revPerm := by
  ext i j
  by_cases h : i = j
  · subst h; simp [Formalism.REAL.Jm]
  · have h' : i.rev ≠ j.rev := fun h'' => h (Fin.rev_injective h'')
    simp [Formalism.REAL.Jm, Matrix.diagonal_apply, h, h']

def barModel {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)
    (hds : ∀ τ, letI := M.nacg τ; letI := M.ips τ
      IsDS (fun a => M.ε τ a.rev) (fun a => -M.lam τ a.rev) (fun g => M.σ τ (barRev g))) :
    DSModel V (fun τ => dualPar (S τ)) where
  H := M.H
  nacg := M.nacg
  ips := M.ips
  σ τ g := M.σ τ (barRev g)
  lam τ a := -M.lam τ a.rev
  ε τ a := M.ε τ a.rev
  fr τ := (M.fr τ).submatrix Fin.revPerm (Equiv.refl _)
  enum τ := isEnum_rev (M.enum τ)
  ds := hds
  fr_unit τ := (Matrix.isUnit_submatrix_equiv _ _).2 (M.fr_unit τ)
  fr_gram τ := by
    rw [Jm_rev, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, M.fr_gram]
    rfl

theorem barRev_barMat {p q n : ℕ} (e : Ix p q ≃ Fin n) (g : Mat p q) :
    barRev (barMat (e.trans Fin.revPerm) g) = plainMat e g := by
  ext i j
  simp [barRev, barMat, plainMat, Matrix.reindex_apply]

theorem barRev_plainMat {p q n : ℕ} (e : Ix p q ≃ Fin n) (g : Mat p q) :
    barRev (plainMat (e.trans Fin.revPerm) g) = barMat e g := by
  ext i j
  simp [barRev, barMat, plainMat, Matrix.reindex_apply]

theorem directBridge : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.ModelsAreCoverSeries D → DirectBridge D := by
  intro D hB X V S M τ p q l₁ l₂ c hpq h₁ h₂ hpar hhas hS
  obtain ⟨hsrc, htgt⟩ := hB
  have hds : ∀ τ, letI := M.nacg τ; letI := M.ips τ
      IsDS (fun a => M.ε τ a.rev) (fun a => -M.lam τ a.rev) (fun g => M.σ τ (barRev g)) :=
    fun τ => GlobalTheory.T.isDiscreteSeries_conjugate_reverse_contragredient _ _ _ _ _ (M.ds τ)
  have hset : GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.HidaSetting X p q l₁ l₂ c (fun τ => dualPar (S τ)) τ := by
    refine ⟨hpq, h₁, h₂, hpar, hhas, ?_⟩
    show dualPar (S τ) = _
    rw [hS]
  obtain ⟨-, m, hm, hU⟩ := hsrc X V _ (barModel M hds) τ p q l₁ l₂ c hset
  obtain ⟨-, m', hm', hU'⟩ := htgt X V _ (barModel M hds) τ p q l₁ l₂ c hset
  obtain rfl : m' = m := by exact_mod_cast hm'.trans hm.symm
  refine ⟨m', hm', fun e he b => ?_⟩
  have he' : SignCompat ((barModel M hds).ε τ) (e.trans Fin.revPerm) := by
    intro a
    change M.ε τ ((e.trans Fin.revPerm) a).rev = a.isLeft
    simp [he a]
  cases b
  · obtain ⟨U, hUm⟩ := hU _ he'
    refine ⟨U, ⟨fun x y => map_add U x y, fun z x => ?_, U.bijective, fun x => U.norm_map x, fun g x => ?_,
      fun x => ?_⟩⟩
    · exact U.map_smul z x
    · have hg := hUm.grp g x
      change _ = _ • U (M.σ τ (barRev (barMat (e.trans Fin.revPerm) _)) x) at hg
      rw [barRev_barMat] at hg
      simpa [phi] using hg
    · exact (isKFin_barRev (M.ε τ) (M.σ τ) x).symm.trans (hUm.kfin x)
  · obtain ⟨U, hUm⟩ := hU' _ he'
    refine ⟨U, ⟨fun x y => map_add U x y, fun z x => ?_, U.bijective, fun x => U.norm_map x, fun g x => ?_,
      fun x => ?_⟩⟩
    · exact U.map_smulₛₗ z x
    · have hg := hUm.grp g x
      change _ = _ • U (M.σ τ (barRev (plainMat (e.trans Fin.revPerm) _)) x) at hg
      rw [barRev_plainMat] at hg
      simpa [phi] using hg
    · exact (isKFin_barRev (M.ε τ) (M.σ τ) x).symm.trans (hUm.kfin x)

end GlobalTheory.ArchRec.Direct

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqSumFiniteCoordsOfInfinitePartZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.InfZeroFinSum

open Module

theorem repr_map_id {F A A' E ι : Type*} [Field F] [CommRing A] [Algebra F A] [CommRing A'] [Algebra F A']
    [CommRing E] [Algebra F E] [Fintype ι] [DecidableEq ι] (b : Basis ι F E) (f : A →ₐ[F] A')
    (z : A ⊗[F] E) (k : ι) :
    (Algebra.TensorProduct.basis A' b).repr (Algebra.TensorProduct.map f (AlgHom.id F E) z) k
      = f ((Algebra.TensorProduct.basis A b).repr z k) := by
  have hz : z = ∑ i, (Algebra.TensorProduct.basis A b).repr z i • (Algebra.TensorProduct.basis A b) i :=
    ((Algebra.TensorProduct.basis A b).sum_repr z).symm
  have hm : Algebra.TensorProduct.map f (AlgHom.id F E) z
      = ∑ i, f ((Algebra.TensorProduct.basis A b).repr z i) • (Algebra.TensorProduct.basis A' b) i := by
    conv_lhs => rw [hz]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  rw [hm, (Algebra.TensorProduct.basis A' b).repr_sum_self]

theorem eq_sum_of_fst_zero {F Ai Afn E ι : Type*} [Field F] [CommRing Ai] [Algebra F Ai] [CommRing Afn]
    [Algebra F Afn] [CommRing E] [Algebra F E] [Fintype ι] [DecidableEq ι] (b : Basis ι F E)
    (z : (Ai × Afn) ⊗[F] E)
    (hz : Algebra.TensorProduct.map (AlgHom.fst F Ai Afn) (AlgHom.id F E) z = 0) :
    z = ∑ k, ((0 : Ai), (Algebra.TensorProduct.basis Afn b).repr
      (Algebra.TensorProduct.map (AlgHom.snd F Ai Afn) (AlgHom.id F E) z) k) ⊗ₜ[F] b k := by
  have h1 : ∀ k, ((Algebra.TensorProduct.basis (Ai × Afn) b).repr z k).1 = 0 := by
    intro k
    have := repr_map_id b (AlgHom.fst F Ai Afn) z k
    rw [hz, map_zero] at this
    simpa using this.symm
  conv_lhs => rw [← (Algebra.TensorProduct.basis (Ai × Afn) b).sum_repr z]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [repr_map_id b (AlgHom.snd F Ai Afn) z k]
  have hc : (Algebra.TensorProduct.basis (Ai × Afn) b).repr z k
      = ((0 : Ai), AlgHom.snd F Ai Afn ((Algebra.TensorProduct.basis (Ai × Afn) b).repr z k)) :=
    Prod.ext (h1 k) rfl
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  exact congrArg (fun x => x ⊗ₜ[F] b k) hc

end GlobalTheory.InfZeroFinSum

theorem GlobalTheory.InfZeroFinSum.eq_sum_finCoord_of_infPart_eq_zero : ∀ (D : D7) (z : AE D), infPart D z = 0 → z = ∑ k, pairA D.host.F 0 (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D (GlobalTheory.HolDict.ShortVec.finPr D z) k) ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E k := by
  intro D z hz
  exact GlobalTheory.InfZeroFinSum.eq_sum_of_fst_zero (Module.finBasis D.host.F D.host.E) z hz
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfContr
section
noncomputable section

open scoped TensorProduct InnerProductSpace Classical

namespace GlobalTheory.Chain.IoLift.TensorFormProof

open GlobalTheory.Chain.IoLift

variable {A V H : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H]

theorem contr_tmul (ι : V →ₗ[ℂ] H) (y : V) (a : A) (v : V) :
    contr ι y (a ⊗ₜ[ℂ] v) = ⟪ι y, ι v⟫_ℂ • a := by
  unfold contr
  rw [LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearMap.comp_apply, innerₛₗ_apply_apply]
  exact TensorProduct.rid_tmul _ _

theorem dual_contr (ι : V →ₗ[ℂ] H) (y : V) (l : A →ₗ[ℂ] ℂ) (t : A ⊗[ℂ] V) :
    l (contr ι y t) = ⟪ι y, ι (TensorProduct.lid ℂ V (LinearMap.rTensor V l t))⟫_ℂ := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a v =>
    rw [contr_tmul, map_smul, LinearMap.rTensor_tmul, TensorProduct.lid_tmul, map_smul, inner_smul_right,
      smul_eq_mul, mul_comm]
  | add s u hs hu => simp only [map_add, inner_add_right, hs, hu]

theorem eq_zero_of_contr (ι : V →ₗ[ℂ] H) (hι : Function.Injective ι) (t : A ⊗[ℂ] V)
    (h : ∀ y, contr ι y t = 0) : t = 0 := by

  have hl : ∀ l : A →ₗ[ℂ] ℂ, LinearMap.rTensor V l t = 0 := by
    intro l
    set w := TensorProduct.lid ℂ V (LinearMap.rTensor V l t) with hw
    have h0 : ⟪ι w, ι w⟫_ℂ = 0 := by
      have := dual_contr ι w l t
      rw [h w, map_zero] at this
      exact this.symm
    have hw0 : w = 0 := hι ((inner_self_eq_zero.mp h0).trans (map_zero ι).symm)
    rw [hw] at hw0
    exact (LinearEquiv.map_eq_zero_iff _).mp hw0

  let e := (Module.Basis.ofVectorSpace ℂ A).repr
  have hs : TensorProduct.finsuppScalarLeft ℂ V _ (LinearMap.rTensor V e.toLinearMap t) = 0 := by
    ext i
    rw [TensorProduct.finsuppScalarLeft_apply, ← LinearMap.rTensor_comp_apply, hl, map_zero]
    rfl
  have h2 : LinearMap.rTensor V e.toLinearMap t = 0 := (LinearEquiv.map_eq_zero_iff _).mp hs
  have h3 := congrArg (LinearMap.rTensor V e.symm.toLinearMap) h2
  rwa [← LinearMap.rTensor_comp_apply, LinearEquiv.symm_comp, LinearMap.rTensor_id_apply, map_zero] at h3

theorem exists_tensor (ι : V →ₗ[ℂ] H) (β : V →ₛₗ[starRingEnd ℂ] A) (E : Submodule ℂ V) [FiniteDimensional ℂ E]
    (h : ∀ y, (∀ e ∈ E, ⟪ι y, ι e⟫_ℂ = 0) → β y = 0) : ∃ t : A ⊗[ℂ] V, ∀ y, contr ι y t = β y := by

  set F : Submodule ℂ H := E.map ι with hF
  haveI : FiniteDimensional ℂ F := by rw [hF]; infer_instance
  let b := stdOrthonormalBasis ℂ F
  have hpre : ∀ k, ∃ e : V, e ∈ E ∧ ι e = (b k : H) := fun k => Submodule.mem_map.mp (b k).2
  choose e heE he using hpre
  refine ⟨∑ k, β (e k) ⊗ₜ[ℂ] e k, fun y => ?_⟩
  rw [map_sum]
  simp only [contr_tmul, he]

  set z : V := ∑ k, ⟪(b k : H), ι y⟫_ℂ • e k with hz
  have hperp : ∀ x ∈ E, ⟪ι (y - z), ι x⟫_ℂ = 0 := by
    intro x hx
    have hxF : ι x ∈ F := Submodule.mem_map_of_mem hx
    have hx' : ι x = ∑ j, ⟪(b j : H), ι x⟫_ℂ • (b j : H) := by
      have := congrArg Subtype.val (b.sum_repr' ⟨ι x, hxF⟩)
      simpa [Submodule.coe_inner] using this.symm
    have key : ⟪ι y, ι x⟫_ℂ = ∑ j, ⟪ι y, (b j : H)⟫_ℂ * ⟪(b j : H), ι x⟫_ℂ := by
      conv_lhs => rw [hx']
      rw [inner_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [inner_smul_right, mul_comm]
    simp only [hz, map_sub, map_sum, map_smul, he, inner_sub_left, sum_inner, inner_smul_left, inner_conj_symm]
    rw [key, sub_self]
  have hyz := h (y - z) hperp
  rw [map_sub, sub_eq_zero] at hyz
  rw [hyz, hz, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.map_smulₛₗ, inner_conj_symm]

theorem tensorForm : TensorForm := by
  intro U A V H _ _ _ _ _ _ _ _ ι hι
  have sep : ∀ s u : A ⊗[ℂ] V, (∀ y, contr ι y s = contr ι y u) → s = u := fun s u hsu =>
    sub_eq_zero.mp (eq_zero_of_contr ι hι _ fun y => by rw [map_sub, hsu, sub_self])
  refine ⟨fun t ht => eq_zero_of_contr ι hι t ht, fun B hB => ?_⟩
  have hex : ∀ P, ∃ t : A ⊗[ℂ] V, ∀ y, contr ι y t = B P y := by
    intro P
    obtain ⟨E, hE, hk⟩ := hB P
    exact exists_tensor ι (B P) E hk
  choose g hg using hex
  exact ⟨{ toFun := g
           map_add' := fun P Q => sep _ _ fun y => by simp [hg]
           map_smul' := fun c P => sep _ _ fun y => by simp [hg] }, hg⟩

end GlobalTheory.Chain.IoLift.TensorFormProof

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyUnitClassRealizedByLatticeIsometryStatement
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_unitClass_realized_by_lattice_isometry : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r) (J : Matrix (Fin r) (Fin r) E), IsHermND σ J → ∀ (L : Submodule (𝓞 E) (Fin r → E)) [Submodule.IsLattice E L], ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∃ (φ : (Fv F v ⊗[F] Fld P) ≃ₗ[Fv F v ⊗[F] E] (Fin r → Fv F v ⊗[F] E)) (h : IsIsom P (Fv F v) J (1 : plusUnits P (Fv F v)).1.1 φ), gam h ∈ stabLoc σ J L v ∧ ∀ t, torEmb h t ∈ stabLoc σ J L v ↔ t ∈ stabLoc (star' P) (one₁ P) (stdLattice (Fld P) 1) v := by
  first | exact @GlobalTheory.TrUnitLat.eventually_unitClass_isom | exact GlobalTheory.TrUnitLat.eventually_unitClass_isom | (intros; apply GlobalTheory.TrUnitLat.eventually_unitClass_isom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCompactAnnihilatorFiniteAdelesStdChar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ScalarAnnih

open IsDedekindDomain GlobalTheory.Idele
open scoped nonZeroDivisors

theorem exists_compact_annihilator_finiteAdeles_traceChar (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ)
    (hc : Continuous ψ)
    (hfin : ∀ x : F, ψ (pairA F 0 (algebraMap F (Af F) x)) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F x : ℚ) : ℂ)))
    (O : Set (Af F)) (hO : O ∈ nhds (0 : Af F)) : ∃ K : Set (Af F), IsCompact K ∧
      ∀ x : Af F, (∀ t ∈ O, ψ (pairA F 0 (t * x)) = 1) → x ∈ K := by
  obtain ⟨N, hN, hNO⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F O hO
  obtain ⟨t, ht⟩ := exists_idealOf_eq (GlobalTheory.StdDual.codiff_ne_zero (F := F))
  let c : Af F := algebraMap F (Af F) ((N : F)⁻¹) * (t : Af F)
  refine ⟨(fun a => c * a) '' {a : Af F | ∀ v, a v ∈ v.adicCompletionIntegers F},
    (GlobalTheory.AdeleCocompact.isCompact_integral F).image (continuous_const.mul continuous_id), ?_⟩
  intro x hx
  have h1 : (N : Af F) * x ∈ adelicIdeal (GlobalTheory.StdDual.codiff F) := by
    rw [GlobalTheory.SplitUnram.mem_adelicIdeal_codiff_iff hc hfin]
    intro α hα
    have := hx _ (hNO α hα)
    rwa [nsmul_eq_mul, mul_assoc, mul_left_comm] at this
  have h2 : (t : Af F) * (((t⁻¹ : (Af F)ˣ) : Af F) * ((N : Af F) * x)) ∈
      adelicIdeal (t • (1 : FractionalIdeal (𝓞 F)⁰ F)) := by
    rw [Units.mul_inv_cancel_left, smul_one_eq, ht]; exact h1
  rw [mul_mem_adelicIdeal_smul, mem_adelicIdeal] at h2
  refine ⟨_, fun v => (mem_localIdeal_one_iff v _).1 (h2 v), ?_⟩
  have hN0 : (N : F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have e : algebraMap F (Af F) ((N : F)⁻¹) * (N : Af F) = 1 := by
    rw [← map_natCast (algebraMap F (Af F)) N, ← map_mul, inv_mul_cancel₀ hN0, map_one]
  simp only [c]
  calc algebraMap F (Af F) ((N : F)⁻¹) * (t : Af F) * (((t⁻¹ : (Af F)ˣ) : Af F) * ((N : Af F) * x))
      = algebraMap F (Af F) ((N : F)⁻¹) * (N : Af F) * x := by
        rw [mul_assoc, Units.mul_inv_cancel_left, mul_assoc]
    _ = x := by rw [e, one_mul]

theorem exists_compact_of_annih : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ O ∈ nhds (0 : Af D.host.F), ∃ K : Set (Af D.host.F), IsCompact K ∧
      ∀ x : Af D.host.F, (∀ t ∈ O, ψ (pairA D.host.F 0 (t * x)) = 1) → x ∈ K :=
  fun D ψ hψ O hO =>
    exists_compact_annihilator_finiteAdeles_traceChar D.host.F ψ hψ.1.1 (GlobalTheory.StdRat.stdChar_fin_rat D ψ hψ) O hO

end GlobalTheory.ScalarAnnih

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsConjugateInverseStaircaseModulusIdealStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conjugate_inverse_staircase_modulus_ideal : ∀ {D : D7} {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) (a b : ℕ), ∃ I' : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E, P.stA sc ^ a * (P.stAbar sc ^ a)⁻¹ * (((P.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ^ b * (((P.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ^ b)⁻¹) * I' = 1 ∧ ∀ x : D.host.E, x ∈ I' ↔ star x ∈ P.stA sc ^ a * (P.stAbar sc ^ a)⁻¹ * (((P.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ^ b * (((P.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ^ b)⁻¹) := by
  first | exact @GlobalTheory.ConjIdeal.stA_modul_conj_inv | exact GlobalTheory.ConjIdeal.stA_modul_conj_inv | (intros; apply GlobalTheory.ConjIdeal.stA_modul_conj_inv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHomSpaceDualIsotropicMiddleDecompositionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_homSpace_dual_isotropic_middle_decomposition : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∃ e : (Mx D W.rank r × Mx D W.rank r × WO V' W) ≃ₜ+ WO V W, (∀ t y x, e (t, y, x) = isoPart V W C' t + isoPart V W C y + midPart V V' W B x) ∧ ∀ t y x, e (t, y, x) ∈ ratL W V ↔ t ∈ ratMx D W.rank r ∧ y ∈ ratMx D W.rank r ∧ x ∈ ratL W V' := by
  first | exact @GlobalTheory.TwistDecomp.decomp_exists | exact GlobalTheory.TwistDecomp.decomp_exists | (intros; apply GlobalTheory.TwistDecomp.decomp_exists <;> assumption)
end

