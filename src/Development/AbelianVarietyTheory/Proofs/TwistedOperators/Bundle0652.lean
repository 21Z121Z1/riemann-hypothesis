import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0451
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1947
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1876
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0577
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0637
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0640
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1722
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0573
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0643
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0645
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1406
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1904
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1439
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0176
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0476
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0379
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0370
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0427
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0394
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0429
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0382
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0646
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0603
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1456
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlaceLinesRelatedAndVanishOffPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section

namespace GlobalTheory.PlaceLines

variable {D : D7}

theorem cart_herm {V : HSp D} (A : Fr V) (τ : D.what₂.Tau) :
    (A.cart τ)ᴴ * gramAt D V τ = gramAt D V τ * A.cart τ := by
  have hJ : (Formalism.REAL.Jm (A.ε τ))ᴴ = Formalism.REAL.Jm (A.ε τ) := by
    unfold Formalism.REAL.Jm
    rw [Matrix.diagonal_conjTranspose]
    congr 1; funext a; by_cases h : A.ε τ a = true <;> simp [h]
  have hJJ : Formalism.REAL.Jm (A.ε τ) * Formalism.REAL.Jm (A.ε τ) = 1 := by
    unfold Formalism.REAL.Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext a; split_ifs <;> norm_num
  have hdet : IsUnit (A.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ)
  have h1 : A.fr τ * (A.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have h2 : ((A.fr τ)⁻¹)ᴴ * (A.fr τ)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  have k1 : ∀ M : Matrix (Fin V.rank) (Fin V.rank) ℂ, ((A.fr τ)⁻¹)ᴴ * ((A.fr τ)ᴴ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  have k2 : ∀ M : Matrix (Fin V.rank) (Fin V.rank) ℂ, A.fr τ * ((A.fr τ)⁻¹ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have k3 : ∀ M : Matrix (Fin V.rank) (Fin V.rank) ℂ, Formalism.REAL.Jm (A.ε τ) * (Formalism.REAL.Jm (A.ε τ) * M) = M :=
    fun M => by rw [← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  rw [← A.fr_gram τ]
  simp only [Fr.cart, Matrix.conjTranspose_mul, hJ, Matrix.mul_assoc, k1, k2, k3]

theorem cart_herm_conj {V : HSp D} (A : Fr V) (τ : D.what₂.Tau) :
    (A.cart τ)ᵀ * (gramAt D V τ).map (starRingEnd ℂ) = (gramAt D V τ).map (starRingEnd ℂ) * (A.cart τ).map (starRingEnd ℂ) := by
  have h := congrArg (fun M => Matrix.map M (starRingEnd ℂ)) (cart_herm A τ)
  simp only [Matrix.map_mul] at h
  rw [← h]
  congr 1
  ext i j
  simp [Matrix.conjTranspose_apply]

theorem cart_frSgn' (ε : Bool) {V : HSp D} (A : Fr V) (τ : D.what₂.Tau) :
    (frSgn ε A).cart τ = (if ε then -1 else 1 : ℂ) • A.cart τ := by
  cases ε
  · simp [Fr.cart, frSgn]
  · have h : Formalism.REAL.Jm (fun a => xor true (A.ε τ a)) = -Formalism.REAL.Jm (A.ε τ) := by
      ext a b
      by_cases hab : a = b
      · subst hab; cases h : A.ε τ a <;> simp [Formalism.REAL.Jm, h]
      · simp [Formalism.REAL.Jm, hab]
    show (A.fr τ)⁻¹ * Formalism.REAL.Jm (fun a => xor true (A.ε τ a)) * A.fr τ = _
    rw [h, Matrix.mul_neg, Matrix.neg_mul]
    simp [Fr.cart]

theorem det_ne (ε : Bool) (S : HSp D) (τ : D.what₂.Tau) :
    IsUnit (((if ε then -1 else 1 : D.host.E) • S.gram).map ((starRingEnd ℂ).comp (tauE D τ))).det := by
  have hm := RingHom.map_det ((starRingEnd ℂ).comp (tauE D τ)) ((if ε then -1 else 1 : D.host.E) • S.gram)
  simp only [RingHom.mapMatrix_apply] at hm
  rw [← hm]
  refine Ne.isUnit ?_
  rw [Ne, map_eq_zero_iff _ (RingHom.injective _), Matrix.det_smul]
  refine mul_ne_zero (pow_ne_zero _ ?_) (gram_det_ne S)
  split_ifs <;> norm_num

open Classical in

theorem read_line (θ : InfFam D) (hθ : IsInfFam θ) (ε : Bool) (S X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d)
    (cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X)
    (hcS : ∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D)))
    (τ τ' : D.what₂.Tau) (φ : AE D →+* ℂ) (hφ : ∀ y, φ y = starRingEnd ℂ (θ τ' (infPart D y)))
    (z : Matrix (Fin X.rank) (Fin S.rank) ℂ) :
    ((cS.symm (lineAt θ τ z 1)).map φ)ᵀ.submatrix e id *
        (((if ε then -1 else 1 : D.host.E) • S.gram).map ((starRingEnd ℂ).comp (tauE D τ'))) =
      if τ' = τ then z.map (starRingEnd ℂ) else 0 := by
  have hy := cS.apply_symm_apply (lineAt θ τ z 1)
  rw [hcS] at hy
  have hinc : ∀ x : D.host.E, φ (inclR (AF D.host.F) x) = starRingEnd ℂ (tauE D τ' x) := by
    intro x
    rw [hφ]
    congr 1
    rw [← (hθ τ').1 x]
    congr 1
  have hR : (lineAt θ τ z 1).map φ = if τ' = τ then z.map (starRingEnd ℂ) else 0 := by
    have hL := (GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ z).2.2 1 τ'
    ext i j
    have h3 := congrFun (congrFun hL i) j
    simp only [compAt, Matrix.map_apply] at h3
    rw [Matrix.map_apply, hφ, h3]
    split_ifs <;> simp
  rw [← hR]
  conv_rhs => rw [← hy]
  rw [Matrix.map_mul]
  congr 1
  ext i j
  simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, hinc]

theorem zero_off (θ : InfFam D) (hθ : IsInfFam θ) (ε : Bool) (S X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d)
    (cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X)
    (hcS : ∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D)))
    (τ τ' : D.what₂.Tau) (hne : τ' ≠ τ) (φ : AE D →+* ℂ) (hφ : ∀ y, φ y = starRingEnd ℂ (θ τ' (infPart D y)))
    (z : Matrix (Fin X.rank) (Fin S.rank) ℂ) :
    (cS.symm (lineAt θ τ z 1)).map φ = 0 := by
  have h := read_line θ hθ ε S X e cS hcS τ τ' φ hφ z
  rw [if_neg hne] at h
  have h0 : ((cS.symm (lineAt θ τ z 1)).map φ)ᵀ.submatrix e id = 0 := by
    calc _ = ((cS.symm (lineAt θ τ z 1)).map φ)ᵀ.submatrix e id *
          (((if ε then -1 else 1 : D.host.E) • S.gram).map ((starRingEnd ℂ).comp (tauE D τ'))) *
          (((if ε then -1 else 1 : D.host.E) • S.gram).map ((starRingEnd ℂ).comp (tauE D τ')))⁻¹ :=
          (Matrix.mul_nonsing_inv_cancel_right _ _ (det_ne ε S τ')).symm
      _ = 0 := by rw [h, Matrix.zero_mul]
  ext i j
  have h4 := congrFun (congrFun h0 (e.symm j)) i
  simpa using h4

theorem submatrix_triple_mul_of_triangular {n d k : ℕ} (e : Fin k ≃ Fin d) (V : Matrix (Fin n) (Fin n) ℂ) (U : Matrix (Fin n) (Fin d) ℂ)
    (b : Matrix (Fin k) (Fin k) ℂ) :
    (V * U * (reindex e e b)ᵀ)ᵀ.submatrix e id = b * (Uᵀ.submatrix e id) * Vᵀ := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.mul_apply, reindex_apply, id,
    Equiv.symm_apply_apply, Finset.sum_mul]
  rw [← e.sum_comp]
  simp only [Equiv.symm_apply_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun l _ => ?_
  ring

open Classical in

theorem at_place (θ : InfFam D) (hθ : IsInfFam θ) (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ}
    (e : Fin X.rank ≃ Fin d) (cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X)
    (hcS : ∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D)))
    (τ : D.what₂.Tau) (φ : AE D →+* ℂ) (hφ : ∀ y, φ y = starRingEnd ℂ (θ τ (infPart D y)))
    (z : Matrix (Fin X.rank) (Fin S.rank) ℂ) :
    (cS.symm (lineAt θ τ (cplxO ((frSgn ε A).cart τ) (B.cart τ) z) 1)).map φ =
      Complex.I • ((if ε then 1 else -1 : ℂ) • A.cart τ * (cS.symm (lineAt θ τ z 1)).map φ *
        ((reindex e e (B.cart τ)).map (starRingEnd ℂ))ᵀ) := by
  set G := ((if ε then -1 else 1 : D.host.E) • S.gram).map ((starRingEnd ℂ).comp (tauE D τ)) with hGdef
  have hdet : IsUnit G.det := det_ne ε S τ
  have h1 : ((cS.symm (lineAt θ τ z 1)).map φ)ᵀ.submatrix e id * G = z.map (starRingEnd ℂ) := by
    have h := read_line θ hθ ε S X e cS hcS τ τ φ hφ z
    rw [if_pos rfl] at h
    exact h
  have h2 : ((cS.symm (lineAt θ τ (cplxO ((frSgn ε A).cart τ) (B.cart τ) z) 1)).map φ)ᵀ.submatrix e id * G =
      (cplxO ((frSgn ε A).cart τ) (B.cart τ) z).map (starRingEnd ℂ) := by
    have h := read_line θ hθ ε S X e cS hcS τ τ φ hφ (cplxO ((frSgn ε A).cart τ) (B.cart τ) z)
    rw [if_pos rfl] at h
    exact h
  have hP : ∀ M N : Matrix (Fin S.rank) (Fin d) ℂ, Mᵀ.submatrix e id = Nᵀ.submatrix e id → M = N := by
    intro M N h; ext i j; have h5 := congrFun (congrFun h (e.symm j)) i; simpa using h5
  have hC : ∀ M N : Matrix (Fin X.rank) (Fin S.rank) ℂ, M * G = N * G → M = N := by
    intro M N h
    rw [← Matrix.mul_nonsing_inv_cancel_right G M hdet, h, Matrix.mul_nonsing_inv_cancel_right G N hdet]
  have hG : G = (if ε then -1 else 1 : ℂ) • (gramAt D S τ).map (starRingEnd ℂ) := by
    rw [hGdef]; ext i j; cases ε <;> simp [gramAt]
  have hkey : ((if ε then 1 else -1 : ℂ) • A.cart τ)ᵀ * G =
      -(G * ((frSgn ε A).cart τ).map (starRingEnd ℂ)) := by
    rw [hG, cart_frSgn']
    have hh := cart_herm_conj A τ
    have hn : ((-1 : ℂ) • A.cart τ).map (starRingEnd ℂ) = -(A.cart τ).map (starRingEnd ℂ) := by
      ext i j; simp
    cases ε
    · simp only [Bool.false_eq_true, if_false, one_smul, neg_smul, Matrix.transpose_neg, Matrix.neg_mul, hh]
    · simp only [if_true, one_smul, hn, neg_smul, Matrix.neg_mul, Matrix.mul_neg, neg_neg, hh]
      have hn2 : (-A.cart τ).map (starRingEnd ℂ) = -(A.cart τ).map (starRingEnd ℂ) := by ext i j; simp
      rw [hn2, Matrix.mul_neg]
  have hm : ∀ M : Matrix (Fin X.rank) (Fin S.rank) ℂ,
      (Complex.I • M).map (starRingEnd ℂ) = -(Complex.I • M.map (starRingEnd ℂ)) := fun M => by
    ext i j; simp
  have hb : (reindex e e (B.cart τ)).map (starRingEnd ℂ) = reindex e e ((B.cart τ).map (starRingEnd ℂ)) := rfl
  have hs : ∀ M : Matrix (Fin S.rank) (Fin d) ℂ,
      (Complex.I • M)ᵀ.submatrix e id = Complex.I • (Mᵀ.submatrix e id) := fun M => by ext; simp
  apply hP
  apply hC
  rw [h2, hb, hs, submatrix_triple_mul_of_triangular, Matrix.smul_mul, Matrix.mul_assoc, hkey,
    Matrix.mul_neg, ← Matrix.mul_assoc, Matrix.mul_assoc _ _ G, h1, cplxO, hm, Matrix.map_mul, Matrix.map_mul, smul_neg]

theorem lines_at_place : ∀ (D : D7) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∀ (τ : D.what₂.Tau) (z : Matrix (Fin X.rank) (Fin S.rank) ℂ),
      ∃ w, (∀ w', w' ≠ w →
          (cS.symm (lineAt θ τ z 1)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w')) = 0 ∧
          (cS.symm (lineAt θ τ (cplxO ((frSgn ε A).cart τ) (B.cart τ) z) 1)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w')) = 0) ∧
        (cS.symm (lineAt θ τ (cplxO ((frSgn ε A).cart τ) (B.cart τ) z) 1)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w)) =
          Complex.I • (Vs.θ w * (cS.symm (lineAt θ τ z 1)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w)) * (Ws.θ w)ᵀ) := by
  intro D θ hθ ε S X A B d e Bs hBs Vs Ws r s r' s' hJ hJW hV hW hemb cS hcS τ z
  classical
  choose τf hτf hθV hθW using hemb
  have hpi : ∀ w y, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w) y = starRingEnd ℂ (θ (τf w) (infPart D y)) := by
    intro w y
    have h1 : (Bs.emb w).1 = (starRingEnd ℂ).comp (tauE D (τf w)) := RingHom.ext (hτf w)
    have h2 : ((starRingEnd ℂ).comp (tauE D (τf w))).comp (algebraMap D.host.F D.host.E) = w.embedding := by
      rw [← h1]; exact (Bs.emb w).2
    have h3 : Bs.emb w = ⟨(starRingEnd ℂ).comp (tauE D (τf w)), h2⟩ := Subtype.ext h1
    rw [h3]
    exact GlobalTheory.ConjInfExp.piInf_eq θ hθ (τf w) w h2 y
  have hinj : ∀ w w', τf w = τf w' → w = w' := by
    intro w w' h
    have h1 : (Bs.emb w).1 = (starRingEnd ℂ).comp (tauE D (τf w)) := RingHom.ext (hτf w)
    have h1' : (Bs.emb w').1 = (starRingEnd ℂ).comp (tauE D (τf w')) := RingHom.ext (hτf w')
    have e1 : w.embedding = w'.embedding := by
      rw [← (Bs.emb w).2, ← (Bs.emb w').2, h1, h1', h]
    rw [← NumberField.InfinitePlace.mk_embedding w, ← NumberField.InfinitePlace.mk_embedding w', e1]
  have hz : ∀ w', τf w' ≠ τ → ∀ z₀ : Matrix (Fin X.rank) (Fin S.rank) ℂ,
      (cS.symm (lineAt θ τ z₀ 1)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w')) = 0 := fun w' hne z₀ =>
    GlobalTheory.PlaceLines.zero_off θ hθ ε S X e cS hcS τ (τf w') hne _ (hpi w') z₀
  by_cases hex : ∃ w, τf w = τ
  · obtain ⟨w, hw⟩ := hex
    refine ⟨w, fun w' hw' => ?_, ?_⟩
    · have hne : τf w' ≠ τ := fun h => hw' (hinj w' w (h.trans hw.symm))
      exact ⟨hz w' hne z, hz w' hne _⟩
    · rw [hθV w, hθW w]
      subst hw
      exact GlobalTheory.PlaceLines.at_place θ hθ ε S X A B e cS hcS (τf w) _ (hpi w) z
  · obtain ⟨w0⟩ : Nonempty (NumberField.InfinitePlace D.host.F) := inferInstance
    have hne : ∀ w', τf w' ≠ τ := fun w' h => hex ⟨w', h⟩
    refine ⟨w0, fun w' _ => ⟨hz w' (hne w') z, hz w' (hne w') _⟩, ?_⟩
    rw [hz w0 (hne w0) z, hz w0 (hne w0) _]
    simp

end GlobalTheory.PlaceLines
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictionLineOperatorSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.ThetaLineDeriv
open GlobalTheory.WeilM GlobalTheory.LFun Filter Topology
open scoped Classical

theorem rho_sum {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (u : Matrix (Fin n) (Fin d) (AE F E))
    {m : ℕ} (φ : Fin m → (Fin n × Fin d → AF F) → ℂ) :
    M.co.rho ψ u (∑ i, φ i) = ∑ i, M.co.rho ψ u (φ i) := by
  funext x
  simp only [Darboux.rho, schr, Finset.sum_apply, Finset.mul_sum]

theorem rho_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (u : Matrix (Fin n) (Fin d) (AE F E)) :
    M.co.rho ψ u 0 = 0 := by
  funext x
  simp only [Darboux.rho, schr, Pi.zero_apply, mul_zero]

private theorem hasDerivAt_clm_comp_of_tendsto_slope {κ : Type} [Fintype κ] {F : Type} [Field F] [NumberField F] (c : ℝ → SInf F κ)
    (f c' : SInf F κ) (hc0 : c 0 = f) (hl : Tendsto (fun t : ℝ => t⁻¹ • (c t - f)) (𝓝[≠] 0) (𝓝 c'))
    (T : SInf F κ →L[ℂ] ℂ) : HasDerivAt (fun t => T (c t)) (T c') 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hT := ((T.restrictScalars ℝ).continuous.tendsto c').comp hl
  refine hT.congr fun t => ?_
  simp only [Function.comp_apply, slope_def_module, sub_zero, hc0]
  rw [← map_sub]
  exact (T.restrictScalars ℝ).map_smul t⁻¹ (c t - f)

theorem hasDerivAt_eval {κ : Type} [Fintype κ] {F : Type} [Field F] [NumberField F] (c : ℝ → SInf F κ) (f c' : SInf F κ)
    (hc0 : c 0 = f) (hl : Tendsto (fun t : ℝ => t⁻¹ • (c t - f)) (𝓝[≠] 0) (𝓝 c')) (y : κ → mixedEmbedding.mixedSpace F) :
    HasDerivAt (fun t => c t y) (c' y) 0 := by
  have h := hasDerivAt_clm_comp_of_tendsto_slope c f c' hc0 hl
    ((BoundedContinuousFunction.evalCLM ℂ y).comp (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ))
  simpa using h

theorem hasDerivAt_clm {κ : Type} [Fintype κ] {F : Type} [Field F] [NumberField F] (c : ℝ → SInf F κ) (f c' : SInf F κ)
    (hc0 : c 0 = f) (hl : Tendsto (fun t : ℝ => t⁻¹ • (c t - f)) (𝓝[≠] 0) (𝓝 c')) (T : SInf F κ →L[ℂ] ℂ) :
    HasDerivAt (fun t => T (c t)) (T c') 0 :=
  hasDerivAt_clm_comp_of_tendsto_slope c f c' hc0 hl T

private theorem exists_ne_zero_smul_mem_of_mem_span' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ)
    (om : Rep σ X W) (γ : Multiplicative ℝ →* UA σ W.J) (u : Matrix (Fin n) (Fin d) (AE F E))
    (f f₁ : SInf F (Fin n × Fin d)) (r : (Fin n × Fin d → AF F) → ℂ) (hR : Rest (evI F) (⇑f) r)
    (hD : ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) (⇑f) (⇑f₁))
    (horb : ∃ (c : ℝ → SInf F (Fin n × Fin d)) (c' : SInf F (Fin n × Fin d)), c 0 = f ∧
      Tendsto (fun t : ℝ => t⁻¹ • (c t - f)) (𝓝[≠] 0) (𝓝 c') ∧
      ∀ t : ℝ, Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) (⇑f) (⇑(c t)))
    (hclm : f ≠ 0 → ∃ T : SInf F (Fin n × Fin d) →L[ℂ] ℂ, ∀ g : SInf F (Fin n × Fin d),
      HasSum (fun ξ : Fin n × Fin d → F => M.co.rho ψ u (tens (evI F) (⇑g) r) (fun i => algebraMap F (AF F) (ξ i))) (T g)) :
    (∀ t : ℝ, Summable fun ξ : Fin n × Fin d → F =>
      M.co.rho ψ u (om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) (⇑f) r)) (fun i => algebraMap F (AF F) (ξ i))) ∧
    (Summable fun ξ : Fin n × Fin d → F => M.co.rho ψ u (tens (evI F) (⇑f₁) r) (fun i => algebraMap F (AF F) (ξ i))) ∧
    HasDerivAt (fun t : ℝ => thetaSum F (M.co.rho ψ u (om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) (⇑f) r))))
      (thetaSum F (M.co.rho ψ u (tens (evI F) (⇑f₁) r))) 0 := by
  obtain ⟨c, c', hc0, hl, hc⟩ := horb
  have hcr : ∀ t : ℝ, om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) (⇑f) r) = tens (evI F) (⇑(c t)) r :=
    fun t => hc t r hR
  have hder : ∀ x, HasDerivAt (fun t : ℝ => tens (evI F) (⇑(c t)) r x) (tens (evI F) (⇑c') r x) 0 := fun x =>
    (hasDerivAt_eval c f c' hc0 hl (fun j => evI F (x j))).mul_const (r x)
  have hf₁ : tens (evI F) (⇑f₁) r = tens (evI F) (⇑c') r := by
    funext x
    have h1 := hD r hR x
    simp only [hcr] at h1
    exact h1.unique (hder x)
  by_cases hf : f = 0
  · have hz : tens (evI F) (⇑f) r = 0 := by
      funext x
      simp [tens, hf]
    have h0 : ∀ t : ℝ, tens (evI F) (⇑(c t)) r = 0 := by
      intro t
      rw [← hcr t, hz, map_zero]
    have hc'0 : tens (evI F) (⇑c') r = 0 := by
      funext x
      have h3 : HasDerivAt (fun t : ℝ => tens (evI F) (⇑(c t)) r x) 0 0 := by
        simp only [h0, Pi.zero_apply]
        exact hasDerivAt_const _ _
      exact (hder x).unique h3
    refine ⟨fun t => ?_, ?_, ?_⟩
    · simp only [hcr, h0, rho_zero, Pi.zero_apply]
      exact summable_zero
    · simp only [hf₁, hc'0, rho_zero, Pi.zero_apply]
      exact summable_zero
    · simp only [hcr, h0, hf₁, hc'0, rho_zero, thetaSum, Pi.zero_apply, tsum_zero]
      exact hasDerivAt_const _ _
  · obtain ⟨T, hT⟩ := hclm hf
    refine ⟨fun t => ?_, ?_, ?_⟩
    · rw [hcr t]
      exact (hT (c t)).summable
    · rw [hf₁]
      exact (hT c').summable
    · have e1 : (fun t : ℝ => thetaSum F (M.co.rho ψ u (om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) (⇑f) r))))
          = fun t => T (c t) := by
        funext t
        rw [hcr t]
        exact (hT (c t)).tsum_eq
      have e2 : thetaSum F (M.co.rho ψ u (tens (evI F) (⇑c') r)) = T c' := (hT c').tsum_eq
      rw [e1, hf₁, e2]
      exact hasDerivAt_clm c f c' hc0 hl T

end GlobalTheory.ThetaLineDeriv

namespace GlobalTheory.ThetaLineDeriv
open GlobalTheory.WeilM GlobalTheory.LFun Filter Topology
open scoped Classical

theorem main : GlobalTheory.FunPr.Hypotheses₂ → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ γ ∈ Lines σ G.W, ∀ (m : ℕ) (f f₁ : Fin m → SInf F (Fin a × Fin (a + a')))
    (r : Fin m → (Fin a × Fin (a + a') → AF F) → ℂ), (∀ i, Rest (evI F) (⇑(f i)) (r i)) →
    (∀ i, ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) (⇑(f i)) (⇑(f₁ i))) →
    ∀ u, HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (G.M.co.rho B.ψ u
        (om (1, γ (Multiplicative.ofAdd t)) (∑ i, tens (evI F) (⇑(f i)) (r i)))))
      (GlobalTheory.WeilM.thetaSum F (G.M.co.rho B.ψ u (∑ i, tens (evI F) (⇑(f₁ i)) (r i)))) 0 := by
  intro hP F E _ _ _ _ _ σ a a' B G X om om' hT γ hγ m f f₁ r hR hD u
  have hone := fun i => exists_ne_zero_smul_mem_of_mem_span' G.M B.ψ om γ u (f i) (f₁ i) (r i) (hR i) (hD i)
    (GlobalTheory.WeilArchSmooth.exists_orbit hP G.M B.ψ X.β (X.β / X.α) om hT.base.cm hT.base.std hT.weil γ hγ (f i))
    (fun hf => GlobalTheory.ThetaSchrCont.exists_clm_hasSum G.M B.ψ hT.base.std u (f i) (r i) (hR i) hf)
  have e1 : ∀ t : ℝ, thetaSum F (G.M.co.rho B.ψ u (om (1, γ (Multiplicative.ofAdd t)) (∑ i, tens (evI F) (⇑(f i)) (r i))))
      = ∑ i, thetaSum F (G.M.co.rho B.ψ u (om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) (⇑(f i)) (r i)))) := by
    intro t
    rw [map_sum, rho_sum]
    unfold thetaSum
    simp only [Finset.sum_apply]
    exact (hasSum_sum fun i _ => ((hone i).1 t).hasSum).tsum_eq
  have e2 : thetaSum F (G.M.co.rho B.ψ u (∑ i, tens (evI F) (⇑(f₁ i)) (r i)))
      = ∑ i, thetaSum F (G.M.co.rho B.ψ u (tens (evI F) (⇑(f₁ i)) (r i))) := by
    rw [rho_sum]
    unfold thetaSum
    simp only [Finset.sum_apply]
    exact (hasSum_sum fun i _ => (hone i).2.1.hasSum).tsum_eq
  simp only [e1, e2]
  exact HasDerivAt.fun_sum fun i _ => (hone i).2.2

end GlobalTheory.ThetaLineDeriv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentConjugateToSquareStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicSchwartzSpace_le_span_pureTensors : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (d : ℕ) (W : Spc F E d) (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → (2 : 𝓞 F) ∉ v.asIdeal →
    ∀ n ∈ GlobalTheory.InertDbl.NabD σ W v, ∃ s ∈ GlobalTheory.InertDbl.ParD σ W v, s * n * s⁻¹ = n * n := by
  first | exact @GlobalTheory.SplitConj.conj_to_sq | exact GlobalTheory.SplitConj.conj_to_sq | (intros; apply GlobalTheory.SplitConj.conj_to_sq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionOneParamSubgroupGaussVacuumSmooth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

namespace GlobalTheory.GaussLine

theorem smooth_vacuum_line : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.W, ∀ T : ℝ → SInf F (Fin a × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a × Fin (a + a')),
    (∀ (t : ℝ) (f : SInf F (Fin a × Fin (a + a'))), Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) f (T t f)) → ∀ f₀, G.M.IsGauss B.ψ B.emb f₀ →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F) => T p.1 f₀ p.2) ∧ ∃ f' ∈ G.M.Pol B.ψ B.emb, ∀ x, HasDerivAt (fun t => T t f₀ x) (f' x) 0 := by
  intro F E _ _ _ _ _ σ a a' B G X om om' hT γ hγ T hTa f₀ hf₀
  obtain ⟨h1, h0⟩ := GlobalTheory.T.unitaryArchimedeanLine_operators_oneParameter B G X om om' hT γ hγ T hTa
  have hU := GlobalTheory.T.one_parameter_operator_unique B G X om om' hT γ hγ T hTa Measure.addHaar inferInstance
  obtain ⟨A, hAc, hAadd, hA0, hAint⟩ := GlobalTheory.T.one_parameter_weil_operator_derivative B G X om om' hT γ hγ T hTa
  have hC := GlobalTheory.T.continuous_archimedeanWeilOperator_line_triple B G X om om' hT γ hγ T hTa
  obtain ⟨J₀, hJ, hvac⟩ := GlobalTheory.T.exists_complexStructure_gaussVacuum_fockEquations B G X om om' hT f₀ hf₀
  haveI : BorelSpace (Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F) := Pi.borelSpace
  obtain ⟨hsm, n, qs, qs', cs, c, hd⟩ := GlobalTheory.T.weilOneParam_moves_fockVacuum_smoothly (V := Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F) Measure.addHaar (GlobalTheory.GaussLine.pairInf F (Fin a × Fin (a + a')))
    (GlobalTheory.T.tracePairingArchimedeanVars_nondegenerate_right F _) T h1 h0 hU A hAc hAadd hA0 hAint hC J₀ hJ f₀ hvac
  refine ⟨hsm, ?_⟩
  have hf₀P : f₀ ∈ G.M.Pol B.ψ B.emb := Submodule.mem_sInf.2 fun N hN => hN.1 f₀ hf₀
  have hmul := GlobalTheory.T.thetaTriple_polynomialFock_stable_mul_trace_linear B G X om om' hT
  choose m hmP hmE using hmul
  refine ⟨(∑ i, cs i • m (qs i) (m (qs' i) f₀ hf₀P) (hmP _ _ _)) + c • f₀,
    add_mem (sum_mem fun i _ => Submodule.smul_mem _ _ (hmP _ _ _)) (Submodule.smul_mem _ _ hf₀P), fun x => ?_⟩
  convert hd x using 1
  simp only [SchwartzMap.add_apply, SchwartzMap.sum_apply, SchwartzMap.smul_apply, smul_eq_mul, hmE]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end GlobalTheory.GaussLine
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLineOneParameterStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.ArchUniq MeasureTheory
open scoped SchwartzMap Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_line_one_parameter : GlobalTheory.FunPr.Hypotheses₂ → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    IsCMExt F E σ → IsStd ψ → M.IsWeil ψ χX χW om → ∀ γ ∈ Lines σ W,
    ∃ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
      (∀ t (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) ⇑f ⇑(T t f)) ∧
      (∀ s t (f : SInf F (Fin n × Fin d)), T (s + t) f = T s (T t f)) ∧ ∀ f : SInf F (Fin n × Fin d), T 0 f = f := by
  first | exact @GlobalTheory.ArchFamily.exists_family | exact GlobalTheory.ArchFamily.exists_family | (intros; apply GlobalTheory.ArchFamily.exists_family <;> assumption)
end

