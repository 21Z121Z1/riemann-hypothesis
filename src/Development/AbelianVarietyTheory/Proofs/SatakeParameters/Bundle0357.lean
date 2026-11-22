import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulCompSmul
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MuCharacterDetLevelEqLocalTameProduct
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0032
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0264
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0267
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0345
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.EqOneOfPh
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0350
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0004
import Formalism.LocalToGlobal.GroupLattices.Joint0
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.GramLevelZeroEqReindex
import Formalism.LocalToGlobal.HermitianForms.Bundle0007
import Formalism.SharpRestriction.GrowthBounds.TwistedLevelAgreement.StepInTwK
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.Bundle0003
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StabilisesColumnBaseLatticeIffFirstFactor
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.WtTieOf
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Reframe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0084

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepCharacterDetCoupledEqProdLocal
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

noncomputable section

namespace GlobalTheory.CplMuDet

open Matrix
open scoped TensorProduct

section Cong

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
  {P : HeightOneSpectrum (𝓞 E)}

theorem intAtA_add {a b : E ⊗[F] FiniteAdeleRing (𝓞 F) F} (ha : IntAtA (F := F) P a) (hb : IntAtA (F := F) P b) :
    IntAtA (F := F) P (a + b) := by
  obtain ⟨s, hs, h1⟩ := ha
  obtain ⟨r, hr, h2⟩ := hb
  have hi : ∀ x : 𝓞 E, iA F E (algebraMap (𝓞 E) E x) ∈ Formalism.L2.Herm.intAf F E := fun x => (toRInt F E x).2
  refine ⟨s * r, fun h => (P.isPrime.mem_or_mem h).elim hs hr, ?_⟩
  have e : iA F E (algebraMap (𝓞 E) E (s * r)) * (a + b) =
      iA F E (algebraMap (𝓞 E) E r) * (iA F E (algebraMap (𝓞 E) E s) * a) +
        iA F E (algebraMap (𝓞 E) E s) * (iA F E (algebraMap (𝓞 E) E r) * b) := by
    rw [map_mul, map_mul]; ring
  rw [e]
  exact add_mem (mul_mem (hi r) h1) (mul_mem (hi s) h2)

theorem intAtA_mul {a b : E ⊗[F] FiniteAdeleRing (𝓞 F) F} (ha : IntAtA (F := F) P a) (hb : IntAtA (F := F) P b) :
    IntAtA (F := F) P (a * b) := by
  obtain ⟨s, hs, h1⟩ := ha
  obtain ⟨r, hr, h2⟩ := hb
  refine ⟨s * r, fun h => (P.isPrime.mem_or_mem h).elim hs hr, ?_⟩
  have e : iA F E (algebraMap (𝓞 E) E (s * r)) * (a * b) =
      (iA F E (algebraMap (𝓞 E) E s) * a) * (iA F E (algebraMap (𝓞 E) E r) * b) := by
    rw [map_mul, map_mul]; ring
  rw [e]
  exact mul_mem h1 h2

theorem intAtA_int (x : 𝓞 E) : IntAtA (F := F) P (iA F E (algebraMap (𝓞 E) E x)) :=
  ⟨1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by
    rw [map_one, map_one, one_mul]; exact (toRInt F E x).2⟩

def intAtSub (P : HeightOneSpectrum (𝓞 E)) :
    Subring (E ⊗[F] FiniteAdeleRing (𝓞 F) F) where
  carrier := {a | IntAtA (F := F) P a}
  mul_mem' := GlobalTheory.CplMuDet.intAtA_mul
  one_mem' := by simpa using GlobalTheory.CplMuDet.intAtA_int (F := F) (P := P) 1
  add_mem' := GlobalTheory.CplMuDet.intAtA_add
  zero_mem' := by simpa using GlobalTheory.CplMuDet.intAtA_int (F := F) (P := P) 0
  neg_mem' := by
    intro a ha
    have := GlobalTheory.CplMuDet.intAtA_mul (GlobalTheory.CplMuDet.intAtA_int (F := F) (P := P) (-1)) ha
    simpa using this

theorem det_congAt {d : ℕ} (hd : 1 ≤ d) {k : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (h : CongAt P d k) :
    IntAtA (F := F) P (iA F E ((qOf P : ℕ) : E)⁻¹ *
      (((Matrix.GeneralLinearGroup.det k : (E ⊗[F] FiniteAdeleRing (𝓞 F) F)ˣ) : E ⊗[F] FiniteAdeleRing (𝓞 F) F) - 1)) := by
  classical
  set S := intAtSub (F := F) P with hS
  have hq : ((qOf P : ℕ) : E) ≠ 0 := by
    have : qOf P ≠ 0 := fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact_mod_cast this
  set Q := iA F E ((qOf P : ℕ) : E) with hQ
  have hcQ : iA F E ((qOf P : ℕ) : E)⁻¹ * Q = 1 := by rw [hQ, ← map_mul, inv_mul_cancel₀ hq, map_one]
  have hQS : Q ∈ S := by
    have := GlobalTheory.CplMuDet.intAtA_int (F := F) (P := P) ((qOf P : ℕ) : 𝓞 E)
    simpa [hQ] using this
  have hZ : ∀ a b, Q ^ (d - 1) * (iA F E (((qOf P : ℕ) : E) ^ d)⁻¹ *
      ((k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1) a b) ∈ S :=
    fun a b => S.mul_mem (S.pow_mem hQS _) (h a b)
  have hZe : ∀ a b, Q * (Q ^ (d - 1) * (iA F E (((qOf P : ℕ) : E) ^ d)⁻¹ *
      ((k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1) a b)) =
      ((k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1) a b := by
    intro a b
    have e : Q * Q ^ (d - 1) * iA F E (((qOf P : ℕ) : E) ^ d)⁻¹ = 1 := by
      rw [← pow_succ', Nat.sub_add_cancel hd, hQ, ← map_pow, ← map_mul, mul_inv_cancel₀ (pow_ne_zero _ hq), map_one]
    rw [← mul_assoc, ← mul_assoc, e, one_mul]
  let Z : Matrix (Fin N) (Fin N) S := fun a b => ⟨_, hZ a b⟩
  let q' : S := ⟨Q, hQS⟩
  let M : Matrix (Fin N) (Fin N) S := 1 + q' • Z
  have hM : M.map S.subtype = (k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) := by
    ext a b
    have e1 : S.subtype ((1 : Matrix (Fin N) (Fin N) S) a b) = (1 : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) a b := by
      rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
    rw [Matrix.map_apply]
    simp only [M]
    rw [Matrix.add_apply, map_add, e1, Matrix.smul_apply, smul_eq_mul, map_mul]
    show _ + Q * (Q ^ (d - 1) * _) = _
    rw [hZe, Matrix.sub_apply]
    ring_nf
  set I : Ideal S := Ideal.span {q'}
  have hMI : M.map (Ideal.Quotient.mk I) = 1 := by
    ext a b
    have hq0 : Ideal.Quotient.mk I q' = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
    rw [Matrix.map_apply]
    simp only [M]
    rw [Matrix.add_apply, map_add, Matrix.smul_apply, smul_eq_mul, map_mul, hq0, zero_mul, add_zero,
      Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hdet : Ideal.Quotient.mk I M.det = Ideal.Quotient.mk I 1 := by
    rw [RingHom.map_det, map_one]
    show (M.map (Ideal.Quotient.mk I)).det = 1
    rw [hMI, Matrix.det_one]
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 hdet)
  have hk : ((Matrix.GeneralLinearGroup.det k : (E ⊗[F] FiniteAdeleRing (𝓞 F) F)ˣ) : E ⊗[F] FiniteAdeleRing (𝓞 F) F) =
      S.subtype M.det := by
    rw [RingHom.map_det, Matrix.GeneralLinearGroup.val_det_apply]
    exact congrArg Matrix.det hM.symm
  have e2 : iA F E ((qOf P : ℕ) : E)⁻¹ *
      (((Matrix.GeneralLinearGroup.det k : (E ⊗[F] FiniteAdeleRing (𝓞 F) F)ˣ) : E ⊗[F] FiniteAdeleRing (𝓞 F) F) - 1) = (w : _) := by
    rw [hk, show S.subtype M.det - 1 = S.subtype (M.det - 1) by simp, ← hw, map_mul]
    show iA F E ((qOf P : ℕ) : E)⁻¹ * ((w : _) * Q) = _
    rw [mul_comm (w : E ⊗[F] FiniteAdeleRing (𝓞 F) F), ← mul_assoc, hcQ, one_mul]
  rw [e2]
  exact w.2

end Cong

end GlobalTheory.CplMuDet

namespace GlobalTheory.CplMuDet

open Matrix
open scoped TensorProduct

section Rat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem det_ratA (g : GL (Fin n) E) :
    ((Matrix.GeneralLinearGroup.det (ratA F g) : (E ⊗[F] FiniteAdeleRing (𝓞 F) F)ˣ) : E ⊗[F] FiniteAdeleRing (𝓞 F) F) =
      iA F E ((Matrix.GeneralLinearGroup.det g : Eˣ) : E) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
  rfl

end Rat

section Frame

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Fields} (s : Seam D X)

theorem det_seamGL {n : ℕ} (g : Sp X.E n ≃ₗ[X.E] Sp X.E n) :
    ((Matrix.GeneralLinearGroup.det (seamGL s g) : D.host.Eˣ) : D.host.E) = s.iE ((LinearEquiv.det g : X.Eˣ) : X.E) := by
  have h : ((seamGL s g : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) =
      (LinearMap.toMatrix' g.toLinearMap).map (s.iE : X.E →+* D.host.E) := rfl
  rw [Matrix.GeneralLinearGroup.val_det_apply, h, ← RingHom.mapMatrix_apply, ← RingHom.map_det, LinearMap.det_toMatrix',
    LinearEquiv.coe_det]
  rfl

variable {i : ℕ} {SB : Finset (HeightOneSpectrum (𝓞 X.E))} (fb : SB → GL (Fin (D.R.N i)) D.host.E) (dep : SB → ℕ)

theorem det_inFrame {P : SB} {κ : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)}
    {g : Sp X.E (D.R.N i) ≃ₗ[X.E] Sp X.E (D.R.N i)} (hd : 1 ≤ dep P) (h : InFrame s fb dep P κ g) :
    IntAtA (F := D.host.F) (seamP s P.1) (iA D.host.F D.host.E ((qOf (seamP s P.1) : D.host.E))⁻¹ *
      ((((Matrix.GeneralLinearGroup.det κ)⁻¹ : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E) *
        iA D.host.F D.host.E (s.iE ((LinearEquiv.det g : X.Eˣ) : X.E)) - 1)) := by
  have H := det_congAt hd h
  have e : ((Matrix.GeneralLinearGroup.det (((ratA D.host.F (fb P))⁻¹ * κ * ratA D.host.F (fb P))⁻¹ *
      ratA D.host.F (seamGL s g)) : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E) =
      (((Matrix.GeneralLinearGroup.det κ)⁻¹ : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E) *
        iA D.host.F D.host.E (s.iE ((LinearEquiv.det g : X.Eˣ) : X.E)) := by
    rw [map_mul, map_inv, map_mul, map_mul, map_inv, Units.val_mul, det_ratA, det_seamGL]
    congr 2
    rw [mul_comm, mul_inv_cancel_left]
  rw [← e]
  exact H

end Frame

end GlobalTheory.CplMuDet

theorem GlobalTheory.CplMuDet.muOf_det_cpl : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => MuLaw t u μ dtU → ∀ (β' : (St (t.m2 + 1) (cpl_lt t μ).le).Ch)
    (κ' : ((St (t.m2 + 1) (cpl_lt t μ).le).K β').lev.U) (κ'' : GLQ t.X.E (D.R.N (t.m2 + 1)) (SB t μ)),
    (∀ P, InFrame t.seam (A.fb (t.m2 + 1) (cpl_lt t μ).le β') (t.cst μ).D P κ'.1 ((κ'' P)⁻¹).1) →
    muOf t u μ dtU (t.m2 + 1) (Matrix.GeneralLinearGroup.det κ'.1) =
      t.seam.σ₀ (∏ P : SB t μ, rhoS t.Ch t.sel (t.tup μ) t.m2 P ((LinearEquiv.det (κ'' P).1 : t.X.Eˣ) : t.X.E))) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie hMu β' κ' κ'' hF
  have hlt : t.m2 < D.R.m := by have := cpl_lt t μ; omega
  obtain ⟨-, h⟩ := GlobalTheory.LevMuDet.muOf_det_lev A dtU a hPin hTie hMu t.m2 hlt (t.m2 + 1) (cpl_lt t μ).le β' κ'
    (fun P => ((LinearEquiv.det ((κ'' P)⁻¹).1 : t.X.Eˣ) : t.X.E))
    (fun P => GlobalTheory.CplMuDet.det_inFrame t.seam _ _ ((t.idx_ok μ).cst_ok.D_pos P) (hF P))
  rw [h]
  congr 1
  exact Finset.prod_congr rfl fun P _ => GlobalTheory.TopLaw.rhoT_inv _ P (κ'' P)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepChartsPlacesFirstFactorEqStepZero
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.Xc

set_option maxHeartbeats 4000000 in

theorem chart_places_firstFactor_eq_zero :
    Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
      ∀ j (hj : j + 1 ≤ D.R.m) (β : (I.at' j hj).st.Ch) v, ((I.at' j hj).st.loc β).pl v = (A0 J).pl v ∧
        ∀ x, phiA ((I.at' j hj).st.loc β) v x = phiA (A0 J) v x) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S _hD _hS j hj β v
  refine ⟨J.pl j hj β v, ?_⟩
  have h := firstFactor_agree D.host.F D.host.E _ _ (((I.at' j hj).st.loc β).pl v).1 ((A0 J).pl v).1
    (((I.at' j hj).st.loc β).eQ v) ((A0 J).eQ v) (((I.at' j hj).st.loc β).ph v) ((A0 J).ph v)
    (fun c => by
      show ((((I.at' j hj).st.loc β).spl v) ((1 : D.host.E) ⊗ₜ[D.host.F] c)).1 = c
      rw [J.alg j hj β v c])
    (fun c => by
      show (((A0 J).spl v) ((1 : D.host.E) ⊗ₜ[D.host.F] c)).1 = c
      rw [J.alg0 v c])
    ((H.core j hj β).int v) (J.one.int v)
    (fun a => by
      have h1 := RingHom.congr_fun (J.iw j hj β v) a
      exact h1)
  exact h.2

end GlobalTheory.TwV.Xc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroLatticeTupleMoveByRationalIsometry
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.Xc.Mv0

theorem frm_gen {E Q : Type} [Field E] [Field Q] (σ : E →+* E) {a N : ℕ} (rk hr : a = N) (J0 : Matrix (Fin N) (Fin N) E)
    (B g : GL (Fin N) E) (iw : E →+* Q) (M : GL (Fin a) Q) (hM : castGL rk Q M = bc iw (B⁻¹ * g * B)) :
    (((LinearMap.toMatrix' ((stdCo σ (J0.reindex (finCongr rk.symm) (finCongr rk.symm)) : (Fin a → E) ≃ₗ[E] (Fin a → E)) :
      (Fin a → E) →ₗ[E] (Fin a → E))) * ((reGL (finCongr rk.symm) B : GL (Fin a) E) : Matrix (Fin a) (Fin a) E)).map iw).submatrix
        (finCongr (rfl : a = a)) (finCongr (rfl : a = a)) * (M : Matrix (Fin a) (Fin a) Q) =
    (eMat hr σ J0 g).map iw *
      ((((LinearMap.toMatrix' ((stdCo σ (J0.reindex (finCongr rk.symm) (finCongr rk.symm)) : (Fin a → E) ≃ₗ[E] (Fin a → E)) :
      (Fin a → E) →ₗ[E] (Fin a → E))) * ((reGL (finCongr rk.symm) B : GL (Fin a) E) : Matrix (Fin a) (Fin a) E)).map iw).submatrix
        (finCongr (rfl : a = a)) (finCongr (rfl : a = a))) := by
  subst rk
  have hJ : J0.reindex (finCongr (rfl : a = a)) (finCongr (rfl : a = a)) = J0 := by ext i j; simp
  have hB : ((reGL (finCongr (rfl : a = a)) B : GL (Fin a) E) : Matrix (Fin a) (Fin a) E) = (B : Matrix (Fin a) (Fin a) E) := by
    ext i j
    show (Matrix.reindexAlgEquiv E E (finCongr (rfl : a = a)) (B : Matrix (Fin a) (Fin a) E)) i j = _
    simp [Matrix.reindexAlgEquiv_apply]
  have hMm : (M : Matrix (Fin a) (Fin a) Q) = ((B⁻¹ * g * B : GL (Fin a) E) : Matrix (Fin a) (Fin a) E).map iw := by
    ext i j
    have h1 := congrArg (fun x : GL (Fin a) Q => (x : Matrix (Fin a) (Fin a) Q) i j) hM
    simp only [castGL_apply] at h1
    exact h1
  have hE : eMat hr σ J0 g = LinearMap.toMatrix' ((stdCo σ J0 : (Fin a → E) ≃ₗ[E] (Fin a → E)) : (Fin a → E) →ₗ[E] (Fin a → E)) *
      (g : Matrix (Fin a) (Fin a) E) *
      LinearMap.toMatrix' (((stdCo σ J0).symm : (Fin a → E) ≃ₗ[E] (Fin a → E)) : (Fin a → E) →ₗ[E] (Fin a → E)) := by
    have e0 : eMat hr σ J0 g = LinearMap.toMatrix' (stdG σ J0 g).toLinearMap := by ext i j; simp [eMat]
    rw [e0]
    have e1 : (stdG σ J0 g).toLinearMap = (stdCo σ J0 : (Fin a → E) →ₗ[E] (Fin a → E)) ∘ₗ (Matrix.toLin' (g : Matrix (Fin a) (Fin a) E)) ∘ₗ
        ((stdCo σ J0).symm : (Fin a → E) →ₗ[E] (Fin a → E)) := by
      apply LinearMap.ext; intro x; rfl
    rw [e1, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', Matrix.mul_assoc]
  have hsub : ∀ A : Matrix (Fin a) (Fin a) Q, A.submatrix (finCongr (rfl : a = a)) (finCongr (rfl : a = a)) = A := fun A => by ext i j; rfl
  rw [hsub, hJ, hB, hMm, hE, ← Matrix.map_mul, ← Matrix.map_mul]
  congr 1
  have hci : LinearMap.toMatrix' (((stdCo σ J0).symm : (Fin a → E) ≃ₗ[E] (Fin a → E)) : (Fin a → E) →ₗ[E] (Fin a → E)) *
      LinearMap.toMatrix' ((stdCo σ J0 : (Fin a → E) ≃ₗ[E] (Fin a → E)) : (Fin a → E) →ₗ[E] (Fin a → E)) = 1 := by
    rw [← LinearMap.toMatrix'_comp, LinearEquiv.symm_comp, LinearMap.toMatrix'_id]
  have hBB : (B : Matrix (Fin a) (Fin a) E) * ((B⁻¹ : GL (Fin a) E) : Matrix (Fin a) (Fin a) E) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  simp only [Units.val_mul]
  calc _ = LinearMap.toMatrix' ((stdCo σ J0 : (Fin a → E) ≃ₗ[E] (Fin a → E)) : (Fin a → E) →ₗ[E] (Fin a → E)) *
        ((B : Matrix (Fin a) (Fin a) E) * ((B⁻¹ : GL (Fin a) E) : Matrix (Fin a) (Fin a) E)) * (g : Matrix (Fin a) (Fin a) E) * (B : Matrix (Fin a) (Fin a) E) := by
          simp only [Matrix.mul_assoc]
    _ = _ := by
          rw [hBB, Matrix.mul_one]
          calc _ = LinearMap.toMatrix' ((stdCo σ J0 : (Fin a → E) ≃ₗ[E] (Fin a → E)) : (Fin a → E) →ₗ[E] (Fin a → E)) * (g : Matrix (Fin a) (Fin a) E) *
                (LinearMap.toMatrix' (((stdCo σ J0).symm : (Fin a → E) ≃ₗ[E] (Fin a → E)) : (Fin a → E) →ₗ[E] (Fin a → E)) *
                  LinearMap.toMatrix' ((stdCo σ J0 : (Fin a → E) ≃ₗ[E] (Fin a → E)) : (Fin a → E) →ₗ[E] (Fin a → E))) * (B : Matrix (Fin a) (Fin a) E) := by
                rw [hci, Matrix.mul_one]
            _ = _ := by simp only [Matrix.mul_assoc]

end GlobalTheory.TwV.Xc.Mv0

namespace GlobalTheory.TwV.Xc.Mv0

open Formalism.MainNotions.G.CmpJ.PStabEq

theorem regl2 {R : Type} [CommRing R] {a N : ℕ} (h : a = N) (h' : N = a) (y : GL (Fin N) R) :
    Formalism.L2.PairingIndexBounds.F.reGL (finCongr h) (Formalism.L2.PairingIndexBounds.F.reGL (finCongr h') y) = y := by
  subst h
  ext i j
  show (Matrix.reindexAlgEquiv R R (finCongr (rfl : a = a)) (Matrix.reindexAlgEquiv R R (finCongr h') (y : Matrix (Fin a) (Fin a) R))) i j = _
  simp [Matrix.reindexAlgEquiv_apply]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n p : ℕ} {G : GAtP p}
  {A : LocAt F E n G} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} {S : StepLevel F E σ J T f bad}
  {cl : Type} {y : cl → UPts σ J (FiniteAdeleRing (𝓞 F) F)}

theorem ptEps_spec (H1 : OneHyp S A y) (i : G.comp) (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v)) :
    A.IsPt i g (Classical.epsilon fun x => A.IsPt i g x ∧ x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) ∧
      (Classical.epsilon fun x => A.IsPt i g x ∧ x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) := by
  obtain ⟨c, γ₀, κ₀, hγ₀, hp⟩ := ptEx_of H1.good S y H1.y_bij.2 i g
  exact Classical.epsilon_spec (p := fun x => A.IsPt i g x ∧ x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F))
    ⟨_, hp, Subgroup.mul_mem _ (Subgroup.mul_mem _ (bc_mem hγ₀) (y c).2) (U_le κ₀.2)⟩

theorem pt_gen (H1 : OneHyp S A y) (i : G.comp) (γ : (G.lev i).Γ) (L : G.P.Tup) (hL : G.P.IsLatTup L) (κa : S.U)
    (hκa : A.IsAway i γ κa.1) (bas : G.P.Tup → ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v))
    (hbas : ∀ L' v, bas L' v = Classical.epsilon fun g : GL (Fin (G.P.m + 1)) (G.P.Qq v) =>
      L' v = colSpan (G.P.W v) (g : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))) :
    ∃ κ : S.U, (Classical.epsilon fun x => A.IsPt i (bas ((G.lev i).smul γ L)) x ∧ x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) =
      GlobalTheory.TwU.ratA F (A.gamI i γ) * (Classical.epsilon fun x => A.IsPt i (bas L) x ∧ x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) * κ.1 ∧
      S.chi κ * S.chi κa = 1 := by
  obtain ⟨g0, hg0⟩ := exists_bases1 L hL
  have hb : ∀ (L' : G.P.Tup) (g1 : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v)),
      (∀ v, L' v = colSpan (G.P.W v) (g1 v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))) →
      ∀ v, L' v = colSpan (G.P.W v) (bas L' v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)) := by
    intro L' g1 h v
    rw [hbas]
    exact Classical.epsilon_spec (p := fun g : GL (Fin (G.P.m + 1)) (G.P.Qq v) =>
      L' v = colSpan (G.P.W v) (g : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))) ⟨g1 v, h v⟩
  have hbL := hb L g0 hg0
  have hbγ := hb _ _ (smul_colSpan i γ L g0 hg0)
  have hs := ptEps_spec H1 i (bas L)
  have hs' := ptEps_spec H1 i (bas ((G.lev i).smul γ L))
  exact GlobalTheory.TwV.Xc.isPt_move_eq F E σ n p G A J T f bad S H1.good H1.int H1.hypP H1.actB H1.bad_p i γ (H1.gamU i γ) κa hκa
    (bas L) (bas ((G.lev i).smul γ L)) (fun v => (hbγ v).symm.trans (smul_colSpan i γ L (bas L) hbL v))
    ⟨_, hs.2⟩ ⟨_, hs'.2⟩ hs.1 hs'.1

end GlobalTheory.TwV.Xc.Mv0

namespace GlobalTheory.TwV.Xc

set_option maxHeartbeats 4000000 in

theorem moveBy_zero : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ (c : (sysS H X std).Lv.comp 0) (La : ((sysS H X std).Pj 0).Tup) (γ : ((sysS H X std).Lv.lev 0 c).Γ), ((sysS H X std).Pj 0).IsLatTup La → ∃ g κ, MoveBy std J 0 (Nat.zero_le _) c La γ g κ) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hS c La γ hL
  have hfr : ∀ (hr : ((sysS H X std).Pj 0).m + 1 = D.R.N 0) (v : (sysS H X std).Pl),
      (J.fd std).frM 0 (c, La) v * (gamAt (sysS H X std) 0 c γ v : Matrix _ _ _) =
        (eMat hr (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) ((A0 J).gamI c γ)).map (J.rho std v) * (J.fd std).frM 0 (c, La) v := by
    intro hr v
    exact Mv0.frm_gen _ (A0 J).rk hr (gramN D 0 (Nat.zero_le _)) (A0 J).B ((A0 J).gamI c γ) ((A0 J).iw v) _ (J.one.actB c v γ)
  obtain ⟨κa, hκa⟩ := awayEx_of J.one.good _ J.one.gam c γ
  obtain ⟨ra, hra1, hra2⟩ := (lev0AtOf_compatible J.Gd.cmp u w hg).chi c γ κa hκa
  have hJpt : ∀ L', (J.pt std 0 (Nat.zero_le _) (c, L')).1 = Classical.epsilon fun x => (A0 J).IsPt c (basesAt _ std _ _ _ _ _ _ _ 0 L') x ∧
      x ∈ UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
    intro L'
    have hs := Mv0.ptEps_spec J.one c (basesAt _ std _ _ _ _ _ _ _ 0 L')
    have hspec : J.IsPt std 0 (Nat.zero_le _) (c, L') (J.pt std 0 (Nat.zero_le _) (c, L')) :=
      Classical.epsilon_spec (p := J.IsPt std 0 (Nat.zero_le _) (c, L')) ⟨⟨_, hs.2⟩, (A0 J).rk, (Mv0.regl2 _ _ _).symm⟩
    obtain ⟨hr, e⟩ := hspec
    rw [e]
    exact Mv0.regl2 _ _ _
  obtain ⟨κ, hκ1, hκ2⟩ := Mv0.pt_gen J.one c γ La hL κa hκa (basesAt _ std _ _ _ _ _ _ _ 0) (fun L' v => rfl)
  obtain ⟨-, -, hU, hchi⟩ := J.lev0 (J.chart std 0 (Nat.zero_le _) (c, La))
  have hmem : κ.1 ∈ ((J.St 0 (Nat.zero_le _)).K (J.chart std 0 (Nat.zero_le _) (c, La))).lev.U := by rw [hU]; exact κ.2
  refine ⟨(A0 J).gamI c γ, ⟨κ.1, hmem⟩, J.one.gamU c γ, ?_, hfr, ra⁻¹, ?_, ?_⟩
  · exact (hJpt _).trans (hκ1.trans (by rw [hJpt]))
  · rw [hchi ⟨κ.1, hmem⟩ κ rfl, map_inv₀, hra1, ← Units.val_inv_eq_inv_val]
    exact congrArg (fun z : ℂˣ => (z : ℂ)) (eq_inv_of_mul_eq_one_left hκ2).symm
  · rw [map_inv₀]
    exact eq_inv_of_mul_eq_one_left hra2

end GlobalTheory.TwV.Xc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroLevelStatementsOfJointStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.step_zero_level_statements_of_joint : ∀ {D : D7} (Gt : GatTies D) (c : LatCmp D) (g : GroupCompatibilityAll D Gt c) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), Joint0 g.herm.lev0 u (g.forms u) → OneHyp ((g.forms u).cls0).toChart.lev (lev0At g u w hg).A ((g.forms u).cls0).toChart.y := by
  first | exact @GlobalTheory.Port.oneHyp_lev0At | exact GlobalTheory.Port.oneHyp_lev0At | (intros; apply GlobalTheory.Port.oneHyp_lev0At <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SystemWeightsEqShiftedCharacterExponents
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.Xc

theorem wG_succ_eq_shift (R : Ranks) (z : ℤ) (j : ℕ) :
    Formalism.BasicNotions.wG R (z : ℚ) (j + 1) = ((z - ((j * (R.t + 1) / 2 : ℕ) : ℤ) - ((R.N (j + 1) / 2 : ℕ) : ℤ) : ℤ) : ℚ) := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨b, hb⟩ := R.t_odd
  have h1 : j * (R.t + 1) / 2 = j * (b + 1) := by
    rw [hb, show j * (2 * b + 1 + 1) = 2 * (j * (b + 1)) by ring]; omega
  have h2 : R.N (j + 1) / 2 = a + (j + 1) * (b + 1) := by
    show (R.k + (j + 1) * (R.t + 1)) / 2 = _
    rw [hb, ha, show a + a + (j + 1) * (2 * b + 1 + 1) = 2 * (a + (j + 1) * (b + 1)) by ring]; omega
  rw [h1, h2]
  unfold Formalism.BasicNotions.wG
  rw [ha, hb]
  push_cast
  ring

set_option maxHeartbeats 4000000 in

theorem fillAt_of_comp : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    ∀ j (hj : j < D.R.m), (sysS H X std).Lv.comp (j + 1) → FillAt (hT := hT) (H := H) (X := X) std j hj) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hS j hj c
  have hj' : j + 1 ≤ D.R.m := hj
  have c' : Lv.comp (j + 1) := c
  have hW := (H.core j hj' ((I.at' j hj').st.eC.symm c').1).wt
  rw [J.pos j hj'] at hW
  have ht : (Gl.Fl u w hg).t = D.R.t := X.fl_t
  have hk := hT.gat_k u w hg
  have rk := rk_of hT w hg (Gl.Fl u w hg) ht j
  intro e he v s
  show (Gl.Fl u w hg).w v (j + 1) s = e (hT.gat_pos u w hg ⟨v, s⟩) - ((j * ((Gl.Fl u w hg).t + 1) / 2 : ℕ) : ℤ) -
      (((((Gl.Fl u w hg).Pj (j + 1)).m + 1) / 2 : ℕ) : ℤ)
  have hlt : (D.gat u w hg).P.m + 1 + j * ((Gl.Fl u w hg).t + 1) < ((Gl.Fl u w hg).Pj (j + 1)).m + 1 := by
    show _ < (D.gat u w hg).P.m + (j + 1) * ((Gl.Fl u w hg).t + 1) + 1
    nlinarith
  have h := hW v s ⟨_, hlt⟩
  have h0 := (congrArg (fun z : ℤ => (z : ℚ)) h).trans (((I.at' j hj').M).lam_eq (j + 1) hj' (hT.gat_pos u w hg ⟨v, s⟩) _)
  have hi : ¬ (D.gat u w hg).P.m + 1 + j * ((Gl.Fl u w hg).t + 1) < D.R.k := by omega
  have hq : ((D.gat u w hg).P.m + 1 + j * ((Gl.Fl u w hg).t + 1) - D.R.k) / (D.R.t + 1) = j := by
    rw [← hk, ← ht, Nat.add_sub_cancel_left]; exact Nat.mul_div_cancel _ (Nat.succ_pos _)
  simp only [finCongr_apply, Fin.coe_cast] at h0
  rw [dif_neg hi] at h0
  simp only [hq] at h0
  have hL : ((Gl.Fl u w hg).Pj (j + 1)).lam0 v s ⟨_, hlt⟩ = -((Gl.Fl u w hg).w v (j + 1) s) := by
    show liftWt (Gl.Fl u w hg).t (D.gat u w hg).P.m ((D.gat u w hg).P.lam0 v s) (fun a => (Gl.Fl u w hg).w v a s) (j + 1) ⟨_, hlt⟩ = _
    unfold liftWt
    rw [dif_neg (Nat.not_lt.mpr (Nat.le_add_right _ _))]
    congr 2
    simp only [Nat.add_sub_cancel_left]
    rw [Nat.mul_div_cancel _ (Nat.succ_pos _)]
  rw [hL, Int.cast_neg, neg_inj, D.hcW_e, ← he] at h0
  rw [rk, ht]
  apply Int.cast_injective (α := ℚ)
  rw [h0]
  exact wG_succ_eq_shift D.R _ j

end GlobalTheory.TwV.Xc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TaylorSeriesMatrixPullbackEqLinearSubstitution
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelB

theorem pull_eq_linear (D : D7) (T : TaylorLogMetric.Tor D) (hT : ∀ τ, T.emb τ = TaylorLogMetric.embT D τ) {a b : ℕ}
    (e : Matrix (Fin a) (Fin a) D.host.E) (e' : Matrix (Fin b) (Fin b) D.host.E) (Θ : TaylorLogMetric.VC D a b → ℂ) :
    TaylorLogMetric.pull D T e e' Θ = fun z => Θ (fun τ i j =>
      ∑ x : D.what₂.Tau × Fin b × Fin a, pullMat e e' (τ, i, j) x * z x.1 x.2.1 x.2.2) := by
  funext z
  unfold TaylorLogMetric.pull
  congr 1
  funext τ i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.of_apply, hT,
    Fintype.sum_prod_type, pullMat]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_mul]
  rw [Finset.sum_comm]
  rw [Fintype.sum_eq_single τ (fun x hx => by simp [Ne.symm hx])]
  simp only [if_true]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [← Complex.star_def]
  ring

end GlobalTheory.TwV.DelB

namespace GlobalTheory.TwV.DelB

theorem tay_eq_taylorDir (D : D7) {a b : ℕ} (G : TaylorLogMetric.VC D a b → ℂ) :
    tay G = taylorDir (Formalism.MainNotions.TaylorLogMetric.coordV D) G := by
  ext α
  exact GlobalTheory.ConjSeries.taylor_eq_coeff D G α

theorem tay_pull_linSub : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {a b : ℕ} (e : Matrix (Fin a) (Fin a) D.host.E) (e' : Matrix (Fin b) (Fin b) D.host.E) (Θ : TaylorLogMetric.VC D a b → ℂ), Differentiable ℂ Θ → tay (TaylorLogMetric.pull D (TaylorLogMetric.tor0 D cc δ) e e' Θ) = linSub (pullMat e e') (tay Θ) := by
  intro D cc δ a b e e' Θ hΘ
  rw [pull_eq_linear D (TaylorLogMetric.tor0 D cc δ) (fun _ => rfl) e e' Θ, tay_eq_taylorDir, tay_eq_taylorDir, linSub]
  exact GlobalTheory.PSerLin.taylorDir_linear D Θ (pullMat e e') hΘ

end GlobalTheory.TwV.DelB
end

