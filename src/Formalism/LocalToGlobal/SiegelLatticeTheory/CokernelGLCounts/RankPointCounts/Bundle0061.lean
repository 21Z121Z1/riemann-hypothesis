import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NormBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.GflagSwap
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.VolPinAsm
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0008
import Formalism.SharpRestriction.CuspSpanNormBounds.OscillatoryIntegralBounds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0058
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0049
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0013
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0039
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0017
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.EmbeddingIntegerAlgebraMap
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.Bundle0003

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AbsNormTG
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace Formalism.L2.SG.NGCut.NormalIntegrality

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem zhat_int {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hun : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ)
    {T T' : D.host.E} (F : FlagG (VS D) D.R.rS T) (F' : FlagG (VS D) D.R.rS T')
    (hF : ∀ b, F.fvec b ∈ Λ) (hF' : ∀ b, F'.fvec b ∈ Λ) :
    ∃ FinalForm : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E),
      Zhat F F' = FinalForm.map (algebraMap (𝓞 D.host.E) D.host.E) := by
  have hmem : ∀ a b, ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = Zhat F F' a b := by
    intro a b
    have hx : F'.fvec b ∈ Formalism.HermitianLatticesTheory.dual (VS D).hT Λ := by
      rw [show Formalism.HermitianLatticesTheory.dual (VS D).hT Λ = Λ from hun]
      exact hF' b
    unfold Formalism.HermitianLatticesTheory.dual Formalism.E.hdual at hx
    have h1 := (Submodule.mem_iInf _).mp hx (F.fvec a)
    have h2 := (Submodule.mem_iInf _).mp h1 (hF a)
    rw [Submodule.mem_comap] at h2
    exact Submodule.mem_one.mp h2
  choose FinalForm hZo using hmem
  exact ⟨Matrix.of FinalForm, by ext a b; exact (hZo a b).symm⟩

theorem yv_mem {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hun : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ)
    (n : ℕ) {T' : D.host.E} (F : FlagG (VS D) D.R.rS (n : D.host.E)) (F' : FlagG (VS D) D.R.rS T')
    (hF : ∀ b, F.fvec b ∈ Λ) (hF' : ∀ b, F'.fvec b ∈ Λ) : NormalVectorPairings.yv F F' ∈ Λ := by
  obtain ⟨FinalForm, hZo⟩ := zhat_int hun F F' hF hF'
  have hadj : (Zhat F F').adjugate = FinalForm.adjugate.map (algebraMap (𝓞 D.host.E) D.host.E) := by
    rw [hZo]
    exact (RingHom.map_adjugate _ _).symm
  have hD : Dl F F' (D.R.rS + 1) = algebraMap (𝓞 D.host.E) D.host.E
      ((FinalForm.submatrix (Fin.castLE le_rfl) (Fin.castLE le_rfl)).det) := by
    unfold Dl leadMinorE
    rw [dif_pos le_rfl, hZo, Matrix.submatrix_map, RingHom.map_det]
    rfl
  unfold NormalVectorPairings.yv NormalVectorPairings.omp
  refine Λ.add_mem ?_ ?_
  · rw [Nat.cast_smul_eq_nsmul]
    refine nsmul_mem (Λ.sum_mem fun b _ => ?_) n
    rw [hadj, Matrix.map_apply, algebraMap_smul]
    exact Λ.smul_mem _ (hF' b)
  · rw [hD, algebraMap_smul]
    have hz : F.z = F.fvec (Fin.last _) := by simp [FlagG.fvec]
    rw [hz]
    exact Λ.smul_mem _ (hF _)

theorem yv_orth_X {T T' : D.host.E} (F : FlagG (VS D) D.R.rS T) (F' : FlagG (VS D) D.R.rS T') :
    ∀ x ∈ F.X, brS (VS D) (NormalVectorPairings.yv F F') x = 0 := by
  have key : ∀ a : Fin D.R.rS, (VS D).hT (F.e a) (NormalVectorPairings.yv F F') = 0 := by
    intro a
    have hz : ∀ b, (VS D).hT (F.e a) (F'.fvec b) = Zhat F F' a.castSucc b := by
      intro b
      simp [Zhat, brS, FlagG.fvec, Fin.snoc_castSucc]
    have hm := congrFun (congrFun (Matrix.mul_adjugate (Zhat F F')) a.castSucc) (Fin.last _)
    rw [Matrix.mul_apply] at hm
    simp only [Matrix.smul_apply, Matrix.one_apply, Fin.castSucc_ne_last, if_false, smul_zero] at hm
    unfold NormalVectorPairings.yv NormalVectorPairings.omp
    rw [map_add, map_smul, map_smul, F.z_orth a, smul_zero, add_zero, map_sum]
    simp only [map_smul, smul_eq_mul, hz]
    rw [show ∑ b, (Zhat F F').adjugate b (Fin.last D.R.rS) * Zhat F F' a.castSucc b =
        ∑ b, Zhat F F' a.castSucc b * (Zhat F F').adjugate b (Fin.last D.R.rS) from
      Finset.sum_congr rfl fun b _ => mul_comm _ _, hm, mul_zero]
  intro x hx
  simp only [brS]
  refine Submodule.span_induction (p := fun y _ => (VS D).hT y (NormalVectorPairings.yv F F') = 0) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨a, rfl⟩
    exact key a
  · simp
  · intro y z _ _ hy hz
    simp [hy, hz]
  · intro c y _ hy
    simp [hy]

theorem X_iso {T : D.host.E} (F : FlagG (VS D) D.R.rS T) : ∀ x ∈ F.X, ∀ x' ∈ F.X, brS (VS D) x x' = 0 := by
  intro x hx x' hx'
  simp only [brS]
  refine Submodule.span_induction (p := fun y _ => (VS D).hT y x = 0) ?_ ?_ ?_ ?_ hx'
  · rintro _ ⟨b, rfl⟩
    refine Submodule.span_induction (p := fun y _ => (VS D).hT (F.e b) y = 0) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨a, rfl⟩
      exact F.e_iso b a
    · simp
    · intro y z _ _ hy hz
      simp [hy, hz]
    · intro c y _ hy
      simp [hy]
  · simp
  · intro y z _ _ hy hz
    simp [hy, hz]
  · intro c y _ hy
    simp [hy]

theorem abs_norm_TG (n : ℕ) (g : D.host.E) :
    |((Algebra.norm ℚ ((n : D.host.E) * g) : ℚ) : ℝ)| =
      (n : ℝ) ^ (2 * D.R.f) * (∏ w : InfinitePlace D.host.E, w g) ^ 2 := by
  have hc : ∀ w : InfinitePlace D.host.E, w.mult = 2 := by
    intro w
    have hnr : ¬ w.IsReal := by
      intro hw
      have hr := InfinitePlace.isReal_iff.mp hw
      have h2 : starRingEnd ℂ (w.embedding D.host.sqq) = w.embedding D.host.sqq :=
        RingHom.congr_fun hr _
      have h1 : w.embedding D.host.sqq ^ 2 = w.embedding (-(D.host.q : D.host.E)) := by
        rw [← map_pow, D.host.sqq_sq]
      have h3 := Complex.conj_eq_iff_re.mp h2
      rw [← h3, map_neg, map_natCast] at h1
      have h4 := congrArg Complex.re h1
      simp only [pow_two, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
        Complex.neg_re, Complex.natCast_re] at h4
      have hq0 : 0 < D.host.q := by have := D.host.qd_big.1; omega
      have hq : (0 : ℝ) < D.host.q := by exact_mod_cast hq0
      nlinarith [mul_self_nonneg (w.embedding D.host.sqq).re]
    simp [InfinitePlace.mult, hnr]
  have hprod := InfinitePlace.prod_eq_abs_norm g
  simp only [hc, Finset.prod_pow] at hprod
  rw [← map_natCast (algebraMap ℚ D.host.E) n, map_mul, Algebra.norm_algebraMap,
    Formalism.MainNotions.BridgeLemma.szf_finrankE D, hprod]
  push_cast
  rw [abs_mul, abs_pow, Nat.abs_cast]

end Formalism.L2.SG.NGCut.NormalIntegrality
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ChartC
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.NGCut.SplitEmbedding

namespace Formalism.L2.SG.NGCut.StabilizerCovolume

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ht {D : D7} {w : Point D.host.E (D.R.rS + 1)} (p : Formalism.L2.SG.RealObj.FreeE w) : ℕ := p.1.2.val - p.1.1.val

def ChartC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (t : TT Y u u'), t.relevant → t.G ≠ 0 →
    ∀ w, t.toTerm.atPt w → ∀ (γw s s' : X.B.I.Ginf),
      Formalism.L2.SG.RealObj.IsPtRep X u u' w γw → s ∈ X.SinfU u → s' ∈ X.SinfU u' → t.pt.1 = s * γw * s'⁻¹ →
      ∃ BX : Formalism.L2.SG.RealObj.FreeE w → (Formalism.L2.SG.RealObj.FreeE w → ℂ) → (Formalism.L2.SG.RealObj.FreeE w → ℂ) → ℂ,
        (∀ p, Measurable (fun z : (Formalism.L2.SG.RealObj.FreeE w → ℂ) × (Formalism.L2.SG.RealObj.FreeE w → ℂ) => BX p z.1 z.2)) ∧
        (∀ p (x x' y y' : Formalism.L2.SG.RealObj.FreeE w → ℂ), (∀ q, ht q < ht p → x q = x' q ∧ y q = y' q) →
          BX p x y = BX p x' y') ∧
        (∀ p (x : Formalism.L2.SG.RealObj.FreeE w → ℂ), BX p x 0 = 0) ∧
        Measurable (Formalism.L2.SG.RealObj.stCoord X u' w γw) ∧
        MeasurableSet (Formalism.L2.SG.RealObj.StInf X u u' γw) ∧
        Set.InjOn (Formalism.L2.SG.RealObj.stCoord X u' w γw) (Formalism.L2.SG.RealObj.StInf X u u' γw) ∧
        (∀ x, ∃ z ∈ Formalism.L2.SG.RealObj.StInf X u u' γw, Formalism.L2.SG.RealObj.stCoord X u' w γw z = x) ∧
        (∀ z₁ ∈ Formalism.L2.SG.RealObj.StInf X u u' γw, ∀ z₂ ∈ Formalism.L2.SG.RealObj.StInf X u u' γw,
          z₁ * z₂ ∈ Formalism.L2.SG.RealObj.StInf X u u' γw ∧
          Formalism.L2.SG.RealObj.stCoord X u' w γw (z₁ * z₂) =
            lawX BX (Formalism.L2.SG.RealObj.stCoord X u' w γw z₁) (Formalism.L2.SG.RealObj.stCoord X u' w γw z₂)) ∧
        (∀ r ∈ Formalism.L2.SG.TermOp.Vanish.Rset t, s⁻¹ * r * s ∈ Formalism.L2.SG.RealObj.StInf X u u' γw)

def LatC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (t : TT Y u u'), t.relevant → t.G ≠ 0 →
    ∀ w, t.toTerm.atPt w → ∀ (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L U : Formalism.L2.SG.PairVal.MatR D),
      Formalism.L2.SG.PairVal.NormRep t.toTerm w F' L U → ∀ (γw s s' : X.B.I.Ginf),
      Formalism.L2.SG.RealObj.IsPtRep X u u' w γw → s ∈ X.SinfU u → s' ∈ X.SinfU u' → t.pt.1 = s * γw * s'⁻¹ →
      ∀ (c : X.B.I.Ginf) (Φ : Formalism.L2.SG.Pf.VolPinAsm.StG w →* X.B.I.Ginf),
        Formalism.L2.SG.Pf.VolPinAsm.DictProps t w F' L γw s c Φ →
      ∃ (σ : Formalism.L2.SG.RealObj.FreeE w → ℂ) (h' : Formalism.L2.SG.RealObj.FreeE w → ℕ) (I : Formalism.L2.SG.RealObj.FreeE w → (FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)ˣ)
        (Λ : Formalism.L2.SG.RealObj.FreeE w → AddSubgroup D.host.E) (k : Formalism.L2.SG.RealObj.FreeE w → ℕ)
        (τ : Formalism.L2.SG.RealObj.FreeE w → (InfinitePlace X.B.I.F → Formalism.L2.SG.RealObj.FreeE w → ℂ) → (InfinitePlace X.B.I.F → ℂ))
        (σι : InfinitePlace X.B.I.F ≃ {w : InfinitePlace D.host.E // w.IsComplex}),
        (∀ p q, ht q < ht p → h' q < h' p) ∧
        (∀ v, Formalism.L2.SG.Pf.VolPinAsm.phiV X v = (σι v).1.embedding ∨
          Formalism.L2.SG.Pf.VolPinAsm.phiV X v = ComplexEmbedding.conjugate (σι v).1.embedding) ∧
        (∀ p, ∀ a ∈ Λ p, a ∈ (I p : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) ∧
        (∀ p, (Λ p).relIndex
          (((I p : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Submodule (𝓞 D.host.E) D.host.E).toAddSubgroup) = k p) ∧
        (∀ p, k p ≠ 0) ∧ (∀ p, σ p ≠ 0) ∧
        (∀ p (x x' : InfinitePlace X.B.I.F → Formalism.L2.SG.RealObj.FreeE w → ℂ),
          (∀ q, h' q < h' p → ∀ v, x v q = x' v q) → τ p x = τ p x') ∧
        (∀ x : InfinitePlace X.B.I.F → Formalism.L2.SG.RealObj.FreeE w → ℂ,
          (∃ β : Formalism.L2.SG.Pf.VolPinAsm.StG w, (β : Formalism.L2.SG.PairVal.GLR D) ∈ Formalism.L2.SG.PairVal.stabInt D u u' Y.δ Y.M w ∧
            x = Formalism.L2.SG.RealObj.stCoord X u' w γw (s⁻¹ * (c⁻¹ * Φ β * c) * s)) ↔
          ∀ p, (fun v => x v p) - τ p x ∈ (Λ p).map (embS (Formalism.L2.SG.Pf.VolPinAsm.phiV X) (σ p))) ∧
        0 ≤ D.host.ka / (X.B.g : ℝ) / Real.pi ∧
        ∏ p, ((D.host.ka / (X.B.g : ℝ) / Real.pi) ^ Fintype.card (InfinitePlace X.B.I.F) * k p *
          (FractionalIdeal.absNorm (I p : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : ℝ) *
          2⁻¹ ^ Fintype.card (InfinitePlace X.B.I.F) * √|(discr D.host.E : ℝ)| *
          ‖σ p‖ ^ (2 * Fintype.card (InfinitePlace X.B.I.F))) = 1

end Formalism.L2.SG.NGCut.StabilizerCovolume
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CrossTranspose
section
noncomputable section

open Matrix

namespace Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents

variable {K K' : Type*} [CommRing K] [CommRing K'] {r : ℕ}

def ld (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) : K := (A.submatrix Fin.castSucc Fin.castSucc).det

def Ec (r : ℕ) : Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
  Matrix.of fun a b => if a = Fin.last r ∧ b = Fin.last r then 1 else 0

theorem ld_add_corner (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (t : K) : ld (A + t • Ec r) = ld A := by
  unfold ld
  congr 1
  ext a b
  simp [Ec, Fin.castSucc_ne_last]

theorem det_add_corner (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (t : K) :
    (A + t • Ec r).det = A.det + t * ld A := by
  have hE : A + t • Ec r = A.updateRow (Fin.last r) (A (Fin.last r) + t • Pi.single (Fin.last r) 1) := by
    ext a b
    by_cases ha : a = Fin.last r
    · subst ha
      by_cases hb : b = Fin.last r
      · subst hb; simp [Ec]
      · simp [Ec, hb]
    · simp [Ec, ha]
  rw [hE, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]
  congr 2
  rw [Matrix.det_succ_row _ (Fin.last r), Fin.sum_univ_castSucc]
  have h0 : ∀ j : Fin r, (A.updateRow (Fin.last r) (Pi.single (Fin.last r) 1)) (Fin.last r) j.castSucc = 0 := by
    intro j
    rw [Matrix.updateRow_self, Pi.single_eq_of_ne (Fin.castSucc_ne_last j)]
  simp only [h0, mul_zero, zero_mul, Finset.sum_const_zero, zero_add, Matrix.updateRow_self,
    Pi.single_eq_same, mul_one, Fin.succAbove_last]
  have hs : (A.updateRow (Fin.last r) (Pi.single (Fin.last r) 1)).submatrix Fin.castSucc Fin.castSucc =
      A.submatrix Fin.castSucc Fin.castSucc := by
    ext a b
    simp only [Matrix.submatrix_apply]
    rw [Matrix.updateRow_ne (Fin.castSucc_ne_last a)]
  rw [hs, ld]
  have hpow : ((-1 : K) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ))) = 1 := Even.neg_one_pow ⟨_, rfl⟩
  rw [hpow, one_mul]

theorem ld_smul (c : K) (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) : ld (c • A) = c ^ r * ld A := by
  unfold ld
  rw [show (c • A).submatrix Fin.castSucc Fin.castSucc = c • A.submatrix Fin.castSucc Fin.castSucc from rfl,
    Matrix.det_smul, Fintype.card_fin]

theorem ld_transpose (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) : ld Aᵀ = ld A := by
  unfold ld
  rw [← Matrix.det_transpose]
  rfl

theorem ld_map (f : K →+* K') (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) : ld (A.map f) = f (ld A) := by
  unfold ld
  rw [RingHom.map_det]
  rfl

def Cross (A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) K) : Prop := ld A * A'.det = ld A' * A.det

theorem cross_shift {A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : Cross A A') (c t : K) :
    Cross (c • A + t • Ec r) (c • A' + t • Ec r) := by
  unfold Cross at h ⊢
  rw [ld_add_corner, ld_add_corner, det_add_corner, det_add_corner, ld_smul, ld_smul, Matrix.det_smul,
    Matrix.det_smul, Fintype.card_fin]
  linear_combination c ^ r * c ^ (r + 1) * h

theorem cross_transpose {A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : Cross A A') : Cross Aᵀ A'ᵀ := by
  unfold Cross at h ⊢
  rw [ld_transpose, ld_transpose, Matrix.det_transpose, Matrix.det_transpose]
  exact h

theorem cross_map (f : K →+* K') {A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : Cross A A') :
    Cross (A.map f) (A'.map f) := by
  unfold Cross at h ⊢
  have e1 : (A'.map f).det = f A'.det := (RingHom.map_det f A').symm
  have e2 : (A.map f).det = f A.det := (RingHom.map_det f A).symm
  rw [ld_map, ld_map, e1, e2, ← map_mul, ← map_mul, h]

theorem cross_scale (x y : Fin (r + 1) → K) {A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : Cross A A') :
    Cross (Matrix.of fun a b => y b * x a * A a b) (Matrix.of fun a b => y b * x a * A' a b) := by
  have e : ∀ B : Matrix (Fin (r + 1)) (Fin (r + 1)) K,
      (Matrix.of fun a b => y b * x a * B a b) = Matrix.diagonal x * B * Matrix.diagonal y := by
    intro B; ext a b; simp [Matrix.diagonal_mul, Matrix.mul_diagonal]; ring
  have el : ∀ B : Matrix (Fin (r + 1)) (Fin (r + 1)) K,
      ld (Matrix.diagonal x * B * Matrix.diagonal y) = (∏ i : Fin r, x i.castSucc) * (∏ i : Fin r, y i.castSucc) * ld B := by
    intro B
    unfold ld
    have : (Matrix.diagonal x * B * Matrix.diagonal y).submatrix Fin.castSucc Fin.castSucc =
        Matrix.diagonal (fun i : Fin r => x i.castSucc) * B.submatrix Fin.castSucc Fin.castSucc *
          Matrix.diagonal (fun i : Fin r => y i.castSucc) := by
      ext a b; simp [Matrix.diagonal_mul, Matrix.mul_diagonal]
    rw [this, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal]
    ring
  unfold Cross at h ⊢
  rw [e, e, el, el, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul]
  linear_combination (∏ i : Fin r, x i.castSucc) * (∏ i : Fin r, y i.castSucc) * (Matrix.diagonal x).det *
    (Matrix.diagonal y).det * h

theorem kappa_eq {A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : Cross A A') (c : K)
    (hu : IsUnit (A + c • (Ec (K := K) r)).det) (hu' : IsUnit (A' + c • (Ec (K := K) r)).det) :
    (A + c • (Ec (K := K) r))⁻¹ (Fin.last r) (Fin.last r) = (A' + c • (Ec (K := K) r))⁻¹ (Fin.last r) (Fin.last r) := by
  have k1 := SplitCoefficientComponents.inv_last_mul_det (A + c • (Ec (K := K) r)) hu
  have k2 := SplitCoefficientComponents.inv_last_mul_det (A' + c • (Ec (K := K) r)) hu'
  have l1 : ((A + c • (Ec (K := K) r)).submatrix Fin.castSucc Fin.castSucc).det = ld A := ld_add_corner A c
  have l2 : ((A' + c • (Ec (K := K) r)).submatrix Fin.castSucc Fin.castSucc).det = ld A' := ld_add_corner A' c
  rw [l1, det_add_corner] at k1
  rw [l2, det_add_corner] at k2
  rw [det_add_corner] at hu hu'
  unfold Cross at h
  obtain ⟨v, hv⟩ := hu
  obtain ⟨v', hv'⟩ := hu'
  have key : (A + c • (Ec (K := K) r))⁻¹ (Fin.last r) (Fin.last r) * ((A.det + c * ld A) * (A'.det + c * ld A')) =
      (A' + c • (Ec (K := K) r))⁻¹ (Fin.last r) (Fin.last r) * ((A.det + c * ld A) * (A'.det + c * ld A')) := by
    have e1 : (A + c • (Ec (K := K) r))⁻¹ (Fin.last r) (Fin.last r) * ((A.det + c * ld A) * (A'.det + c * ld A')) =
        ld A * (A'.det + c * ld A') := by rw [← mul_assoc, k1]
    have e2 : (A' + c • (Ec (K := K) r))⁻¹ (Fin.last r) (Fin.last r) * ((A.det + c * ld A) * (A'.det + c * ld A')) =
        ld A' * (A.det + c * ld A) := by rw [mul_comm (A.det + _), ← mul_assoc, k2]
    rw [e1, e2]
    linear_combination h
  have hunit : IsUnit ((A.det + c * ld A) * (A'.det + c * ld A')) := by
    rw [← hv, ← hv']; exact (v * v').isUnit
  exact hunit.mul_right_cancel key

end Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DiagCL
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.FourierDecayAlt

namespace Formalism.L2.SG.RowsConc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def DiagCL : Prop :=
  ∀ Cg cb Cw cT CT C0 A : ℝ, ∃ CB C4 : ℝ, 0 ≤ CB ∧ 0 ≤ C4 ∧ ∀ CG : ℝ, max CB C4 + 1 ≤ CG → ∃ C'₀ Cl₀ : ℝ,
    ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Formalism.MainNotions.S.Cnt.Hyp D large₂ u u C' Cl Cg cb Cw cT CT C0 A → Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoParameterConditions D large₂ Cl Cg CT →
      ConcTie X Y → (Y.tO u u).AbsConv → large₂.CGam = CG →
      (Y.tO u u).RowBig (epsL D) (ddC X Y u u) → (Y.tO u u).RowNotScalar (epsL D) (ddC X Y u u) →
      Formalism.L2.SG.RowsOther.DiagRow (Y.tO u u) (oneC X Y u) (D.mem u).A.GamP (ddC X Y u u)

theorem diagCL_of_rows (hA : PB.PairBoundAbstract) (hP : PB.NormSqBoundOfEqualIota) (hE : PB.GramSumLeOfPosSemidef) (hS : PB.PairSplit)
    (hSub : PB.SubFamily) (hGG : Formalism.L2.SG.GGMirabolic.TermsGGBound)
    (hNS : NormExpSatTied) (hC : CorankPosC) (hId : IdOneC) (hNG : RowNGC) (hM : RowMainEqC)
    (hNum : DiagNumC) : DiagCL := by
  intro Cg cb Cw cT CT C0 A
  obtain ⟨CB, hCB, C'₁, Cl₁, hM'⟩ := hM Cg cb Cw cT CT C0 A
  obtain ⟨C4, hC4, C'₂, Cl₂, hNG'⟩ := hNG Cg cb Cw cT CT C0
  obtain ⟨C'₄, Cl₄, hNum'⟩ := hNum Cg cb Cw cT CT C0 A CB C4 hCB hC4
  refine ⟨CB, C4, hCB, hC4, fun CG hCG => ⟨max (max C'₁ C'₂) C'₄, max (max Cl₁ Cl₂) Cl₄,
    fun C' Cl h1 h2 D large₂ X Y u hH hK2 hT ha hG r1 r2 => ?_⟩⟩
  have a1 : C'₁ ≤ C' := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) h1
  have a2 : C'₂ ≤ C' := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) h1
  have a4 : C'₄ ≤ C' := le_trans (le_max_right _ _) h1
  have b1 : Cl₁ ≤ Cl := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) h2
  have b2 : Cl₂ ≤ Cl := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) h2
  have b4 : Cl₄ ≤ Cl := le_trans (le_max_right _ _) h2
  have h0 : Formalism.MainNotions.S.Cnt.Hyp0 D large₂ C' Cl Cg cb Cw cT CT C0 := hH.1
  have hs : Formalism.MainNotions.S.Cnt.Stand D u u := hH.2.1
  have hPg : 0 ≤ PgC Y := Finset.prod_nonneg fun v _ => by positivity
  have hdd := dd_nonneg hT u u
  have r3 := hM' C' Cl a1 b1 D large₂ X Y u hH hT ha
  have r4 := hNG' C' Cl a2 b2 D large₂ X Y u u h0 hs hT ha
  have hGB : (Y.tO u u).GGBound (PgC Y) :=
    Formalism.L2.SG.TermOp.ggBound Y.TR (Y.cs u) (Y.cs u) (Y.FN u) (Y.FN u) hGG Y.psi_ne
      (fun v => card_ge_three hK2 Y.TR v)
  have hD := Formalism.L2.SG.RowsOther.diag_of_abstract (Y.tO u u) hA hP hE hS hSub (oneC X Y u) (PgC Y)
    (gamB D large₂ CB) (epsL D) (epsNG D large₂ C4) (ddC X Y u u) hPg hdd ha (hNS D X Y u u hT) hGB
    (Formalism.L2.SG.TermOp.rowOrth Y.TR (Y.cs u) (Y.cs u) (Y.FN u) (Y.FN u)) (hC D X Y u u hT) (hId D X Y u hT)
    r1 r2 r3 r4
  unfold Formalism.L2.SG.RowsOther.DiagRow at hD ⊢
  exact hD.trans (mul_le_mul_of_nonneg_right (hNum' C' Cl a4 b4 D large₂ X Y u hH hK2 hT (hG ▸ hCG)) hdd)

end Formalism.L2.SG.RowsConc
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdNF
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdNP

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D)

theorem mem_of_bcP {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Submodule.IsLattice D.host.E Λ) {x : (VS D).V}
    (h : ∀ p, baseChange₂ D p x ∈ lattice₂ D Zd.M p Λ) : x ∈ Λ := by
  refine PI.UnitaryGroupMassFormula.UJClassMass.interLocF (F := D.host.F) Λ hΛ x fun v => ?_
  have := v.isPrime
  have h2 := (Formalism.L2.SG.Pf.LocalDenominators.baseChangeAt_mem_localLattice_iff Zd v hΛ x).1 (h v)
  exact (Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF v.asIdeal Λ x).1 h2

theorem baseChange_mem_localLattice {Λ : Submodule (𝓞 D.host.E) (VS D).V} {x : (VS D).V} (hx : x ∈ Λ) (p : PlF D) :
    baseChange₂ D p x ∈ lattice₂ D Zd.M p Λ := Submodule.subset_span ⟨x, hx, rfl⟩

theorem iE_intD (p : PlF D) {y : D.host.E} (hy : IsIntegral ℤ y) : (D.s.atP p).ιE y ∈ (Zd.M p).L.O := by
  rw [LocFacts.lf_hO Zd p]
  exact Formalism.L2.SG.Pf.StabIntSh.lg_iota_int p ⟨y, hy⟩

theorem int_of_loc {y : D.host.E} (h : ∀ p, (D.s.atP p).ιE y ∈ (Zd.M p).L.O) : IsIntegral ℤ y :=
  Formalism.L2.SG.Pf.StabIntSh.lg_int_of_loc y fun p => by rw [← LocFacts.lf_hO Zd p]; exact h p

theorem localForm_baseChange (p : PlF D) (x y : (VS D).V) :
    (locH Zd p).h (baseChange₂ D p x) (baseChange₂ D p y) = (D.s.atP p).ιE ((VS D).hT y x) :=
  baseChangeAt_form Zd.M p (Zd.hcj p) x y

theorem h_eq (p : PlF D) : (locH Zd p).h = LocFacts₂ Zd.M p := rfl

theorem sd_of_loc {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Submodule.IsLattice D.host.E Λ)
    (hloc : ∀ p, (locH Zd p).IsSelfDual (lattice₂ D Zd.M p Λ)) : BwdNA.SD (VS D) Λ := by
  intro x
  constructor
  · intro hx y hy
    refine int_of_loc Zd fun p => ?_
    rw [← localForm_baseChange]
    exact ((hloc p).2.2 (baseChange₂ D p x)).1 (baseChange_mem_localLattice Zd hx p) (baseChange₂ D p y) (baseChange_mem_localLattice Zd hy p)
  · intro h
    refine mem_of_bcP Zd hΛ fun p => ((hloc p).2.2 _).2 fun w hw => ?_
    rw [h_eq]
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨y, hy, rfl⟩ := hw
      rw [← h_eq, localForm_baseChange]
      exact iE_intD Zd p (h y hy)
    | zero => rw [LocFacts.localForm_zero_right]; exact zero_mem _
    | add a b _ _ ha hb => rw [LocFacts.localForm_add_right]; exact add_mem ha hb
    | smul o w _ hw =>
      change LocFacts₂ Zd.M p (baseChange₂ D p x) ((o : (D.s.atP p).Ep) • w) ∈ _
      rw [LocFacts.localForm_smul_right]
      exact mul_mem (LocFacts.lf_cjM_mem Zd p _ o.2) hw

variable {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem tf (p : PlF D) (γ : TermDef.Term D u u' F0 what₂) (a : Fin (D.R.rS + 1)) :
    (tLoc Zd p γ).f a = (TermLoc.sgnP D p a * frFac Zd.δ p a) • baseChange₂ D p (frame (lf D F0) a) := rfl

theorem tLam (p : PlF D) (γ : TermDef.Term D u u' F0 what₂) : (tLoc Zd p γ).abelian₂ = lattice₂ D Zd.M p γ.lam := rfl

theorem sgnP_last (p : PlF D) : TermLoc.sgnP D p (Fin.last D.R.rS) = 1 := by
  unfold TermLoc.sgnP
  split
  · simp
  · rfl

theorem frFac_last' (p : PlF D) : frFac Zd.δ p (Fin.last D.R.rS) = 1 := by
  unfold frFac; simp

theorem tf_last (p : PlF D) (γ : TermDef.Term D u u' F0 what₂) :
    (tLoc Zd p γ).f (Fin.last D.R.rS) = baseChange₂ D p F0.z := by
  rw [tf, sgnP_last, frFac_last', one_mul, one_smul]
  congr 1
  simp [frame, FlagG.fvec]

theorem frame_cs (i : Fin D.R.rS) : frame (lf D F0) i.castSucc = F0.e i := by
  simp [frame, FlagG.fvec]

theorem unit_of_frame (p : PlF D) (γ : TermDef.Term D u u' F0 what₂) {L : Submodule (Zd.M p).L.O (Vp D p)}
    {T : (D.s.atP p).Fp} (hfr : (locH Zd p).IsFrame L D.R.rS (tLoc Zd p γ).f T) (a : Fin (D.R.rS + 1)) :
    IsUnit (TermLoc.sgnP D p a * frFac Zd.δ p a) := by
  have hs : IsUnit (TermLoc.sgnP D p a) := ⟨⟨TermLoc.sgnP D p a, TermLoc.sgnP D p a, TermLoc.localSign_sq p a, TermLoc.localSign_sq p a⟩, rfl⟩
  refine hs.mul ?_
  by_cases h : IsUnit ((algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Zd.δ p) * (D.s.atP p).ιE (uP p : D.host.E)) ^
      (D.R.rS - a.val))
  · obtain ⟨w, hw⟩ := h
    unfold frFac
    rw [← hw, Ring.inverse_unit]
    exact Units.isUnit _
  · exfalso
    have h0 : frFac Zd.δ p a = 0 := by unfold frFac; exact Ring.inverse_non_unit _ h
    have hne := hfr.1.2.1.ne_zero a
    apply hne
    rw [tf, h0, mul_zero, zero_smul]

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdNP
end
end

