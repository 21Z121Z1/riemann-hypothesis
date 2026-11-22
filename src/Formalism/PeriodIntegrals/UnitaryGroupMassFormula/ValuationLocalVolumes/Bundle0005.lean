import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.Bundle0004
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle0001

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.HostStarConj
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmW

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)

theorem sigR_inclR (e : E) : sigR R σ (inclR R e) = inclR R (σ e) := by
  simp [sigR, inclR]

theorem sigR_tmul_one (x : R) : sigR R σ (x ⊗ₜ[F] (1 : E)) = x ⊗ₜ[F] (1 : E) := by
  simp [sigR]

theorem hform_smul {A : Type} [CommRing A] {M : ℕ} (τ : A →+* A) (J : Matrix (Fin M) (Fin M) A) (c d : A)
    (x y : Fin M → A) : Formalism.UG.hform τ J (c • x) (d • y) = τ c * d * Formalism.UG.hform τ J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hR_ratTup {M k : ℕ} (J : Matrix (Fin M) (Fin M) E) (Y : Fin k → Fin M → E) (a b : Fin k) :
    hR R σ J (ratTup R Y a) (ratTup R Y b) = inclR R (hE σ J (Y a) (Y b)) := by
  simp only [hR, hE, Formalism.UG.hform, JR, ratTup, Matrix.map_apply, map_sum, map_mul, sigR_inclR]
  rfl

end Gen

theorem dV_ne_zero {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) : dV v ≠ 0 := by
  unfold dV
  split_ifs with h
  · exact h.choose_spec.1
  · exact one_ne_zero

theorem alp_ne_zero {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (r : ℕ) (a : Fin (r + 1)) :
    alp v r a ≠ 0 := by
  unfold alp
  split_ifs
  · exact pow_ne_zero _ (inv_ne_zero (dV_ne_zero v))
  · exact one_ne_zero

theorem alp_last {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (r : ℕ) :
    alp v r (Fin.last r) = 1 := by
  simp [alp]

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)

theorem host_star_conj : Formalism.BasicNotions.bridge_star := by
  intro R H x
  have := H.isCMField_hostE
  apply H.φ₀.injective
  change H.φ₀ (NumberField.IsCMField.complexConj H.E x) = H.φ₀ (H.conj x)
  rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]

theorem sig_apply (a : X.B.I.E) : X.B.I.cm.sig a = star a := rfl

theorem hE_crdOf (x y : (VS D).V) :
    hE X.B.I.cm.sig X.B.I.J (crdOf X.B.I X.ιE X.bas x) (crdOf X.B.I X.ιE X.bas y) =
      X.ιE.symm ((VS D).hT x y) := by
  have key : (VS D).hT x y = ∑ i, ∑ j, star (X.bas.repr x i) * (VS D).hT (X.bas i) (X.bas j) *
      X.bas.repr y j := by
    conv_lhs => rw [← X.bas.sum_repr x, ← X.bas.sum_repr y]
    simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul,
      smul_eq_mul, starRingEnd_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  apply X.ιE.injective
  rw [RingEquiv.apply_symm_apply, key]
  simp only [hE, Formalism.UG.hform, crdOf, map_sum, map_mul, RingHom.coe_coe, sig_apply, X.ιE_conj,
    RingEquiv.apply_symm_apply, X.J_eq]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← host_star_conj D.R D.host]

def hv : Fin (D.R.rS + 1 + D.R.rS) → (VS D).V := Fin.append (Fin.snoc X.eX (X.zu u')) X.fY

theorem tupH_eq (a : Fin (D.R.rS + 1 + D.R.rS)) :
    tupH (frameOf X u') a = crdOf X.B.I X.ιE X.bas (hv X u' a) := by
  refine Fin.addCases (fun a => ?_) (fun b => ?_) a
  · rw [hv, Fin.append_left, tupH, Fin.append_left]
    refine Fin.lastCases ?_ (fun i => ?_) a
    · rw [F0, Fin.snoc_last, Fin.snoc_last]; rfl
    · rw [F0, Fin.snoc_castSucc, Fin.snoc_castSucc]; rfl
  · rw [hv, Fin.append_right, tupH, Fin.append_right]; rfl

theorem hT_zero_or (v : PlX X) (a b : Fin (D.R.rS + 1 + D.R.rS)) :
    (VS D).hT (hv X u' a) (hv X u' b) = 0 ∨ scl X v a * scl X v b = 1 := by
  have hs := (VS D).herm
  refine Fin.addCases (fun a => ?_) (fun a => ?_) a <;> refine Fin.addCases (fun b => ?_) (fun b => ?_) b <;>
    simp only [hv, scl, Fin.append_left, Fin.append_right]
  · refine Fin.lastCases ?_ (fun i => ?_) a <;> refine Fin.lastCases ?_ (fun j => ?_) b <;>
      simp only [Fin.snoc_last, Fin.snoc_castSucc]
    · right; rw [alp_last, one_mul]
    · left; exact (hs.eq_iff).1 (X.zu_orth u' j).1
    · left; exact (X.zu_orth u' i).1
    · left; exact X.ee i j
  · refine Fin.lastCases ?_ (fun i => ?_) a <;> simp only [Fin.snoc_last, Fin.snoc_castSucc]
    · left; exact (hs.eq_iff).1 (X.zu_orth u' b).2
    · by_cases h : i = b
      · right; subst h; exact mul_inv_cancel₀ (alp_ne_zero v _ _)
      · left; rw [X.ef, if_neg h]
  · refine Fin.lastCases ?_ (fun j => ?_) b <;> simp only [Fin.snoc_last, Fin.snoc_castSucc]
    · left; exact (X.zu_orth u' a).2
    · by_cases h : j = a
      · right; subst h; exact inv_mul_cancel₀ (alp_ne_zero v _ _)
      · left; refine (hs.eq_iff).1 ?_; rw [X.ef, if_neg h]
  · left; exact X.ff a b

theorem omVGram_holds : OmVGram X u' := by
  intro v
  funext a b
  have hY : ∀ i, yTup X u' v i = sc (E := X.B.I.E) v (scl X v i) • ratTup (Fv X.B.I.F v) (tupH (frameOf X u')) i :=
    fun i => rfl
  show hR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (yTup X u' v a) (yTup X u' v b) =
    inclR (Fv X.B.I.F v) (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) a b)
  rw [hY, hY]
  unfold hR
  rw [hform_smul]
  change sigR (Fv X.B.I.F v) X.B.I.cm.sig (sc v (scl X v a)) * sc v (scl X v b) *
      hR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J _ _ = _
  rw [hR_ratTup]
  simp only [sc, sigR_tmul_one, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  change _ = inclR (Fv X.B.I.F v) (hE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u') a) (tupH (frameOf X u') b))
  rcases hT_zero_or X u' v a b with h | h
  · have h0 : hE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u') a) (tupH (frameOf X u') b) = 0 := by
      rw [tupH_eq, tupH_eq, hE_crdOf, h, map_zero]
    rw [h0, map_zero, mul_zero]
  · rw [h, ← Algebra.TensorProduct.one_def, one_mul]

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVBadTOf
section
noncomputable section

namespace PI.OmVd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory PI.OmLocU
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def PrimT (a : ℕ) : Set (TupV (E := E) v n a) := {X | IsPrim v Λ X}

def prodEtaB (n a : ℕ) : ℝ :=
  ∏ j ∈ Finset.Icc (n - a) n, (1 - (etaV (E := E) v : ℝ) ^ j * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ)))

def GoodP (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  StdHyp σ J ψ ∧ (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) ∧
  IsSDLoc σ J v Λ ∧ UnramAt (E := E) v ∧ a ≤ n ∧ IsPrim v Λ Y

def OrbP (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodP σ J ψ v Λ a Y → ∀ X ∈ PrimT v Λ a, gramR (Fv F v) σ J X = gramR (Fv F v) σ J Y →
    ∃ k ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v, X = k • Y

def FibP (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodP σ J ψ v Λ a Y → (∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ) →
    (∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν) → (∃ fib, IsOm σ J ψ v a fib) →
    ∀ ϖ : Fv F v, IsUnif v ϖ →
    omAt σ J ψ v (gramR (Fv F v) σ J Y) (PrimT v Λ a) =
      dX σ J ψ v a (PrimT v Λ a ∩ NearT v σ J ϖ (gramR (Fv F v) σ J Y)) / dT σ ψ v a (HermP v σ a ϖ)

def CountP (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodP σ J ψ v Λ a Y → (∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ) → ∀ ϖ : Fv F v, IsUnif v ϖ →
    dX σ J ψ v a (PrimT v Λ a ∩ NearT v σ J ϖ (gramR (Fv F v) σ J Y)) =
      ENNReal.ofReal (qv v ^ (-((a : ℤ) ^ 2)) * prodEtaB (E := E) v n a) * dX σ J ψ v a (LamT v Λ a)

def PrimCos (a : ℕ) : Prop :=
  StdHyp σ J ψ → (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) →
    IsSDLoc σ J v Λ → UnramAt (E := E) v → ∀ ϖ : Fv F v, IsUnif v ϖ →
    ∀ X ∈ PrimT v Λ a, ∀ Z ∈ lamN v Λ ϖ a 0, X + Z ∈ PrimT v Λ a

theorem smul_prim {a : ℕ} (k : HA (Fv F v) σ J) (hk : k ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v)
    (Y : TupV (E := E) v n a) (hY : IsPrim v Λ Y) : IsPrim v Λ (k • Y) := by
  have hki : ∀ i, (k • Y) i =
      Matrix.mulVec ((HA.mat (Fv F v) σ J k : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) _) (Y i) :=
    fun i => rfl
  refine ⟨fun i => ?_, fun c hc => hY.2 c ?_⟩
  · rw [hki]; exact (hk (Y i)).1 (hY.1 i)
  · have e : (∑ i, c i • (k • Y) i) =
        Matrix.mulVec ((HA.mat (Fv F v) σ J k : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) _)
          (∑ i, c i • Y i) := by
      rw [Matrix.mulVec_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Matrix.mulVec_smul, hki]
    rw [e] at hc
    exact (hk _).2 hc

end Gen

section Loc

open Formalism.L2.SG.Pf.NcVal.OmVSt Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

def OmVdEx : Prop := ∀ v : PlX X, StdHyp X.B.I.cm.sig X.B.I.J ψ →
  (∃ μ, SdW X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J (Fv X.B.I.F v) (psiV X.B.I.F ψ v) (D.R.rS + 1 + D.R.rS) μ) ∧
    ∃ ν, SdHerm X.B.I.F X.B.I.E X.B.I.cm.sig (Fv X.B.I.F v) (psiV X.B.I.F ψ v) (D.R.rS + 1 + D.R.rS) ν

def OmVdUniq : Prop := ∀ v : PlX X, OmUnique X.B.I.cm.sig X.B.I.J ψ v (D.R.rS + 1 + D.R.rS)

def OmVdOrb : Prop := ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
  OrbP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v)

def OmVdFib : Prop := ∀ v : PlX X, FibP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v)

def OmVdCnt : Prop := ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
  CountP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v)

def OmVdSdW : Prop := ∀ v : PlX X, SdVolW X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS)

def OmVdSdH : Prop := ∀ v : PlX X, SdVolH X.B.I.cm.sig X.B.I.J ψ v (D.R.rS + 1 + D.R.rS)

theorem a_le_n' : D.R.rS + 1 + D.R.rS ≤ X.B.I.n := by
  have h1 := X.n_eq
  have h2 := D.R.rS_two
  unfold Ranks.r at h1
  omega

theorem omVBadT_of (hStd : OmVStd X ψ) (hLat : OmVLat X) (hGram : OmVGram X u')
    (hEx : OmVdEx X ψ) (hUq : OmVdUniq X ψ) (hOrb : OmVdOrb X u' ψ) (hFib : OmVdFib X u' ψ)
    (hCnt : OmVdCnt X u' ψ) (hW : OmVdSdW X ψ) (hH : OmVdSdH X ψ) : OmVBadT X u' ψ := by
  intro hC hS v hv hSD hUn hP
  have hS' := hStd hC hS
  have hG : GoodP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v) :=
    ⟨hS', hLat, hSD, hUn, a_le_n' X, hP⟩
  obtain ⟨ϖ, hϖ⟩ := unifEx_holds v
  obtain ⟨hWe, hHe⟩ := hEx v hS'
  rw [← hGram v]
  set T := gramR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (yTup X u' v) with hTdef
  set ω := omAt X.B.I.cm.sig X.B.I.J ψ v T with hω
  set O := {Y | ∃ k ∈ Kv X.B.I.cm.sig X.B.I.J (abelian₂ X) v, Y = k • yTup X u' v} with hO
  have hsub : O ⊆ PrimT v (abelian₂ X) (D.R.rS + 1 + D.R.rS) := by
    rintro Z ⟨k, hk, rfl⟩
    exact smul_prim X.B.I.cm.sig X.B.I.J v (abelian₂ X) k hk _ hP
  have hsup : PrimT v (abelian₂ X) (D.R.rS + 1 + D.R.rS) ⊆
      O ∪ {Z | gramR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J Z = T}ᶜ := by
    intro Z hZ
    by_cases hg : gramR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J Z = T
    · exact Or.inl (hOrb v hv hG Z hZ hg)
    · exact Or.inr hg
  have hEq : ω O = ω (PrimT v (abelian₂ X) (D.R.rS + 1 + D.R.rS)) := by
    apply le_antisymm (measure_mono hsub)
    calc ω (PrimT v (abelian₂ X) (D.R.rS + 1 + D.R.rS))
        ≤ ω (O ∪ {Z | gramR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J Z = T}ᶜ) := measure_mono hsup
      _ ≤ ω O + ω {Z | gramR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J Z = T}ᶜ := measure_union_le _ _
      _ = ω O := by rw [omAt_compl_zero X.B.I.cm.sig X.B.I.J ψ v T, add_zero]
  show ω O = _
  rw [hEq, hω, hFib v hG hWe hHe (hUq v hS').1 ϖ hϖ, hCnt v hv hG hWe ϖ hϖ, hW v hS' hLat hSD hUn hWe,
    hH v hS' hUn hHe ϖ hϖ]
  have hq := qv_pos v
  have hd := absV_dV_pos v
  rw [← ENNReal.ofReal_mul' (Real.rpow_nonneg hd.le _), ← ENNReal.ofReal_div_of_pos (by positivity)]
  congr 1
  have e : absV v (dV v) ^ ((X.B.I.n : ℝ) * ((D.R.rS + 1 + D.R.rS : ℕ) : ℝ) -
      ((D.R.rS + 1 + D.R.rS : ℕ) : ℝ) ^ 2 / 2) =
      absV v (dV v) ^ ((X.B.I.n : ℝ) * ((D.R.rS + 1 + D.R.rS : ℕ) : ℝ)) /
        absV v (dV v) ^ (((D.R.rS + 1 + D.R.rS : ℕ) : ℝ) ^ 2 / 2) := Real.rpow_sub hd _ _
  rw [e]
  unfold prodEtaB
  have : (0 : ℝ) < qv v ^ (-(((D.R.rS + 1 + D.R.rS : ℕ) : ℤ) ^ 2)) := zpow_pos hq _
  have : (0 : ℝ) < absV v (dV v) ^ (((D.R.rS + 1 + D.R.rS : ℕ) : ℝ) ^ 2 / 2) := Real.rpow_pos_of_pos hd _
  field_simp

end Loc

end PI.OmVd
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVLatHolds
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmW

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  MeasureTheory NumberField IsDedekindDomain

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem isCMExt_sig : IsCMExt X.B.I.F X.B.I.E X.B.I.cm.sig :=
  ⟨X.B.I.cm.totReal, X.B.I.cm.cmUnram.1, X.B.I.cm.deg2, fun τ x => X.B.I.cm.cmUnram.2.1 τ x⟩

theorem isHermND_J : IsHermND X.B.I.cm.sig X.B.I.J := by
  refine ⟨fun i j => ?_, X.B.I.J_det⟩
  have h := congrFun (congrFun X.B.I.J_herm i) j
  exact h

theorem omVStd_holds : OmVStd X ψ := fun h1 h2 => ⟨isCMExt_sig X, isHermND_J X, h1, h2⟩

theorem omVLat_holds : OmVLat X := ⟨X.B.I.L, ⟨X.B.I.L_fg, X.B.I.L_span⟩, rfl⟩

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVUnramHolds
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmW

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain

variable {D : D7} (X : HidaSetting D)

theorem finrank_OE : Module.finrank (𝓞 X.B.I.F) (𝓞 X.B.I.E) = 2 := by
  rw [← IsFractionRing.finrank_eq (𝓞 X.B.I.F) X.B.I.F (𝓞 X.B.I.E) X.B.I.E]
  exact X.B.I.cm.deg2

def tau : 𝓞 X.B.I.E →+* 𝓞 X.B.I.E := RingOfIntegers.mapRingHom (starRingEnd X.B.I.E)

theorem tau_coe (x : 𝓞 X.B.I.E) :
    algebraMap (𝓞 X.B.I.E) X.B.I.E (tau X x) = star (algebraMap (𝓞 X.B.I.E) X.B.I.E x) := rfl

theorem tau_alg (a : 𝓞 X.B.I.F) :
    tau X (algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E) a) = algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E) a := by
  apply RingOfIntegers.coe_injective
  rw [tau_coe, ← IsScalarTower.algebraMap_apply (𝓞 X.B.I.F) (𝓞 X.B.I.E) X.B.I.E,
    IsScalarTower.algebraMap_apply (𝓞 X.B.I.F) X.B.I.F X.B.I.E]
  exact (X.B.I.cm.fixed _).2 ⟨_, rfl⟩

theorem approx (v : HeightOneSpectrum (𝓞 X.B.I.F)) (P : Ideal (𝓞 X.B.I.E)) [P.IsMaximal]
    [P.LiesOver v.asIdeal] (hf : P.inertiaDeg (𝓞 X.B.I.F) = 1)
    (x : 𝓞 X.B.I.E) : ∃ a : 𝓞 X.B.I.F, x - algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E) a ∈ P := by
  have := v.isMaximal
  rw [Ideal.inertiaDeg_eq_of_isMaximal v.asIdeal P] at hf
  let : Field (𝓞 X.B.I.F ⧸ v.asIdeal) := Ideal.Quotient.field _
  let : Field (𝓞 X.B.I.E ⧸ P) := Ideal.Quotient.field _
  have htop : (⊥ : Subalgebra (𝓞 X.B.I.F ⧸ v.asIdeal) (𝓞 X.B.I.E ⧸ P)) = ⊤ :=
    Subalgebra.bot_eq_top_iff_finrank_eq_one.mpr hf
  have hx : Ideal.Quotient.mk P x ∈ (⊥ : Subalgebra (𝓞 X.B.I.F ⧸ v.asIdeal) (𝓞 X.B.I.E ⧸ P)) :=
    htop ▸ Algebra.mem_top
  obtain ⟨y, hy⟩ := Algebra.mem_bot.mp hx
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨a, ?_⟩
  rw [← Ideal.Quotient.eq, ← hy]
  rfl

theorem omVUnram_holds : OmVUnram X := by
  intro v P hP hPb hPv
  have : P.IsMaximal := hP.isMaximal hPb
  have := v.isPrime
  have : P.LiesOver v.asIdeal := ⟨hPv.symm⟩
  have : Fintype (v.asIdeal.primesOver (𝓞 X.B.I.E)) := Fintype.ofFinite _
  have hsum := Ideal.sum_ramification_inertia_eq_finrank v.asIdeal (𝓞 X.B.I.E)
  rw [finrank_OE X] at hsum
  have he := Ideal.ramificationIdx_pos P (𝓞 X.B.I.F)
  have hf := Ideal.inertiaDeg_pos P (𝓞 X.B.I.F)
  have hmem : P ∈ v.asIdeal.primesOver (𝓞 X.B.I.E) := ⟨hP, inferInstance⟩
  have hle := Finset.single_le_sum
    (f := fun q : v.asIdeal.primesOver (𝓞 X.B.I.E) => q.1.ramificationIdx (𝓞 X.B.I.F) * q.1.inertiaDeg (𝓞 X.B.I.F))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ ⟨P, hmem⟩)
  simp only at hle
  by_contra hne
  have h2 : 2 * P.inertiaDeg (𝓞 X.B.I.F) ≤ P.ramificationIdx (𝓞 X.B.I.F) * P.inertiaDeg (𝓞 X.B.I.F) :=
    Nat.mul_le_mul_right _ (by omega)
  have hf1 : P.inertiaDeg (𝓞 X.B.I.F) = 1 := by
    generalize P.ramificationIdx (𝓞 X.B.I.F) * P.inertiaDeg (𝓞 X.B.I.F) = m at *
    omega

  have hττ : ∀ x, tau X (tau X x) = x := fun x => by
    apply RingOfIntegers.coe_injective; rw [tau_coe, tau_coe, star_star]
  have hQ : (P.comap (tau X)).IsPrime := Ideal.comap_isPrime (tau X) P
  have hQv : (P.comap (tau X)).comap (algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E)) = v.asIdeal := by
    ext a
    simp only [Ideal.mem_comap, tau_alg]
    rw [← Ideal.mem_comap, hPv]
  have : (P.comap (tau X)).LiesOver v.asIdeal := ⟨hQv.symm⟩
  have hQP : P.comap (tau X) = P := by
    by_contra hQP
    have hQmem : P.comap (tau X) ∈ v.asIdeal.primesOver (𝓞 X.B.I.E) := ⟨hQ, inferInstance⟩
    have hneq : (⟨P, hmem⟩ : v.asIdeal.primesOver (𝓞 X.B.I.E)) ≠ ⟨P.comap (tau X), hQmem⟩ :=
      fun h => hQP (congrArg Subtype.val h).symm
    have h3 := Finset.sum_le_sum_of_subset
      (f := fun q : v.asIdeal.primesOver (𝓞 X.B.I.E) => q.1.ramificationIdx (𝓞 X.B.I.F) * q.1.inertiaDeg (𝓞 X.B.I.F))
      (Finset.subset_univ {⟨P, hmem⟩, ⟨P.comap (tau X), hQmem⟩})
    rw [Finset.sum_pair hneq] at h3
    have heQ := Ideal.ramificationIdx_pos (P.comap (tau X)) (𝓞 X.B.I.F)
    have hfQ := Ideal.inertiaDeg_pos (P.comap (tau X)) (𝓞 X.B.I.F)
    simp only at h3
    have h4 : 1 ≤ (P.comap (tau X)).ramificationIdx (𝓞 X.B.I.F) * (P.comap (tau X)).inertiaDeg (𝓞 X.B.I.F) :=
      Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    have h5 : 2 ≤ P.ramificationIdx (𝓞 X.B.I.F) * P.inertiaDeg (𝓞 X.B.I.F) := by omega
    omega

  obtain ⟨θ, t, htθ, hnot⟩ := X.B.I.cm.cmUnram.2.2 P inferInstance
  obtain ⟨a, ha⟩ := approx X v P hf1 θ
  have hτθ : tau X θ = t := by
    apply RingOfIntegers.coe_injective; rw [tau_coe]; exact htθ.symm
  have hb : tau X (θ - algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E) a) ∈ P := by
    have : θ - algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E) a ∈ P.comap (tau X) := by rw [hQP]; exact ha
    exact this
  rw [map_sub, hτθ, tau_alg] at hb
  apply hnot
  have h6 : θ - t = (θ - algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E) a) - (t - algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E) a) := by ring
  rw [h6]
  exact sub_mem ha hb

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.ValNonneg
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmW

open Formalism.L2.SG.Pf.NcVal.OmVSt

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  MeasureTheory NumberField IsDedekindDomain

variable {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem n_sub_a : X.B.I.n - (D.R.rS + 1 + D.R.rS) = D.R.k := by
  have h1 := X.n_eq
  have h2 := D.R.rS_two
  unfold Ranks.r at h1
  omega

theorem a_le_n : D.R.rS + 1 + D.R.rS ≤ X.B.I.n := by
  have h1 := X.n_eq
  have h2 := D.R.rS_two
  unfold Ranks.r at h1
  omega

theorem fac_nonneg (v : PlX X) (j : ℕ) :
    0 ≤ 1 - (etaV (E := X.B.I.E) v : ℝ) ^ j * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ)) := by
  have hq : (1 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
    have : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  have h1 : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ)) ≤ 1 := zpow_le_one_of_nonpos₀ hq (by omega)
  have h0 : 0 ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ)) := by positivity
  have he : (etaV (E := X.B.I.E) v : ℝ) ^ j = 1 ∨ (etaV (E := X.B.I.E) v : ℝ) ^ j = -1 := by
    unfold etaV
    split_ifs
    · left; simp
    · push_cast; exact neg_one_pow_eq_or ℝ j
  rcases he with h | h <;> rw [h] <;> linarith

theorem val_nonneg (v : PlX X) (x : ℝ) (s : Finset ℕ) :
    0 ≤ absV v (dV v) ^ x * ∏ j ∈ s,
      (1 - (etaV (E := X.B.I.E) v : ℝ) ^ j * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ))) := by
  refine mul_nonneg (Real.rpow_nonneg ?_ _) (Finset.prod_nonneg fun j _ => fac_nonneg X v j)
  unfold absV
  split_ifs <;> positivity

theorem prod_eq (v : PlX X) (s : Finset ℕ) :
    ∏ j ∈ s, (1 - (etaV (E := X.B.I.E) v : ℝ) ^ j * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ))) =
      ∏ i ∈ s, (1 - ((etaV (E := X.B.I.E) v : ℤ) : ℝ) ^ i / ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ i) := by
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [zpow_neg, zpow_natCast, div_eq_mul_inv]

theorem exp_eq :
    (X.B.I.n : ℝ) * ((D.R.rS + 1 + D.R.rS : ℕ) : ℝ) - ((D.R.rS + 1 + D.R.rS : ℕ) : ℝ) ^ 2 / 2 =
      (X.B.I.n : ℝ) * (2 * D.R.rS + 1) - ((2 * (D.R.rS : ℝ) + 1) ^ 2) / 2 := by
  push_cast; ring

theorem omV_of' (hStd : OmVStd X ψ) (hLat : OmVLat X) (hSD : OmVSD X) (hUn : OmVUnram X) (hPrim : OmVPrim X u')
    (hGram : OmVGram X u') (hDet : OmVDet X u') (hScale : OmVScale X u' ψ) (hBad : OmVBadT X u' ψ)
    (hLocU : OmVLocU X ψ) : Formalism.L2.SG.Pf.NcVal.OmV X u' ψ := by
  intro hψ hψ' v
  show (omAt X.B.I.cm.sig X.B.I.J ψ v (localGramMatrixFrame X u' v)
      {Y | ∃ k ∈ Kv X.B.I.cm.sig X.B.I.J (abelian₂ X) v, Y = k • ratTup (Fv X.B.I.F v) (tupH (frameOf X u'))}).toReal = _
  rw [hScale hψ hψ' v]
  by_cases hT : ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal
  · rw [hBad hψ hψ' v hT (hSD v) (hUn v) (hPrim v), ENNReal.toReal_ofReal (val_nonneg X v _ _), exp_eq X, prod_eq X v]
    unfold aP
    rw [if_pos hT, n_sub_a X]
  · have h := hLocU v _ (yTup X u' v) (hStd hψ hψ') hLat (hSD v) (hUn v) (a_le_n X) (hPrim v)
      (by rw [hGram v]; exact hDet v hT)
    rw [hGram v] at h
    rw [h, ENNReal.toReal_ofReal (val_nonneg X v _ _), exp_eq X, prod_eq X v]
    unfold aP
    rw [if_neg hT, n_sub_a X]

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmW
end
end

