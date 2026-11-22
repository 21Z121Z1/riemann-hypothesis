import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0298
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Choice
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0010
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0289
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0273
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SqIntIrrPerm
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0168
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0195
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0287
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0288
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselModelLinearMapMatrixExists
section
noncomputable section
open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf

namespace GlobalTheory.TypeAsm.GramPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D}

theorem crd_map_mulVec (m : (VS D).V →ₗ[D.host.E] (VS D).V) (y : (VS D).V) :
    X.crd (m y) = (Matrix.of fun i j => X.crd (m (Formalism.L2.SG.Pf.toV X (Pi.single j 1))) i) *ᵥ X.crd y := by
  unfold Formalism.L2.SG.Pf.toV HidaSetting.crd crdOf
  have hb : ∀ j : Fin X.B.I.n, (∑ i, X.ιE ((Pi.single j (1 : X.B.I.E) : Fin X.B.I.n → X.B.I.E) i) • X.bas i) = X.bas j := by
    intro j
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hbj
      simp [Pi.single_apply, hbj]
    · intro h
      exact absurd (Finset.mem_univ j) h
  simp only [hb]
  funext i
  conv_lhs => rw [← X.bas.sum_repr y]
  simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul,
    Matrix.mulVec, dotProduct, Matrix.of_apply, map_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem phiV_linMat (C : Choice X 1) (τ : D.what₂.Tau) (m : (VS D).V →ₗ[D.host.E] (VS D).V) :
    ∃ n : MatKR D.R.k D.R.rS, ∀ y, n *ᵥ GlobalTheory.TypeAsm.phiV C τ y = GlobalTheory.TypeAsm.phiV C τ (m y) := by
  obtain ⟨-, hQ, -⟩ := C.isT τ
  refine ⟨C.Qi τ * (X.B.I.P (vOf X τ))⁻¹ *
      (Matrix.of fun i j => X.crd (m (Formalism.L2.SG.Pf.toV X (Pi.single j 1))) i).map (X.B.I.φ (vOf X τ)) *
      X.B.I.P (vOf X τ) * C.Q τ, fun y => ?_⟩
  have hP : (X.B.I.P (vOf X τ))⁻¹ * ((Matrix.of fun i j => X.crd (m (Formalism.L2.SG.Pf.toV X (Pi.single j 1))) i).map
      (X.B.I.φ (vOf X τ)) * (X.B.I.P (vOf X τ) * (X.B.I.P (vOf X τ))⁻¹)) =
      (X.B.I.P (vOf X τ))⁻¹ * (Matrix.of fun i j => X.crd (m (Formalism.L2.SG.Pf.toV X (Pi.single j 1))) i).map
      (X.B.I.φ (vOf X τ)) := by
    by_cases h : IsUnit (X.B.I.P (vOf X τ)).det
    · rw [Matrix.mul_nonsing_inv _ h, Matrix.mul_one]
    · rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.zero_mul, Matrix.zero_mul]
  have hw : (fun i => X.B.I.φ (vOf X τ) (X.crd (m y) i)) =
      (Matrix.of fun i j => X.crd (m (Formalism.L2.SG.Pf.toV X (Pi.single j 1))) i).map (X.B.I.φ (vOf X τ)) *ᵥ
        (fun i => X.B.I.φ (vOf X τ) (X.crd y i)) := by
    rw [crd_map_mulVec m y]
    funext i
    exact RingHom.map_mulVec _ _ _ i
  have e1 : ∀ z, GlobalTheory.TypeAsm.phiV C τ z =
      (C.Qi τ * (X.B.I.P (vOf X τ))⁻¹) *ᵥ (fun i => X.B.I.φ (vOf X τ) (X.crd z i)) := by
    intro z
    unfold GlobalTheory.TypeAsm.phiV Formalism.L2.SG.HidaSetting.rv
    rw [Matrix.mulVec_mulVec]
  rw [e1, e1, hw, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  congr 1
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (C.Q τ) (C.Qi τ), hQ, Matrix.one_mul, hP]

end GlobalTheory.TypeAsm.GramPf

namespace GlobalTheory.TypeAsm

theorem phiV_linMat_all : ∀ (D : D7) (X : HidaSetting D) (C : Choice X 1) (τ : D.what₂.Tau)
    (m : (VS D).V →ₗ[D.host.E] (VS D).V),
    ∃ n : MatKR D.R.k D.R.rS, ∀ y, n *ᵥ GlobalTheory.TypeAsm.phiV C τ y = GlobalTheory.TypeAsm.phiV C τ (m y) := by
  intro D X C τ m
  exact GramPf.phiV_linMat C τ m

end GlobalTheory.TypeAsm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClassificationUnitaryOfFull
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace

namespace GlobalTheory.DSSU

theorem classU_of_classF : ∀ n : ℕ, (∀ ε : Fin n → Bool, ClassF ε) → ClassU n := by
  intro n hF
  unfold ClassF at hF
  choose F hP hC hE using hF
  obtain ⟨std, t, ht, hst, hren⟩ := GlobalTheory.SignRenumber.block_renumbering n
  have e1a : ∀ (ε : Fin n → Bool) (x : Fin n), std ε (t ε x) = ε x := fun ε x => congrFun (ht ε).1 x
  have hmono : ∀ (ε : Fin n → Bool) (a b : Fin n), a < b → std ε (t ε a) = std ε (t ε b) → t ε a < t ε b := by
    intro ε a b hab h
    rw [e1a, e1a] at h
    exact (ht ε).2 a b hab h
  refine ⟨fun ε lam => (F (std ε)).H (lam ∘ (t ε).symm), fun ε lam => inferInstance, fun ε lam => inferInstance,
    fun ε lam g => (F (std ε)).π (lam ∘ (t ε).symm) (g.submatrix (t ε).symm (t ε).symm), ?_, ?_⟩
  · intro ε lam hlam
    have hpar : IsParU (lam ∘ (t ε).symm) :=
      ⟨hlam.1.injective.comp (t ε).symm.injective, fun a => hlam.2 _⟩
    have e2 : (lam ∘ (t ε).symm) ∘ (t ε) = lam := by funext a; simp
    have h1 := GlobalTheory.T.harish_chandra_permute n (std ε) _ ((F (std ε)).π (lam ∘ (t ε).symm)) (lam ∘ (t ε).symm) (t ε)
      (hmono ε) (by rw [e2]; exact hlam.1) (hP _ _ hpar)
    rw [(ht ε).1, e2] at h1
    exact h1
  · intro ε H' _ _ σ' hσ
    let σ₀ : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H') := fun g => σ' (g.submatrix (t ε) (t ε))
    have hσ₀ : IsSqIntIrr (std ε) σ₀ := by
      rw [(GlobalTheory.DSId.PermK.permKType n (std ε) (t ε) H' σ₀ (hmono ε)).2.2.2.1]
      have e3 : (fun g : Matrix (Fin n) (Fin n) ℂ => σ₀ (g.submatrix (t ε).symm (t ε).symm)) = σ' := by
        funext g
        simp only [σ₀, Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id]
      rw [(ht ε).1, e3]
      exact hσ
    obtain ⟨lam₀, hpar₀, T, hT⟩ := hE (std ε) H' σ₀ hσ₀
    obtain ⟨w, s, hw, hanti, hs⟩ := hren ε (lam₀ ∘ t ε) (hpar₀.1.comp (t ε).injective)
    refine ⟨s, ((lam₀ ∘ t ε) ∘ w) ∘ s, ⟨hanti, fun a => hpar₀.2 _⟩, hs, ?_⟩
    have hstd : std (ε ∘ s) = std ε := (hst ε s).1
    have htt : t (ε ∘ s) = s.trans (t ε) := Equiv.ext ((hst ε s).2 hs)
    show UEquiv (ε ∘ s) (fun g => σ' (g.submatrix s.symm s.symm))
      (fun g => (F (std (ε ∘ s))).π ((((lam₀ ∘ t ε) ∘ w) ∘ s) ∘ (t (ε ∘ s)).symm)
        (g.submatrix (t (ε ∘ s)).symm (t (ε ∘ s)).symm))
    rw [htt, hstd]
    have hconj : ConjK (std ε) lam₀ ((((lam₀ ∘ t ε) ∘ w) ∘ s) ∘ (s.trans (t ε)).symm) := by
      refine ⟨(t ε).symm.trans (w.trans (t ε)), ?_, ?_⟩
      · intro a
        simp only [Equiv.trans_apply]
        rw [e1a, hw, ← e1a ε ((t ε).symm a), Equiv.apply_symm_apply]
      · funext a
        simp [Equiv.symm_trans_apply]
    obtain ⟨T2, hT2⟩ := hC (std ε) lam₀ _ hpar₀ hconj
    refine ⟨T.trans T2, ?_⟩
    intro g hg v
    have hcomp : std ε ∘ (s.trans (t ε)) = ε ∘ s := by
      funext a; simp [Equiv.trans_apply, e1a]
    have hh : g.submatrix (s.trans (t ε)).symm (s.trans (t ε)).symm ∈ UJset (std ε) :=
      (((GlobalTheory.Dec.PermGroup.permGroup n (std ε) (s.trans (t ε))).1 g).1).mp (by rw [hcomp]; exact hg)
    have hσh : σ₀ (g.submatrix (s.trans (t ε)).symm (s.trans (t ε)).symm) = σ' (g.submatrix s.symm s.symm) := by
      show σ' ((g.submatrix _ _).submatrix (t ε) (t ε)) = _
      rw [Matrix.submatrix_submatrix]
      congr 2 <;> funext a <;> simp [Equiv.symm_trans_apply]
    simp only [LinearIsometryEquiv.trans_apply]
    rw [← hσh, hT _ hh, hT2 _ hh]

end GlobalTheory.DSSU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColsSharpDictionary
section
noncomputable section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.St

section Abstract

open Formalism.L2.SG.ColsDim

theorem cols_sharp_abstract {Γ Gi Gf : Type} [Group Γ] [Group Gi] [Group Gf] {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (ιi : Γ →* Gi) (ιf : Γ →* Gf)
    (K : Subgroup Gf) (ψ : K →* ℂˣ) (π : Representation ℂ Gi V)
    (hπ : ∀ h : Gi, ∀ v w : V, ⟪π h v, π h w⟫_ℂ = ⟪v, w⟫_ℂ)
    (hψ : ∀ κ : K, ‖((ψ κ : ℂˣ) : ℂ)‖ = 1)
    (sh : (V →ₗ[ℂ] (Gi × Gf → ℂ)) → Gf → V)
    (hsh : ∀ (T : V →ₗ[ℂ] (Gi × Gf → ℂ)) (x : Gf) (ξ : V), ⟪sh T x, ξ⟫_ℂ = T ξ (1, x)) :
    (∀ (T : Cols ℂ ιi ιf K ψ π) (γ : Γ) (x : Gf) (κ : K),
      sh T.1 (ιf γ * x * κ) = (((ψ κ)⁻¹ : ℂˣ) : ℂ) • π (ιi γ) (sh T.1 x)) ∧
    (∀ T : Cols ℂ ιi ιf K ψ π, (∀ x, sh T.1 x = 0) → T = 0) ∧
    ∀ φ : Gf → V, (∀ (γ : Γ) (x : Gf) (κ : K),
      φ (ιf γ * x * κ) = (((ψ κ)⁻¹ : ℂˣ) : ℂ) • π (ιi γ) (φ x)) →
      ∃ T : Cols ℂ ιi ιf K ψ π, ∀ x, sh T.1 x = φ x := by
  obtain ⟨e, he, hsm⟩ := sharp_bijective Γ Gi Gf V ιi ιf K ψ π hπ hψ
  have key : ∀ (T : Cols ℂ ιi ιf K ψ π) (x : Gf), sh T.1 x = (e T).1 x := fun T x =>
    ext_inner_right ℂ fun ξ => by
      rw [hsh]
      exact he T x ξ
  refine ⟨?_, ?_, ?_⟩
  · intro T γ x κ
    rw [key, key]
    exact (e T).2 γ x κ
  · intro T hT
    have h0 : e T = e ((0 : ℂ) • T) := by
      apply Subtype.ext
      rw [hsm]
      funext x
      rw [← key, hT x]
      simp
    have := e.injective h0
    rw [this]
    simp
  · intro φ hφ
    refine ⟨e.symm ⟨φ, hφ⟩, fun x => ?_⟩
    rw [key, Equiv.apply_symm_apply]

end Abstract

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cols_sharp_dictionary :
    ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter), (∀ κ : Ku X u hK, ‖((psiK X u hK κ : ℂˣ) : ℂ)‖ = 1) ∧ (∀ (h : Hinf X u) (v w : X.Vpi u), ⟪piRep X u h v, piRep X u h w⟫_ℂ = ⟪v, w⟫_ℂ) ∧ (∀ (T : Cu X u hK) (γ : Gam X u) (x : Hfin X u) (κ : Ku X u hK), shP X u T.1 (iotaF X u γ * x * κ) = (((psiK X u hK κ)⁻¹ : ℂˣ) : ℂ) • piRep X u (iotaI X u γ) (shP X u T.1 x)) ∧ (∀ T : Cu X u hK, (∀ x, shP X u T.1 x = 0) → T = 0) ∧ ∀ φ : Hfin X u → X.Vpi u, (∀ (γ : Gam X u) (x : Hfin X u) (κ : Ku X u hK), φ (iotaF X u γ * x * κ) = (((psiK X u hK κ)⁻¹ : ℂˣ) : ℂ) • piRep X u (iotaI X u γ) (φ x)) → ∃ T : Cu X u hK, ∀ x, shP X u T.1 x = φ x := by
  intro D X u hK
  have hψ : ∀ κ : Ku X u hK, ‖((psiK X u hK κ : ℂˣ) : ℂ)‖ = 1 := fun κ => hK.2.2.2.2 _ κ.2
  have hπ : ∀ (h : Hinf X u) (v w : X.Vpi u), ⟪piRep X u h v, piRep X u h w⟫_ℂ = ⟪v, w⟫_ℂ :=
    fun h v w => (X.piU_rep u).2.2.1 _ (hinf_le_sinf X u _ h.2) v w
  exact ⟨hψ, hπ, cols_sharp_abstract (iotaI X u) (iotaF X u) (Ku X u hK) (psiK X u hK) (piRep X u) hπ hψ
    (shP X u) (inner_shP X u)⟩

end GlobalTheory.St

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnWittFrameBasisBlockGram
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.St

variable {D : D7}

theorem hspace_gram_det_ne {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) :
    S.gram.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hv
  have : S.frame.equivFun.symm v = 0 := by
    refine S.nondeg.2 _ fun x => ?_
    have hx : ∀ i, S.hT (S.frame i) (S.frame.equivFun.symm v) = 0 := fun i => by
      have := congrFun h0 i
      simpa [Matrix.mulVec, dotProduct, Formalism.BasicNotions.HSpace.gram, mul_comm] using this
    rw [← S.frame.sum_repr x]
    simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, hx, smul_zero,
      Finset.sum_const_zero]
  exact (LinearEquiv.map_eq_zero_iff _).1 this

theorem hform_crd_setting (X : HidaSetting D) (v w : (VS D).V) :
    X.ιE (Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (X.crd v) (X.crd w)) = (VS D).hT v w := by
  conv_rhs => rw [← X.bas.sum_repr v, ← X.bas.sum_repr w]
  simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Formalism.UG.hform, map_mul, HidaSetting.crd, crdOf, starRingEnd_apply, X.ιE_conj, RingEquiv.apply_symm_apply,
    X.J_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [← Formalism.BasicNotions.bridge_star_holds D.R D.host, RingHom.id_apply]
  ring

theorem gram_entry {A : Type} [CommRing A] {n ι : Type} [Fintype n] (σ : A →+* A) (Q : Matrix n ι A)
    (J : Matrix n n A) (k l : ι) :
    ((Q.map σ)ᵀ * J * Q) k l = Formalism.UG.hform σ J (fun i => Q i k) (fun i => Q i l) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Formalism.UG.hform, Finset.sum_mul]
  exact Finset.sum_comm

def famQ (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) :
    Fin (D.R.N 0) ⊕ (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) → (VS D).V :=
  Sum.elim (qFr wt) (Sum.elim X.eX (Sum.elim X.fY fun _ => X.zu u))

end GlobalTheory.St

namespace GlobalTheory.St
variable {D : D7}

theorem hT_symm_zero {x y : (VS D).V} (h : (VS D).hT x y = 0) : (VS D).hT y x = 0 := by
  rw [← (VS D).herm.eq x y, h, map_zero]

theorem hT_wt_symm (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hiso : ∀ x y, (VS D).hT (wt x) (wt y) = (VS D).hT x y)
    (x y : (VS D).V) : (VS D).hT (wt.symm x) y = (VS D).hT x (wt y) := by
  rw [← hiso, LinearEquiv.apply_symm_apply]

theorem hT_qFr_qFr (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hiso : ∀ x y, (VS D).hT (wt x) (wt y) = (VS D).hT x y)
    (a b : Fin (D.R.N 0)) : (VS D).hT (qFr wt a) (qFr wt b) = Formalism.L2.Forms.gramN D 0 (Nat.zero_le _) a b := by
  rw [qFr, hT_wt_symm wt hiso, qFr, LinearEquiv.apply_symm_apply, xFr, xFr,
    D.sp.iXY_isom 0 (by have := D.R.two_le_m; omega)]
  rfl

theorem hT_qFr_rest (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hw : WittX X u wt)
    (a : Fin (D.R.N 0)) (k : Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) :
    (VS D).hT (qFr wt a) (famQ X u wt (Sum.inr k)) = 0 := by
  obtain ⟨hiso, he, hf, hz⟩ := hw
  rw [qFr, hT_wt_symm wt hiso]
  rcases k with b | b | b
  · simp only [famQ, Sum.elim_inr, Sum.elim_inl, he]; exact (D.sp.hyp_orthX b _).1
  · simp only [famQ, Sum.elim_inr, Sum.elim_inl, hf]; exact (D.sp.hyp_orthX b _).2
  · simp only [famQ, Sum.elim_inr, hz, Formalism.BasicNotions.D7.zmOf, LinearMap.map_smul]
    rw [xFr, D.sp.zm_orth, smul_zero]

end GlobalTheory.St

namespace GlobalTheory.St
variable {D : D7}

theorem hT_fe (X : HidaSetting D) (a b : Fin D.R.rS) :
    (VS D).hT (X.fY a) (X.eX b) = if b = a then 1 else 0 := by
  rw [← (VS D).herm.eq (X.eX b) (X.fY a), X.ef]
  split_ifs <;> simp

theorem hT_ze (X : HidaSetting D) (u : D.what₂.Word) (b : Fin D.R.rS) : (VS D).hT (X.zu u) (X.eX b) = 0 :=
  hT_symm_zero (X.zu_orth u b).1

theorem hT_zf (X : HidaSetting D) (u : D.what₂.Word) (b : Fin D.R.rS) : (VS D).hT (X.zu u) (X.fY b) = 0 :=
  hT_symm_zero (X.zu_orth u b).2

theorem hT_zz_ne (X : HidaSetting D) (u : D.what₂.Word) : (VS D).hT (X.zu u) (X.zu u) ≠ 0 := by
  rw [X.zu_norm, neg_ne_zero, Nat.cast_ne_zero]
  exact ((D.mem u).A.T_prime).ne_zero

def gramR (X : HidaSetting D) (u : D.what₂.Word) :
    Matrix (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) X.B.I.E :=
  Matrix.of fun k l => X.ιE.symm ((VS D).hT (Sum.elim X.eX (Sum.elim X.fY fun _ => X.zu u) k)
    (Sum.elim X.eX (Sum.elim X.fY fun _ => X.zu u) l))

def gramRinv (X : HidaSetting D) (u : D.what₂.Word) :
    Matrix (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) X.B.I.E :=
  Matrix.of fun k l => match k, l with
    | Sum.inl a, Sum.inr (Sum.inl b) => if a = b then 1 else 0
    | Sum.inr (Sum.inl a), Sum.inl b => if a = b then 1 else 0
    | Sum.inr (Sum.inr _), Sum.inr (Sum.inr _) => (X.ιE.symm ((VS D).hT (X.zu u) (X.zu u)))⁻¹
    | _, _ => 0

theorem gramR_mul_inv (X : HidaSetting D) (u : D.what₂.Word) : gramR X u * gramRinv X u = 1 := by
  have ht : X.ιE.symm ((VS D).hT (X.zu u) (X.zu u)) ≠ 0 := by
    rw [Ne, RingEquiv.map_eq_zero_iff]; exact hT_zz_ne X u
  ext (a | a | a) (b | b | b) <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, gramR, gramRinv, X.ee, X.ff, X.ef, hT_fe, hT_ze, hT_zf,
      X.zu_orth, Matrix.one_apply, ht, eq_comm]

end GlobalTheory.St

namespace GlobalTheory.St
variable {D : D7}

theorem qFrame_basis_gram : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V), WittX X u wt → ∃ (Q : Matrix (Fin X.B.I.n) (Fin (D.R.N 0) ⊕ (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit)) X.B.I.E) (Qi : Matrix (Fin (D.R.N 0) ⊕ (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit)) (Fin X.B.I.n) X.B.I.E) (G' : Matrix (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) X.B.I.E), Q * Qi = 1 ∧ Qi * Q = 1 ∧ (∀ j i, Q i (Sum.inl j) = X.crd (qFr wt j) i) ∧ (∀ a i, Q i (Sum.inr (Sum.inl a)) = X.eR a i) ∧ (∀ a i, Q i (Sum.inr (Sum.inr (Sum.inl a))) = X.fR a i) ∧ (∀ i, Q i (Sum.inr (Sum.inr (Sum.inr ()))) = X.zR u i) ∧ IsUnit G'.det ∧ (Q.map (starRingEnd X.B.I.E))ᵀ * X.B.I.J * Q = Matrix.fromBlocks ((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm) 0 0 G' := by
  intro D X u wt hw
  classical
  let Q : Matrix (Fin X.B.I.n) (Fin (D.R.N 0) ⊕ (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit)) X.B.I.E :=
    Matrix.of fun i k => X.crd (famQ X u wt k) i
  have hiso := hw.1

  have hM : (Q.map (starRingEnd X.B.I.E))ᵀ * X.B.I.J * Q =
      Matrix.fromBlocks ((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm) 0 0 (gramR X u) := by
    ext k l
    rw [gram_entry]
    apply X.ιE.injective
    rw [show (fun i => Q i k) = X.crd (famQ X u wt k) from rfl, show (fun i => Q i l) = X.crd (famQ X u wt l) from rfl,
      hform_crd_setting]
    rcases k with a | k <;> rcases l with b | l
    · simp only [Matrix.fromBlocks_apply₁₁, Matrix.map_apply, RingEquiv.apply_symm_apply]
      exact hT_qFr_qFr wt hiso a b
    · simp only [Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, map_zero]
      exact hT_qFr_rest X u wt hw a l
    · simp only [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, map_zero]
      exact hT_symm_zero (hT_qFr_rest X u wt hw b k)
    · simp only [Matrix.fromBlocks_apply₂₂, gramR, Matrix.of_apply, RingEquiv.apply_symm_apply]
      rfl

  have hA : ((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm).det ≠ 0 := by
    have h1 : ((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm).det =
        X.ιE.symm.toRingHom (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).det := by
      rw [RingHom.map_det]; rfl
    rw [h1]
    refine (map_ne_zero _).2 ?_
    unfold Formalism.L2.Forms.gramN
    rw [Matrix.det_reindex_self]
    exact hspace_gram_det_ne _
  have hG : IsUnit (gramR X u).det := Matrix.isUnit_det_of_right_inverse (gramR_mul_inv X u)
  have hMu : IsUnit ((Q.map (starRingEnd X.B.I.E))ᵀ * X.B.I.J * Q).det := by
    rw [hM, Matrix.det_fromBlocks_zero₂₁]
    exact (isUnit_iff_ne_zero.2 hA).mul hG

  have hcard : Fintype.card (Fin (D.R.N 0) ⊕ (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit)) = X.B.I.n := by
    rw [X.n_eq, ← dimS_eq, Formalism.BasicNotions.Ranks.N_zero]
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
    omega
  let σ := Fintype.equivFinOfCardEq hcard
  let P := Q.submatrix σ id
  have hQ : Q = P.submatrix σ.symm id := by
    ext i k; simp [P]
  have hconj : (Q.map (starRingEnd X.B.I.E))ᵀ = Qᴴ := by
    ext i k
    simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.map_apply]
    exact starRingEnd_apply _
  have hPJ : (Q.map (starRingEnd X.B.I.E))ᵀ * X.B.I.J * Q = Pᴴ * X.B.I.J.submatrix σ σ * P := by
    have hJ : X.B.I.J = (X.B.I.J.submatrix σ σ).submatrix σ.symm σ.symm := by
      simp [Matrix.submatrix_submatrix]
    rw [hconj, hQ, Matrix.conjTranspose_submatrix]
    conv_lhs => rw [hJ]
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
  have hP : IsUnit P.det := by
    rw [hPJ, Matrix.det_mul, Matrix.det_mul] at hMu
    exact isUnit_of_mul_isUnit_right hMu
  refine ⟨Q, (P⁻¹).submatrix id σ.symm, gramR X u, ?_, ?_, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun _ => rfl, hG, hM⟩
  · rw [hQ, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.mul_nonsing_inv _ hP,
      Matrix.submatrix_one_equiv]
  · rw [hQ, Matrix.submatrix_mul_equiv, Matrix.nonsing_inv_mul _ hP, Matrix.submatrix_id_id]

end GlobalTheory.St
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousHasCompactSupportInfFinProductTestFunc
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct ENNReal

namespace GlobalTheory.ProdCont

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {d : ℕ} (b : Module.Basis (Fin d) F E) {M n : ℕ}

noncomputable def glueTup (Y : (Fin n → Fin M → Ainf F ⊗[F] E) × (Fin n → Fin M → Af F ⊗[F] E)) :
    Fin n → Fin M → AF F ⊗[F] E :=
  fun a i => (Algebra.TensorProduct.basis (AF F) b).equivFun.symm fun k =>
    pairA F ((Algebra.TensorProduct.basis (Ainf F) b).repr (Y.1 a i) k)
      ((Algebra.TensorProduct.basis (Af F) b).repr (Y.2 a i) k)

theorem continuous_glueTup : Continuous (glueTup (F := F) (E := E) b (M := M) (n := n)) := by
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  haveI : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) _
  haveI : ContinuousSMul (AF F) (AF F ⊗[F] E) := IsModuleTopology.toContinuousSMul (AF F) _
  have hs : Continuous (Algebra.TensorProduct.basis (AF F) b).equivFun.symm :=
    IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.basis (AF F) b).equivFun.symm.toLinearMap
  have hi : Continuous (Algebra.TensorProduct.basis (Ainf F) b).equivFun :=
    IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.basis (Ainf F) b).equivFun.toLinearMap
  have hf : Continuous (Algebra.TensorProduct.basis (Af F) b).equivFun :=
    IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.basis (Af F) b).equivFun.toLinearMap
  refine continuous_pi fun a => continuous_pi fun i => hs.comp (continuous_pi fun k => ?_)
  have h1 : Continuous fun Y : (Fin n → Fin M → Ainf F ⊗[F] E) × (Fin n → Fin M → Af F ⊗[F] E) =>
      (Algebra.TensorProduct.basis (Ainf F) b).equivFun (Y.1 a i) k :=
    (continuous_apply k).comp (hi.comp ((continuous_apply i).comp ((continuous_apply a).comp continuous_fst)))
  have h2 : Continuous fun Y : (Fin n → Fin M → Ainf F ⊗[F] E) × (Fin n → Fin M → Af F ⊗[F] E) =>
      (Algebra.TensorProduct.basis (Af F) b).equivFun (Y.2 a i) k :=
    (continuous_apply k).comp (hf.comp ((continuous_apply i).comp ((continuous_apply a).comp continuous_snd)))
  exact (h1.prodMk h2 :)

theorem glueTup_proj (X : Fin n → Fin M → AF F ⊗[F] E) :
    glueTup b (projInf X, projFin X) = X := by
  funext a i
  refine GlobalTheory.GaugeGlue.tens_ext b fun k => ?_
  simp only [glueTup]
  rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  simp only [projInf, projFin, Module.Basis.equivFun_apply, GlobalTheory.GaugeGlue.repr_map]
  rfl

end GlobalTheory.ProdCont

open GlobalTheory.ProdCont in

theorem GlobalTheory.prod_continuous_hasCompactSupport : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (M n : ℕ) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (Φi : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (Φf : (Fin n → Fin M → Af F ⊗[F] E) → ℂ), Continuous Φi → HasCompactSupport Φi → Continuous Φf → HasCompactSupport Φf → IsProdInfFin Φ Φi Φf → Continuous Φ ∧ HasCompactSupport Φ := by
  intro F E _ _ _ _ _ M n Φ Φi Φf hci hki hcf hkf hΦ
  haveI : FiniteDimensional F E := inferInstance
  let b := Module.finBasis F E
  have hpf : Continuous (projFin (F := F) (E := E) (M := M) (n := n)) :=
    continuous_pi fun a => continuous_pi fun i =>
      (GlobalTheory.GaugeGlue.continuous_map b (sndA F) GlobalTheory.GaugeGlue.continuous_sndA).comp
        ((continuous_apply i).comp (continuous_apply a))
  have hpi := GlobalTheory.GaugeGlue.continuous_projInf (F := F) (E := E) (M := M) (n := n) b
  have hEq : Φ = fun X => Φi (projInf X) * Φf (projFin X) := funext hΦ
  refine ⟨hEq ▸ (hci.comp hpi).mul (hcf.comp hpf), ?_⟩
  have hg : Continuous fun X : Fin n → Fin M → AF F ⊗[F] E => (projInf X, projFin X) :=
    hpi.prodMk hpf
  have hK : IsCompact (tsupport Φi ×ˢ tsupport Φf) := hki.isCompact.prod hkf.isCompact
  have hsub : tsupport Φ ⊆ (fun X => (projInf X, projFin X)) ⁻¹' (tsupport Φi ×ˢ tsupport Φf) := by
    refine closure_minimal (fun X hX => ?_)
      ((isClosed_tsupport Φi).prod (isClosed_tsupport Φf) |>.preimage hg)
    have h0 : Φi (projInf X) * Φf (projFin X) ≠ 0 := by rw [← hΦ]; exact hX
    exact ⟨subset_tsupport _ (left_ne_zero_of_mul h0), subset_tsupport _ (right_ne_zero_of_mul h0)⟩
  have hsub2 : tsupport Φ ⊆ glueTup b '' (tsupport Φi ×ˢ tsupport Φf) := fun X hX =>
    ⟨_, hsub hX, glueTup_proj b X⟩
  exact (hK.image (continuous_glueTup b)).of_isClosed_subset (isClosed_tsupport Φ) hsub2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CutOutSubgroupTangentSecondOrderHilbertSchmidtStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cutOut_subgroup_tangent_second_order_hilbertSchmidt : ∀ (n : ℕ) (ε : Fin n → Bool) (S : Set (Formalism.REAL.UJ ε)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), IsCut ε S E → ∀ g ∈ S, nrm (uMat g - 1 - cmb E (crd E (uMat g - 1))) ≤ nrm (uMat g - 1) ^ 2 := by
  first | exact @GlobalTheory.IwConstApprox.nrm_sub_proj_le_sq | exact GlobalTheory.IwConstApprox.nrm_sub_proj_le_sq | (intros; apply GlobalTheory.IwConstApprox.nrm_sub_proj_le_sq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DerivativesCoefficientsConvolutionFixedVectorStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivatives_coefficients_convolutionFixed_vector : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (α : Matrix (Fin n) (Fin n) ℂ → ℂ) (s : H), IsURepOn (UJset ε) σ → SmoothOnG ε α → HasCompactSupport (fun g : UJ ε => α (umat g)) → (∀ u : H, ∫ g : UJ ε, α (umat g) * ⟪u, σ (umat g) s⟫_ℂ ∂(muG ε) = ⟪u, s⟫_ℂ) → (∀ u, SmoothOnG ε (fun g => ⟪u, σ g s⟫_ℂ)) ∧ ∀ w : List (Fin n × Fin n), ∃ s' : H, ∀ u, ∀ g ∈ UJset ε, Eword ε w (fun x => ⟪u, σ x s⟫_ℂ) g = ⟪u, σ g s'⟫_ℂ := by
  first | exact @GlobalTheory.DerivConv.derivConv | exact GlobalTheory.DerivConv.derivConv | (intros; apply GlobalTheory.DerivConv.derivConv <;> assumption)
end

