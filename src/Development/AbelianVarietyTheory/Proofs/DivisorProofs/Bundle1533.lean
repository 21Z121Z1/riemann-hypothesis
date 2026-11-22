import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1514
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1174
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0934
import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IoOverLeftUnique
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0081
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1496
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1462
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1455
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1477
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1320
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1481
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1471
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumFixesVacuumNonSplitPlaceUnramified
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1516

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralCongruenceLevelEqCountStatement
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_orbitalIntegral_congruence_level_eq_count : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e → ∀ (k : ℕ) (t : K.O), K.Small t → GlobalTheory.UnitLemma.val K.O (algebraMap K.O K.E t) = k → ∀ (n : ℕ) (Q : (w.adicCompletion E)[X]) (B : GlobalTheory.UnitLemma.InvAlg K) (u x : B.A), Q.Separable → Fits w e B Q u → u = 1 + algebraMap K.O B.A t * B.g → ∀ (γ : GLw n w) (hγ : γ ∈ UL n w), IsModel w e B u x γ → twOrb (MonoidHom.id (UL n w)) (KL n w) ⟨γ, hγ⟩ (({g : UL n w | g.1 ∈ congSet w n k} : Set (UL n w)).indicator 1) = ((B.N x : ℚ) : ℂ) := by
  first | exact @GlobalTheory.KapOrb.twOrb_congruence_eq_N | exact GlobalTheory.KapOrb.twOrb_congruence_eq_N | (intros; apply GlobalTheory.KapOrb.twOrb_congruence_eq_N <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldingFrameDeltaChange
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace GlobalTheory.OneMapAll

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
  GlobalTheory.FieldBC
open scoped TensorProduct

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isSec_sum_smul_bc {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) {m : ℕ} (a : Fin m → ℂ)
    (P : Fin m → Frame X.Ψ r → ℂ) (hP : ∀ i, X.IsSec la (P i)) :
    X.IsSec la (fun x => ∑ i, a i * P i x) := by
  refine ⟨DifferentiableOn.fun_sum fun i _ => (hP i).1.const_mul _, fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [(hP i).2.1 x hx b hb]; ring
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [(hP i).2.2 γ hγ x hx]; ring

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c c' : Coeff l} {r n : ℕ}

open Classical in
theorem rdU_unfExt_of_isBC (hle : c.F ≤ c'.F) {σ : c.F →+* ℂ} (σ' : c'.F →+* ℂ)
    (hσ : ∀ a, σ' (incF c c' hle a) = σ a) (U : Unf Xo c σ r) {m : ℕ} {f' : Rul Xo c'}
    {as : Fin m → c'.F} {fs : Fin m → Rul Xo c} (hBC : IsBC hle f' as fs) (k : U.Comp) (x : Frame (U.X k).Ψ r) :
    rdU (unfExt hle σ' hσ U) f' k x = ∑ i, σ' (as i) * rdU U (fs i) k x := by
  show (if h : x ∈ (U.X k).dom then toC (evR Xo c' f' ((unfExt hle σ' hσ U).un k ⟨x, h⟩)) else 0) =
    ∑ i, σ' (as i) * (if h : x ∈ (U.X k).dom then toC (evR Xo c (fs i) (U.un k ⟨x, h⟩)) else 0)
  by_cases hx : x ∈ (U.X k).dom
  · simp only [dif_pos hx]
    exact @hBC (CAt σ') _ σ.toAlgebra σ'.toAlgebra hσ _
  · simp only [dif_neg hx, mul_zero, Finset.sum_const_zero]

theorem isUnf_unfExt (hle : c.F ≤ c'.F) {σ : c.F →+* ℂ} (σ' : c'.F →+* ℂ)
    (hσ : ∀ a, σ' (incF c c' hle a) = σ a) {U : Unf Xo c σ r} (hU : IsUnf U) : IsUnf (unfExt hle σ' hσ U) := by
  obtain rfl : σ = σ'.comp (incF c c' hle) := RingHom.ext fun a => (hσ a).symm
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hU
  letI : Algebra c.F (CAt σ') := (σ'.comp (incF c c' hle)).toAlgebra
  refine ⟨h1, h2, fun y => ?_, h4, fun a n hd f' hf' k => ?_, h6⟩
  · exact h3 (FrPt.res hle (S := CAt σ') hσ y)
  · obtain ⟨m, as, fs, hfs, hBC⟩ := (secBC_and_cuspBC E H Dw l Xo c c' hle).1 a n f' hf'
    have e : rdU (unfExt hle σ' hσ U) f' k = fun x => ∑ i, σ' (as i) * rdU U (fs i) k x :=
      funext fun x => rdU_unfExt_of_isBC hle σ' hσ U hBC k x
    rw [e]
    exact isSec_sum_smul_bc (U.X k) (laU U a n k) _ _ fun i => h5 a n hd _ (hfs i) k

theorem rdU_unfExt_smul_rulBC (hle : c.F ≤ c'.F) {σ : c.F →+* ℂ} (σ' : c'.F →+* ℂ)
    (hσ : ∀ a, σ' (incF c c' hle a) = σ a) (U : Unf Xo c σ r) (u : c'.F) {f : Rul Xo c} (hf : f ∈ sec Xo c 0 0)
    (k : U.Comp) (x : Frame (U.X k).Ψ r) :
    rdU (unfExt hle σ' hσ U) (u • rulBC hle f) k x = σ' u * rdU U f k x := by
  rw [map_smulₛₗ]
  have e := rdU_unfExt_of_isBC hle σ' hσ U (GlobalTheory.FieldBCModel.isBC_rulBC hle hf.1) k x
  simp only [Finset.univ_unique, Finset.sum_singleton, Matrix.cons_val_fin_one, map_one, one_mul] at e
  rw [← e]
  rfl

end Gen

theorem cXiAt_covBC (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (n r : ℕ) (c c' : Coeff l) (hle : c.F ≤ c'.F) (V : HSp D) (hr : V.rank = r) (d : DeltaDat Xo c n) (u : c'.F)
    (U₂ : Unf d.Xo₂ d.c₂ (c.F.val.toRingHom.comp (d.eF.symm : d.c₂.F →+* c.F)) r)
    (dict₂ : GA D V → Σ k, Frame (U₂.X k).Ψ r) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ) (c0 : ℂ)
    (hs : d.cδ ∈ sec d.Xo₂ d.c₂ 0 0) (h : CXiAt V hr c.F.val.toRingHom d U₂ dict₂ io x₀ xi c0) :
    CXiAt V hr c'.F.val.toRingHom (covBC hle d u) (covUnf hle d u U₂) dict₂ io x₀ xi ((u : ℂ) * c0) := by
  obtain ⟨h1, h2, g, e, F, ik, φ, th, h3, h4, h5⟩ := h
  refine ⟨isUnf_unfExt (le_covCoeff hle d) _ (fun _ => rfl) h1, h2, g, e, F, ik, φ, th, h3, h4, fun h γ hm => ?_⟩
  have e1 := rdU_unfExt_smul_rulBC (le_covCoeff hle d)
    (c'.F.val.toRingHom.comp ((covBC hle d u).eF.symm : (covBC hle d u).c₂.F →+* c'.F)) (fun _ => rfl) U₂
    (show (covCoeff hle d).F from u) hs (dict₂ h).1 (dict₂ h).2
  refine e1.trans ?_
  rw [h5 h γ hm, ← mul_assoc]
  rfl

end GlobalTheory.OneMapAll
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
section
noncomputable section

namespace GlobalTheory.ThK.FlagPar

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem mat_mul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g h : UA σ J) : mat (g * h) = mat g * mat h := rfl

theorem mat_one {n : ℕ} {J : Matrix (Fin n) (Fin n) E} : mat (1 : UA σ J) = 1 := rfl

theorem mat_inv_mul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) : mat g⁻¹ * mat g = 1 := by
  rw [← mat_mul, inv_mul_cancel, mat_one]

variable (σ) in

def stabCols {d r m : ℕ} (J : Matrix (Fin d) (Fin d) E) (X : Matrix (Fin d) (Fin r) (AE F E))
    (I : Matrix (Fin d) (Fin m) (AE F E)) : Subgroup (UA σ J) where
  carrier := {u | ∃ (A : GL (Fin r) (AE F E)) (D : GL (Fin m) (AE F E)), mat u * X = X * A.1 ∧
    ∀ z, ∃ a, mat u *ᵥ (I *ᵥ z) = I *ᵥ (D.1 *ᵥ z) + X *ᵥ a}
  one_mem' := ⟨1, 1, by simp [mat_one], fun z => ⟨0, by simp [mat_one]⟩⟩
  mul_mem' := by
    rintro u v ⟨A, D, h1, h2⟩ ⟨A', D', h1', h2'⟩
    refine ⟨A * A', D * D', ?_, fun z => ?_⟩
    · rw [mat_mul, Matrix.mul_assoc, h1', ← Matrix.mul_assoc, h1, Matrix.mul_assoc, Units.val_mul]
    · obtain ⟨a', ha'⟩ := h2' z
      obtain ⟨a, ha⟩ := h2 (D'.1 *ᵥ z)
      refine ⟨a + A.1 *ᵥ a', ?_⟩
      rw [mat_mul, ← Matrix.mulVec_mulVec, ha', Matrix.mulVec_add, ha, Matrix.mulVec_mulVec a' (mat u) X, h1,
        Matrix.mulVec_add, Units.val_mul, ← Matrix.mulVec_mulVec z D.1, ← Matrix.mulVec_mulVec a' X, add_assoc]
  inv_mem' := by
    rintro u ⟨A, D, h1, h2⟩
    have e : mat u⁻¹ * X = X * (A⁻¹).1 := by
      have : X = mat u * (X * (A⁻¹).1) := by
        rw [← Matrix.mul_assoc, h1, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      conv_lhs => rw [this, ← Matrix.mul_assoc, mat_inv_mul, Matrix.one_mul]
    refine ⟨A⁻¹, D⁻¹, e, fun z => ?_⟩
    obtain ⟨a, ha⟩ := h2 ((D⁻¹).1 *ᵥ z)
    refine ⟨-((A⁻¹).1 *ᵥ a), ?_⟩
    have h3 := congrArg (mat u⁻¹ *ᵥ ·) ha
    simp only [Matrix.mulVec_add] at h3
    rw [Matrix.mulVec_mulVec _ (mat u⁻¹) (mat u), mat_inv_mul, Matrix.one_mulVec, Matrix.mulVec_mulVec z D.1,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec, Matrix.mulVec_mulVec a (mat u⁻¹) X, e,
      ← Matrix.mulVec_mulVec] at h3
    rw [h3, Matrix.mulVec_neg, add_neg_cancel_right]

variable (σ) in

def unipCols {d r m : ℕ} (J : Matrix (Fin d) (Fin d) E) (X : Matrix (Fin d) (Fin r) (AE F E))
    (I : Matrix (Fin d) (Fin m) (AE F E)) : Subgroup (UA σ J) where
  carrier := {u | mat u * X = X ∧ ∀ z, ∃ a, mat u *ᵥ (I *ᵥ z) = I *ᵥ z + X *ᵥ a}
  one_mem' := ⟨by simp [mat_one], fun z => ⟨0, by simp [mat_one]⟩⟩
  mul_mem' := by
    rintro u v ⟨h1, h2⟩ ⟨h1', h2'⟩
    refine ⟨?_, fun z => ?_⟩
    · rw [mat_mul, Matrix.mul_assoc, h1', h1]
    · obtain ⟨a', ha'⟩ := h2' z
      obtain ⟨a, ha⟩ := h2 z
      refine ⟨a + a', ?_⟩
      rw [mat_mul, ← Matrix.mulVec_mulVec, ha', Matrix.mulVec_add, ha, Matrix.mulVec_mulVec a' (mat u) X, h1,
        Matrix.mulVec_add, add_assoc]
  inv_mem' := by
    rintro u ⟨h1, h2⟩
    have e : mat u⁻¹ * X = X := by
      conv_lhs => rw [← h1, ← Matrix.mul_assoc, mat_inv_mul, Matrix.one_mul]
    refine ⟨e, fun z => ?_⟩
    obtain ⟨a, ha⟩ := h2 z
    refine ⟨-a, ?_⟩
    have h3 := congrArg (mat u⁻¹ *ᵥ ·) ha
    simp only [Matrix.mulVec_add] at h3
    rw [Matrix.mulVec_mulVec _ (mat u⁻¹) (mat u), mat_inv_mul, Matrix.one_mulVec,
      Matrix.mulVec_mulVec a (mat u⁻¹) X, e] at h3
    rw [Matrix.mulVec_neg, ← sub_eq_add_neg, eq_sub_iff_add_eq]
    exact h3.symm

section Cols

variable {d r m : ℕ} {J : Matrix (Fin d) (Fin d) E} {X : Matrix (Fin d) (Fin r) (AE F E)}
  {I : Matrix (Fin d) (Fin m) (AE F E)}

theorem act_inv {u : UA σ J} {A : GL (Fin r) (AE F E)} {D : GL (Fin m) (AE F E)} (h1 : mat u * X = X * A.1)
    (h2 : ∀ z, ∃ a, mat u *ᵥ (I *ᵥ z) = I *ᵥ (D.1 *ᵥ z) + X *ᵥ a) :
    mat u⁻¹ * X = X * (A⁻¹).1 ∧ ∀ z, ∃ a, mat u⁻¹ *ᵥ (I *ᵥ z) = I *ᵥ ((D⁻¹).1 *ᵥ z) + X *ᵥ a := by
  have e : mat u⁻¹ * X = X * (A⁻¹).1 := by
    have : X = mat u * (X * (A⁻¹).1) := by
      rw [← Matrix.mul_assoc, h1, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
    conv_lhs => rw [this, ← Matrix.mul_assoc, mat_inv_mul, Matrix.one_mul]
  refine ⟨e, fun z => ?_⟩
  obtain ⟨a, ha⟩ := h2 ((D⁻¹).1 *ᵥ z)
  refine ⟨-((A⁻¹).1 *ᵥ a), ?_⟩
  have h3 := congrArg (mat u⁻¹ *ᵥ ·) ha
  simp only [Matrix.mulVec_add] at h3
  rw [Matrix.mulVec_mulVec _ (mat u⁻¹) (mat u), mat_inv_mul, Matrix.one_mulVec, Matrix.mulVec_mulVec z D.1,
    ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec, Matrix.mulVec_mulVec a (mat u⁻¹) X, e,
    ← Matrix.mulVec_mulVec] at h3
  rw [h3, Matrix.mulVec_neg, add_neg_cancel_right]

theorem act_mul {u v : UA σ J} {A A' : GL (Fin r) (AE F E)} {D D' : GL (Fin m) (AE F E)}
    (h : mat u * X = X * A.1 ∧ ∀ z, ∃ a, mat u *ᵥ (I *ᵥ z) = I *ᵥ (D.1 *ᵥ z) + X *ᵥ a)
    (h' : mat v * X = X * A'.1 ∧ ∀ z, ∃ a, mat v *ᵥ (I *ᵥ z) = I *ᵥ (D'.1 *ᵥ z) + X *ᵥ a) :
    mat (u * v) * X = X * (A * A').1 ∧ ∀ z, ∃ a, mat (u * v) *ᵥ (I *ᵥ z) = I *ᵥ ((D * D').1 *ᵥ z) + X *ᵥ a := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  refine ⟨?_, fun z => ?_⟩
  · rw [mat_mul, Matrix.mul_assoc, h1', ← Matrix.mul_assoc, h1, Matrix.mul_assoc, Units.val_mul]
  · obtain ⟨a', ha'⟩ := h2' z
    obtain ⟨a, ha⟩ := h2 (D'.1 *ᵥ z)
    refine ⟨a + A.1 *ᵥ a', ?_⟩
    rw [mat_mul, ← Matrix.mulVec_mulVec, ha', Matrix.mulVec_add, ha, Matrix.mulVec_mulVec a' (mat u) X, h1,
      Matrix.mulVec_add, Units.val_mul, ← Matrix.mulVec_mulVec z D.1, ← Matrix.mulVec_mulVec a' X, add_assoc]

theorem mem_unipCols_iff {u : UA σ J} : u ∈ unipCols σ J X I ↔
    mat u * X = X * (1 : GL (Fin r) (AE F E)).1 ∧
      ∀ z, ∃ a, mat u *ᵥ (I *ᵥ z) = I *ᵥ ((1 : GL (Fin m) (AE F E)).1 *ᵥ z) + X *ᵥ a := by
  simp only [Units.val_one, Matrix.mul_one, Matrix.one_mulVec]; rfl

theorem conj_mem_unipCols {p n : UA σ J} (hp : p ∈ stabCols σ J X I) (hn : n ∈ unipCols σ J X I) :
    p * n * p⁻¹ ∈ unipCols σ J X I := by
  obtain ⟨A, D, h⟩ := hp
  have := act_mul (act_mul h (mem_unipCols_iff.1 hn)) (act_inv h.1 h.2)
  rw [mul_one, mul_one, mul_inv_cancel, mul_inv_cancel] at this
  exact mem_unipCols_iff.2 this

end Cols

variable (σ) in

def unipPar {d d₁ : ℕ} (W : Spc F E d) (H' : Plane E d d₁) (pl : ∀ j : ℕ, Plane E (d₁ - 2 * j) (d₁ - 2 * (j + 1)))
    (i : ℕ) : Subgroup (UA σ W.J) :=
  unipCols σ W.J (incM F (flagX H' pl (i + 1))) (incM F (chainEmb H' pl i))

section Flag

variable {d d₁ : ℕ} {W : Spc F E d} {H' : Plane E d d₁} {pl : ∀ j : ℕ, Plane E (d₁ - 2 * j) (d₁ - 2 * (j + 1))} {i : ℕ}

theorem mem_unipPar {u : UA σ W.J} : u ∈ unipPar σ W H' pl i ↔
    mat u * incM F (flagX H' pl (i + 1)) = incM F (flagX H' pl (i + 1)) ∧ ∀ z, ∃ a : Fin (i + 1) → AE F E,
      mat u *ᵥ (incM F (chainEmb H' pl i) *ᵥ z) = incM F (chainEmb H' pl i) *ᵥ z + incM F (flagX H' pl (i + 1)) *ᵥ a :=
  Iff.rfl

theorem unipPar_le_unipFlag : unipPar σ W H' pl i ≤ unipFlag σ W H' pl i := fun _ hu =>
  Subgroup.subset_closure ⟨⟨1, Matrix.blockTriangular_one, fun k => Matrix.one_apply_eq k, by
    rw [Matrix.mul_one]; exact hu.1⟩, hu.2⟩

theorem act_of_mem_unipFlag {u : UA σ W.J} (hu : u ∈ unipFlag σ W H' pl i) : ∃ A : GL (Fin (i + 1)) (AE F E),
    mat u * incM F (flagX H' pl (i + 1)) = incM F (flagX H' pl (i + 1)) * A.1 ∧ ∀ z, ∃ a,
      mat u *ᵥ (incM F (chainEmb H' pl i) *ᵥ z) =
        incM F (chainEmb H' pl i) *ᵥ ((1 : GL (Fin (d₁ - 2 * i)) (AE F E)).1 *ᵥ z) + incM F (flagX H' pl (i + 1)) *ᵥ a := by
  induction hu using Subgroup.closure_induction with
  | mem u h =>
    obtain ⟨⟨A, hA, h1, h2⟩, h3⟩ := h
    have hd : IsUnit A.det := by rw [Matrix.det_of_upperTriangular hA]; simp [h1]
    exact ⟨((Matrix.isUnit_iff_isUnit_det A).2 hd).unit, h2, by simpa using h3⟩
  | one => exact ⟨1, by simp [mat_one], fun z => ⟨0, by simp [mat_one]⟩⟩
  | mul u v _ _ hu hv =>
    obtain ⟨A, h⟩ := hu
    obtain ⟨A', h'⟩ := hv
    exact ⟨A * A', by simpa only [mul_one] using act_mul h h'⟩
  | inv u _ hu =>
    obtain ⟨A, h⟩ := hu
    exact ⟨A⁻¹, by simpa only [inv_one] using act_inv h.1 h.2⟩

theorem act_of_isLeviFlag {Y : Spc F E (d₁ - 2 * i)} {h₁ : UA σ Y.J} {m : UA σ W.J} (hm : IsLeviFlag H' pl i h₁ m) :
    mat m * incM F (flagX H' pl (i + 1)) = incM F (flagX H' pl (i + 1)) * (1 : GL (Fin (i + 1)) (AE F E)).1 ∧ ∀ z, ∃ a,
      mat m *ᵥ (incM F (chainEmb H' pl i) *ᵥ z) =
        incM F (chainEmb H' pl i) *ᵥ (h₁.1.1 *ᵥ z) + incM F (flagX H' pl (i + 1)) *ᵥ a :=
  ⟨by rw [Units.val_one, Matrix.mul_one]; exact hm.1, fun z => ⟨0, by
    rw [Matrix.mulVec_mulVec, hm.2.2, Matrix.mulVec_zero, add_zero, Matrix.mulVec_mulVec]; rfl⟩⟩

theorem conj_mem_unipPar {p n : UA σ W.J} (hp : p ∈ unipFlag σ W H' pl i) (hn : n ∈ unipPar σ W H' pl i) :
    p * n * p⁻¹ ∈ unipPar σ W H' pl i :=
  let ⟨A, h⟩ := act_of_mem_unipFlag hp
  conj_mem_unipCols ⟨A, 1, h⟩ hn

theorem levi_normalises {Y : Spc F E (d₁ - 2 * i)} {h₁ : UA σ Y.J} {m : UA σ W.J} (hm : IsLeviFlag H' pl i h₁ m)
    (n : UA σ W.J) : n ∈ unipPar σ W H' pl i ↔ m * n * m⁻¹ ∈ unipPar σ W H' pl i := by
  have h : m ∈ stabCols σ W.J (incM F (flagX H' pl (i + 1))) (incM F (chainEmb H' pl i)) :=
    ⟨1, h₁.1, act_of_isLeviFlag hm⟩
  exact ⟨conj_mem_unipCols h, fun hn => by simpa [mul_assoc, unipPar] using conj_mem_unipCols (inv_mem h) hn⟩

theorem comm_mem_unipPar {Y : Spc F E (d₁ - 2 * i)} {h₁ : UA σ Y.J} {m u : UA σ W.J} (hm : IsLeviFlag H' pl i h₁ m)
    (hu : u ∈ unipFlag σ W H' pl i) : u * m * u⁻¹ * m⁻¹ ∈ unipPar σ W H' pl i := by
  obtain ⟨A, h⟩ := act_of_mem_unipFlag hu
  have k := act_of_isLeviFlag hm
  have := act_mul (act_mul (act_mul h k) (act_inv h.1 h.2)) (act_inv k.1 k.2)
  rw [mul_one, mul_inv_cancel, inv_one, mul_one, one_mul, inv_one, mul_one, mul_inv_cancel] at this
  exact mem_unipCols_iff.2 this

end Flag

def LiftZero (ψ : AddChar (AF F) ℂ) {n m : ℕ} (JX : Matrix (Fin n) (Fin n) E) (JY : Matrix (Fin m) (Fin m) E)
    (χX χY : Chr F E) (f : UA σ JY → ℂ) : Prop :=
  ∀ co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JX) (incM F JY)) (Fin n × Fin m),
    (∀ x : Matrix (Fin n) (Fin m) E, ∃ y z : Fin n × Fin m → F,
      co.e (incM F x) = (fun k => algebraMap F (AF F) (y k), fun k => algebraMap F (AF F) (z k))) →
    ∀ om : UA σ JX × UA σ JY →* Module.End ℂ ((Fin n × Fin m → AF F) → ℂ),
      IsUWeilPair (cA σ) (adeleClass F) ψ (-1) (incM F JX) (incM F JY) co χX χY om →
      ∀ Φ ∈ schA F (Fin n × Fin m), ∀ (g : UA σ JX) (μ : Measure (UA σ JY)) (𝓕 : Set (UA σ JY)), μ.IsHaarMeasure →
        IsFundamentalDomain (ratU σ JY) 𝓕 μ → ∫ h in 𝓕, f h * (starRingEnd ℂ) (thetaSum F (om (g, h) Φ)) ∂μ = 0

end GlobalTheory.ThK.FlagPar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentFundamentalDomainIntegral
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThKCtFin GlobalTheory.TorFin

noncomputable section

namespace GlobalTheory.CtTransp

theorem setIntegral_unip_eq_constTerm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), IsCMExt F E σ → ∀ (d r s : ℕ) (W : Spc F E d), W.IsSkew σ B r s → ∀ (hσ : ∀ x, σ (σ x) = x) (c : E) (hc : c ≠ 0), σ c = -c → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ f : UA σ W.J → ℂ, ∀ (μ : Measure (unip σ W H')) (𝓕 : Set (unip σ W H')), μ.IsHaarMeasure → IsFundamentalDomain ((ratU σ W.J).subgroupOf (unip σ W H')) 𝓕 μ → μ 𝓕 = 1 → ∀ cc : GAd σ (c • W.J.map σ) → ℂ, IsConstTerm σ (c • W.J.map σ) (Matrix.of fun i (_ : Fin 1) => H'.x i) (fun x => f ((toGAd hσ W.J hc).symm x)) cc → ∀ g : UA σ W.J, ∫ u in 𝓕, f (u.1 * g) ∂μ = cc (toGAd hσ W.J hc g) := by
  intro F E _ _ _ _ _ σ B _ d r s W hW hσ c hc hcs d₁ W₁ H' i₀ i₁ hH f μ 𝓕 hμ h𝓕 h1 cc hcc g
  set C : Matrix (Fin d) (Fin 1) E := Matrix.of fun i (_ : Fin 1) => H'.x i with hCdef
  let e := toGAd hσ W.J hc
  have hmem := GlobalTheory.T.unipotent_mem_iff_unipotent_radical F E σ B d r s W hW hσ c hc hcs d₁ W₁ H' i₀ i₁ hH
  let e' : unip σ W H' ≃* unipRad σ (c • W.J.map σ) C :=
    { toFun := fun u => ⟨e u.1, (hmem u.1).1 u.2⟩
      invFun := fun v => ⟨e.symm v.1, (hmem _).2 (by rw [e.apply_symm_apply]; exact v.2)⟩
      left_inv := fun u => Subtype.ext (e.symm_apply_apply u.1)
      right_inv := fun v => Subtype.ext (e.apply_symm_apply v.1)
      map_mul' := fun u v => Subtype.ext (map_mul e u.1 v.1) }
  have he : Continuous e := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  have hes : Continuous e.symm := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  have he' : Continuous e' := (he.comp continuous_subtype_val).subtype_mk _
  have hes' : Continuous e'.symm := (hes.comp continuous_subtype_val).subtype_mk _
  haveI : BorelSpace (UA σ W.J) := ⟨rfl⟩
  haveI : ContinuousMul (UA σ W.J) := ⟨by
    have h : (fun p : UA σ W.J × UA σ W.J => p.1 * p.2) =
        e.symm ∘ (fun q : GAd σ (c • W.J.map σ) × GAd σ (c • W.J.map σ) => q.1 * q.2) ∘ Prod.map e e := by
      funext p
      simp
    rw [h]
    exact hes.comp (continuous_mul.comp (he.prodMap he))⟩
  haveI : ContinuousMul (unip σ W H') :=
    ⟨(continuous_mul.comp (continuous_subtype_val.prodMap continuous_subtype_val)).subtype_mk _⟩
  let t : unip σ W H' ≃ₜ unipRad σ (c • W.J.map σ) C := ⟨e'.toEquiv, he', hes'⟩
  let me := t.toMeasurableEquiv
  have hp : MeasurePreserving me μ (μ.map me) := ⟨me.measurable, rfl⟩
  have hH : (μ.map me).IsHaarMeasure := MulEquiv.isHaarMeasure_map μ e' he' hes'
  have hps : MeasurePreserving me.symm (μ.map me) μ := hp.symm
  have hmemU : ∀ γ : (ratPts σ (c • W.J.map σ)).subgroupOf (unipRad σ (c • W.J.map σ) C),
      e'.symm γ.1 ∈ (ratU σ W.J).subgroupOf (unip σ W H') := fun γ => by
    obtain ⟨u, -, hu2⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 γ.2))
    exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.2 ⟨u, hu2⟩)
  have hmemP : ∀ δ : (ratU σ W.J).subgroupOf (unip σ W H'),
      e' δ.1 ∈ (ratPts σ (c • W.J.map σ)).subgroupOf (unipRad σ (c • W.J.map σ) C) := fun δ => by
    obtain ⟨m, hm⟩ := Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 δ.2)
    have h2 := (e δ.1.1).2
    refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨m, ?_, hm⟩))
    exact unitary_of_map_inclR σ d _ m _ (by rw [hm]; rfl) h2
  let fm : (ratU σ W.J).subgroupOf (unip σ W H') →
      (ratPts σ (c • W.J.map σ)).subgroupOf (unipRad σ (c • W.J.map σ) C) := fun δ => ⟨e' δ.1, hmemP δ⟩
  have hf : Function.Bijective fm :=
    ⟨fun a b hab => Subtype.ext (e'.injective (congrArg Subtype.val hab)),
      fun γ => ⟨⟨e'.symm γ.1, hmemU γ⟩, Subtype.ext (e'.apply_symm_apply γ.1)⟩⟩
  have hfd := h𝓕.preimage_of_equiv hps.quasiMeasurePreserving hf fun δ x => by
    show e'.symm (e' δ.1 * x) = δ.1 * e'.symm x
    rw [map_mul, e'.symm_apply_apply]
  have hset : me ⁻¹' (me.symm ⁻¹' 𝓕) = 𝓕 := by
    ext x
    simp
  have hmass : (μ.map me) (me.symm ⁻¹' 𝓕) = 1 := by
    rw [me.map_apply, hset, h1]
  have hc' := hcc (μ.map me) (me.symm ⁻¹' 𝓕) hH hfd hmass (e g)
  rw [hc', ← hp.setIntegral_preimage_emb me.measurableEmbedding, hset]
  refine integral_congr_ae (.of_forall fun u => ?_)
  show f (u.1 * g) = f (e.symm (e u.1 * e g))
  rw [← map_mul, e.symm_apply_apply]

end GlobalTheory.CtTransp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalGradedIsotropicFlagLe
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open scoped TensorProduct

namespace GlobalTheory.TieStd

theorem unipFlag_castLE_le_unip : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ)
    (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (S : Finset (Fin r)) (s : ℕ) (hs : s ≤ r),
    (∀ i : Fin r, i.val < s ↔ ∃ k ∈ S, i ≤ k) → ∀ d : Fin s → ℕ, (∀ i, d i = (S.filter (· < Fin.castLE hs i)).card) →
    GlobalTheory.UAut.unipFlag σ J (X.submatrix id (Fin.castLE hs)) d ≤ GlobalTheory.StdPar.unip σ J X S := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW S s hs hS d hd
  rcases S.eq_empty_or_nonempty with rfl | hne
  · have hs0 : s = 0 := by
      by_contra h0
      obtain ⟨k, hk, -⟩ := (hS ⟨0, by omega⟩).1 (by simp only; omega)
      simp at hk
    subst hs0
    rw [GlobalTheory.StdPar.unip_empty]
    refine (Subgroup.closure_le _).2 fun g hg => ?_
    rw [SetLike.mem_coe, Subgroup.mem_bot]
    refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
    obtain ⟨a, ha⟩ := hg.2 (Pi.single j 1) (Subsingleton.elim _ _)
    have h0 : adMat F (X.submatrix id (Fin.castLE hs)) *ᵥ a = 0 := funext fun _ => by simp [Matrix.mulVec, dotProduct]
    have hv : (fun i => inclR (F := F) (AF F) ((Pi.single j (1 : E) : Fin n → E) i)) = Pi.single j 1 := by
      funext l
      by_cases hl : l = j
      · subst hl; simp
      · simp [Pi.single_apply, hl]
    rw [h0, hv, sub_mulVec, one_mulVec, sub_eq_zero, mulVec_single_one] at ha
    exact (congrFun ha i).trans (Pi.single_apply _ _ _)
  · obtain ⟨m, hmS, hmax⟩ : ∃ m ∈ S, ∀ k ∈ S, k ≤ m := ⟨S.max' hne, S.max'_mem hne, fun k hk => S.le_max' k hk⟩
    have hsm : s = m.val + 1 := by
      apply le_antisymm
      · by_contra hlt
        push_neg at hlt
        obtain ⟨k, hk, hle⟩ := (hS ⟨m.val + 1, by omega⟩).1 (by simp only; omega)
        have h2 := hmax k hk
        rw [Fin.le_def] at hle h2
        simp only at hle
        omega
      · have := (hS m).2 ⟨m, hmS, le_rfl⟩
        omega
    subst hsm
    have hd' : d = fun i => (S.filter fun k => k.val < i.val).card := by
      funext i
      rw [hd i]
      congr 1
    subst hd'
    exact GlobalTheory.FlagRad.unipFlag_le_unip F E σ h n J hJ r X Y hW S m hmS hmax

end GlobalTheory.TieStd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryTorusElementExistsStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_torus_element_exists : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n : ℕ) (X : Spc F E n) (r s : ℕ), B.IsGood σ → X.IsHerm σ B r s → ∀ (q : ℕ) (x y : Fin q → Fin n → E),
    IsFrameU σ X.J x y → ∀ t : Fin q → ℝ, (∀ i, 0 < t i) → ∃ a : UA σ X.J, IsTorusU x y t a := by
  first | exact @GlobalTheory.FrameTorus.exists_isTorusU | exact GlobalTheory.FrameTorus.exists_isTorusU | (intros; apply GlobalTheory.FrameTorus.exists_isTorusU <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumProductExistsNonzeroStatement
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.FinComm GlobalTheory.VacLine

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuum_product_exists_nonzero : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} (vac : ∀ v : Pl F, (κ → Fv F v) → ℂ), (∀ v, vac v ≠ 0) →
    (∀ᶠ v in cofinite, vac v = indO v) → ∃ y : κ → Af F, vacProd vac y ≠ 0 := by
  first | exact @GlobalTheory.VacLine.vacProd_ne_zero_somewhere | exact GlobalTheory.VacLine.vacProd_ne_zero_somewhere | (intros; apply GlobalTheory.VacLine.vacProd_ne_zero_somewhere <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumFixesVacuumNonSplitPlaceUnramifiedStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilDatum_fixes_vacuum_nonSplitPlace_unramified : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (χS χT : (AE D)ˣ →* Circle) (om : (GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))), (∃ η, IsEtaTilde D η) → IsWeilDatumO ψ S T χS χT om → ∀ v ε, NonSplitAt D v ε → UnramAt ε χS → UnramAt ε χT → FixesVacAt ψ S T ΛS ΛT om v ε := by
  first | exact @GlobalTheory.VacInert.fixesVacAt_of_unram | exact GlobalTheory.VacInert.fixesVacAt_of_unram | (intros; apply GlobalTheory.VacInert.fixesVacAt_of_unram <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumRealPlacesFockVacuumCharacterStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilDatum_realPlaces_fockVacuum_character : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (θ : InfFam D), IsInfFam θ → ∀ (χS χT : (AE D)ˣ →* Circle) (om : (GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))) (η : (AE D)ˣ →* Circle), IsEtaTilde D η → IsWeilDatumO ψ S T χS χT om → ∀ (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ g ∈ GinfC S, ∀ h ∈ GinfC T, (∀ τ, sS τ * compAt θ τ (Formalism.L2.Theta.mt S g) = compAt θ τ (Formalism.L2.Theta.mt S g) * sS τ) → (∀ τ, sT τ * compAt θ τ (Formalism.L2.Theta.mt T h) = compAt θ τ (Formalism.L2.Theta.mt T h) * sT τ) → ∀ x y, IsDetRoot S g x → IsDetRoot T h y → ∀ f, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → om (g, h) f = (((((χT * (η ^ T.rank)⁻¹) x)⁻¹ * (χS * (η ^ S.rank)⁻¹) y : Circle) : ℂ) * ∏ τ, detPlus (sS τ) (sT τ) (compAt θ τ (Formalism.L2.Theta.mt S g⁻¹)) (compAt θ τ (Formalism.L2.Theta.mt T h))) • f := by
  first | exact @GlobalTheory.WeilVacChar.vacuum_character | exact GlobalTheory.WeilVacChar.vacuum_character | (intros; apply GlobalTheory.WeilVacChar.vacuum_character <;> assumption)
end

