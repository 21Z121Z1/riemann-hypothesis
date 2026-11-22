import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0764
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1351
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1361
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0337
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0264
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0265
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0269
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0262
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Definitions.Divisors.MemL2OfSmoothVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FaithfulOfDerivationsDualFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1327
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1352
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0182
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1092
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0986
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1357
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMinpolyDefinitePairsTermNeZero
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1358
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealBasisGlLieAlgebraSumSqElementary
section
open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.HCA GroundTheory.Automorphic GlobalTheory.HCAlpha
open scoped ContDiff
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace GlobalTheory

theorem glBasis_sum_sq : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), ∃ (d : ℕ) (b : Module.Basis (Fin d) ℝ (glL E a)), ∀ (A : Type) [Ring A] [Algebra ℝ A] (ρ : glL E a →ₗ[ℝ] A), ∑ k, ρ (b k) * ρ (b k) = ∑ τ : E →+* ℂ, ∑ i : Fin a, ∑ j : Fin a, (ρ ⟨Matrix.single i j (atEmb τ 1), Submodule.mem_top⟩ ^ 2 + ρ ⟨Matrix.single i j (atEmb τ Complex.I), Submodule.mem_top⟩ ^ 2) := by
  intro E _ _ _ a
  classical
  let b0 : Module.Basis (Σ _ : InfinitePlace E, Fin 2) ℝ (Cinf E) := Pi.basis fun _ => Complex.basisOneI
  have hb0 : ∀ w s, b0 ⟨w, s⟩ = Pi.single w (Complex.basisOneI s) := by
    intro w s; simp [b0]
  let b1 := b0.matrix (Fin a) (Fin a)
  have hs : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have hu : ∀ _ : Fin a × Fin a × (Σ _ : InfinitePlace E, Fin 2), IsUnit (Real.sqrt 2) :=
    fun _ => IsUnit.mk0 _ hs.ne'
  let b2 := (b1.isUnitSMul hu).map (Submodule.topEquiv (R := ℝ) (M := Matrix (Fin a) (Fin a) (Cinf E))).symm
  let e := Fintype.equivFin (Fin a × Fin a × (Σ _ : InfinitePlace E, Fin 2))
  refine ⟨_, b2.reindex e, ?_⟩
  intro A _ _ ρ
  let F : InfinitePlace E → Fin a → Fin a → A := fun w i j =>
    ρ ⟨Matrix.single i j (Pi.single w 1), Submodule.mem_top⟩ ^ 2 +
      ρ ⟨Matrix.single i j (Pi.single w Complex.I), Submodule.mem_top⟩ ^ 2
  let G : InfinitePlace E → A := fun w => ∑ i, ∑ j, F w i j
  have hsm : ∀ (r : ℝ) (X : Matrix (Fin a) (Fin a) (Cinf E)),
      ρ ⟨r • X, Submodule.mem_top⟩ = r • ρ ⟨X, Submodule.mem_top⟩ := by
    intro r X
    rw [← map_smul]; rfl
  have hb2 : ∀ i j w s, ρ (b2 (i, j, ⟨w, s⟩)) * ρ (b2 (i, j, ⟨w, s⟩)) =
      ρ ⟨Matrix.single i j (Pi.single w (Complex.basisOneI s)), Submodule.mem_top⟩ ^ 2 +
      ρ ⟨Matrix.single i j (Pi.single w (Complex.basisOneI s)), Submodule.mem_top⟩ ^ 2 := by
    intro i j w s
    have : b2 (i, j, ⟨w, s⟩) = ⟨Real.sqrt 2 • Matrix.single i j (Pi.single w (Complex.basisOneI s)), Submodule.mem_top⟩ := by
      apply Subtype.ext
      simp [b2, b1, Module.Basis.isUnitSMul_apply, hb0]
    rw [this, hsm, smul_mul_smul, Real.mul_self_sqrt (by norm_num), two_smul, sq]
  have hL : ∑ k, ρ (b2.reindex e k) * ρ (b2.reindex e k) = ∑ w, (G w + G w) := by
    simp only [Module.Basis.reindex_apply]
    rw [Equiv.sum_comp e.symm (fun x => ρ (b2 x) * ρ (b2 x))]
    simp only [Fintype.sum_prod_type, Fintype.sum_sigma, Fin.sum_univ_two, hb2, Complex.coe_basisOneI,
      Matrix.cons_val_zero, Matrix.cons_val_one, G, F]
    simp only [← Finset.sum_add_distrib]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun w _ => ?_
    abel
  have hτ : ∀ τ : E →+* ℂ, ∀ i j,
      ρ ⟨Matrix.single i j (atEmb τ 1), Submodule.mem_top⟩ ^ 2 +
        ρ ⟨Matrix.single i j (atEmb τ Complex.I), Submodule.mem_top⟩ ^ 2 = F (InfinitePlace.mk τ) i j := by
    intro τ i j
    have hA1 : atEmb τ 1 = Pi.single (InfinitePlace.mk τ) 1 := by
      unfold atEmb; split_ifs <;> simp
    have hAI : ρ ⟨Matrix.single i j (atEmb τ Complex.I), Submodule.mem_top⟩ ^ 2 =
        ρ ⟨Matrix.single i j (Pi.single (InfinitePlace.mk τ) Complex.I), Submodule.mem_top⟩ ^ 2 := by
      unfold atEmb
      split_ifs with h
      · rfl
      · have h1 : (⟨Matrix.single i j (Pi.single (InfinitePlace.mk τ) (starRingEnd ℂ Complex.I)), Submodule.mem_top⟩ : glL E a) =
            -⟨Matrix.single i j (Pi.single (InfinitePlace.mk τ) Complex.I), Submodule.mem_top⟩ := by
          apply Subtype.ext
          simp [Pi.single_neg, Matrix.single_neg]
        rw [h1, map_neg, neg_sq]
    simp only [F, hAI, hA1]
  have hR : ∑ τ : E →+* ℂ, ∑ i : Fin a, ∑ j : Fin a,
      (ρ ⟨Matrix.single i j (atEmb τ 1), Submodule.mem_top⟩ ^ 2 +
        ρ ⟨Matrix.single i j (atEmb τ Complex.I), Submodule.mem_top⟩ ^ 2) = ∑ w, (G w + G w) := by
    simp only [hτ]
    change ∑ τ : E →+* ℂ, G (InfinitePlace.mk τ) = _
    rw [← Finset.sum_fiberwise Finset.univ InfinitePlace.mk (fun τ => G (InfinitePlace.mk τ))]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => G w) (fun τ hτ' => by rw [(Finset.mem_filter.1 hτ').2]),
      Finset.sum_const, InfinitePlace.card_filter_mk_eq]
    have : w.mult = 2 := by
      simp [InfinitePlace.mult, InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)]
    rw [this, two_smul]
  rw [hL, hR]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistCuspidalTrivialOnSplitCentre
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace GlobalTheory.GKNorm

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem exists_splitCentre_eigen (π : CuspSub E a) : ∃ c : ℂ, ∀ φ ∈ π.V, ∀ (t : ℝ) (g : GA E a),
    φ.1 (GlobalTheory.UnitaryBC.splitCentre E a t * g) = Complex.exp (c * t) * φ.1 g := by
  obtain ⟨c, hc⟩ := GlobalTheory.CuspRep.Central.lie_scalar π (1 : Cinf E)
  refine ⟨c, fun φ hφ t g => ?_⟩
  have e3 : GlobalTheory.CuspRep.Central.scL a (fun _ : InfinitePlace E => (t : ℂ)) =
      t • GlobalTheory.CuspRep.Central.scL (E := E) a 1 := by
    ext i j w
    by_cases hij : i = j <;> simp [hij]
  have h1 := GlobalTheory.CuspRep.Central.rs_exp (fun _ : InfinitePlace E => (t : ℂ)) (c * t) φ (by
    rw [e3, map_smul, LinearMap.smul_apply, hc φ hφ, mul_comm, mul_smul, Complex.coe_smul])
  rw [GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm, GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_eq_scalar]
  exact congrFun (congrArg Subtype.val h1) g

theorem exists_twist_isNormalised : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a →
    ∀ π : CuspSub E a, ∃ χ : HChar E, GlobalTheory.DiscSpec.IsNormalised (π.twist χ) := by
  intro E _ _ _ a ha π
  obtain ⟨c, hs⟩ := exists_splitCentre_eigen π
  obtain ⟨χ, hχ⟩ := GlobalTheory.CuspQuot.exists_chiDet_splitCentre (E := E) (a := a) (by omega) (-c)
  refine ⟨χ, ?_⟩
  rintro _ ⟨φ, hφ, rfl⟩ t g
  change (mulChi a χ φ).1 _ = (mulChi a χ φ).1 _
  rw [mulChi_apply, mulChi_apply, map_mul, Units.val_mul, hχ, hs φ hφ, mul_mul_mul_comm, ← Complex.exp_add]
  simp

end GlobalTheory.GKNorm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueAdmissibleLocalComponentDefiniteUnit
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.LocCompU

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isIrreducible_comp_of_surjective {H H' X : Type} [Group H] [Group H'] [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ H X) (φ : H' →* H) (hφ : Function.Surjective φ) (h : ρ.IsIrreducible) :
    Representation.IsIrreducible (ρ.comp φ) := by
  obtain ⟨h0, h1⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 h
  refine (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨h0, fun W hW => h1 W fun g v hv => ?_⟩
  obtain ⟨g', rfl⟩ := hφ g
  exact hW g' v hv

theorem isClosed_UL (hU : Unr E) (n : ℕ) (w : Pl E) : IsClosed (UL n w : Set (GLw n w)) := by
  unfold UL
  split_ifs
  · exact isClosed_univ
  · have hc := (GlobalTheory.ConjAtPlace.main E hU w).1
    have : Continuous fun g : GLw n w =>
        cT (cj w) (g : Matrix (Fin n) (Fin n) _) * 1 * (g : Matrix (Fin n) (Fin n) _) := by
      refine Continuous.mul (Continuous.mul ?_ continuous_const) Units.continuous_val
      exact continuous_matrix fun i j => hc.comp (Units.continuous_val.matrix_elem _ _)
    exact isClosed_singleton.preimage this

theorem isOpen_isCompact_KL (hU : Unr E) (n : ℕ) (w : Pl E) :
    IsOpen (KL n w : Set (UL n w)) ∧ IsCompact (KL n w : Set (UL n w)) := by
  have hK := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n
  rw [KL, Subgroup.coe_subgroupOf]
  exact ⟨hK.1.preimage continuous_subtype_val,
    (isClosed_UL hU n w).isClosedEmbedding_subtypeVal.isCompact_preimage hK.2⟩

theorem exists_equiv (hU : Unr E) (n : ℕ) (w : Pl E) :
    ∃ e : locU n w ≃ₜ* UL n w, ∀ x : locU n w, ((e x : UL n w) : GLw n w) = cLoc w (x : UA E n) := by
  by_cases hs : IsSplitAt w
  · obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E n w hs
    have h : UL n w = ⊤ := if_pos hs
    have hm : ∀ g : GLw n w, g ∈ UL n w := fun g => by rw [h]; exact Subgroup.mem_top _
    refine ⟨{ toFun := fun x => ⟨e x, hm _⟩
              invFun := fun g => e.symm g.1
              left_inv := fun x => by simp
              right_inv := fun g => Subtype.ext (by simp)
              map_mul' := fun x y => Subtype.ext (by simp)
              continuous_toFun := e.continuous.subtype_mk _
              continuous_invFun := e.symm.continuous.comp continuous_subtype_val }, fun x => he x⟩
  · obtain ⟨-, -, hv, hns, -⟩ := GlobalTheory.ConjAtPlace.main E hU w
    obtain ⟨e, he⟩ := GlobalTheory.DefU.Inert.locU_equiv E n w (cj w) (hns hs).1 hv
    have h : UL n w = UJ (cj w) 1 := if_neg hs
    rw [h]
    exact ⟨e, he⟩

theorem exists_unique_locComp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n →
    ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ w : Pl E,
    (∃ σ : SmIrr (UL n w), IsCompU π w σ ∧
      ∀ U : Subgroup (UL n w), IsOpen (U : Set (UL n w)) → FiniteDimensional ℂ (fixed σ.ρ U)) ∧
    ∀ σ σ' : SmIrr (UL n w), IsCompU π w σ → IsCompU π w σ' → Nonempty (σ.ρ.Equiv σ'.ρ) := by
  intro E _ _ _ hU n _ π hπ w
  obtain ⟨e, he⟩ := exists_equiv hU n w
  obtain ⟨hKo, hKc⟩ := isOpen_isCompact_KL hU n w
  have hesurj : Function.Surjective (e.toMulEquiv.symm.toMonoidHom) := e.symm.surjective
  refine ⟨?_, ?_⟩
  · obtain ⟨σ₀, hadm, hirr, f, hf0, hfm, hf⟩ := GlobalTheory.DefU.LocAdm.exists_admissible_comp E n ⟨π, hπ⟩ w
    let ρ : Representation ℂ (UL n w) σ₀.V := σ₀.ρ.comp e.toMulEquiv.symm.toMonoidHom
    have hρ : ∀ g v, ρ g v = σ₀.ρ (e.symm g) v := fun _ _ => rfl
    let σ : SmIrr (UL n w) :=
      { V := σ₀.V
        ρ := ρ
        smooth := fun v => (σ₀.smooth v).preimage e.symm.continuous
        irred := isIrreducible_comp_of_surjective σ₀.ρ _ hesurj σ₀.irred }
    refine ⟨σ, ⟨e.toMulEquiv.toMonoidHom, fun x => he x, σ.irred, f, hf0, hfm, fun x v => ?_⟩, fun U hUo => ?_⟩
    · change f (σ₀.ρ (e.symm (e x)) v) = _
      rw [e.symm_apply_apply]
      exact hf x v
    · let K' : Subgroup (locU n w) := (U ⊓ KL n w).comap e.toMulEquiv.toMonoidHom
      have hK'o : IsOpen (K' : Set (locU n w)) := by
        change IsOpen (e ⁻¹' ((U : Set (UL n w)) ∩ (KL n w : Set (UL n w))))
        exact (hUo.inter hKo).preimage e.continuous
      have hK'c : IsCompact (K' : Set (locU n w)) := by
        change IsCompact (e ⁻¹' ((U : Set (UL n w)) ∩ (KL n w : Set (UL n w))))
        exact e.toHomeomorph.isCompact_preimage.2 (hKc.inter_left (U.isClosed_of_isOpen hUo))
      haveI := hadm.2 K' hK'o hK'c
      have hle : fixed σ.ρ U ≤ fixed σ₀.ρ K' := by
        intro v hv k
        have h1 := hv ⟨e k, k.2.1⟩
        simp only [MonoidHom.one_apply, Units.val_one, one_smul] at h1 ⊢
        change σ₀.ρ (e.symm (e k)) v = v at h1
        rwa [e.symm_apply_apply] at h1
      exact Submodule.finiteDimensional_of_le hle
  · rintro σ σ' ⟨p, hp, -, f, hf0, hfm, hf⟩ ⟨p', hp', -, f', hf0', hfm', hf'⟩
    have hpe : ∀ x, p x = e x := fun x => Subtype.ext ((hp x).trans (he x).symm)
    have hpe' : ∀ x, p' x = e x := fun x => Subtype.ext ((hp' x).trans (he x).symm)
    have hps : Function.Surjective p := fun g => ⟨e.symm g, by rw [hpe, e.apply_symm_apply]⟩
    have hps' : Function.Surjective p' := fun g => ⟨e.symm g, by rw [hpe', e.apply_symm_apply]⟩
    obtain ⟨r, -, -, hr2⟩ := GlobalTheory.DefU.LocRet.exists_ret E n w
    let π' : GlobalTheory.DefU.AutSub E n := ⟨π, hπ⟩
    let F : Representation.IntertwiningMap (σ.ρ.comp p) (π'.rep.comp (locU n w).subtype) :=
      ⟨f.codRestrict π hfm, fun x => LinearMap.ext fun v => Subtype.ext (hf x v)⟩
    let F' : Representation.IntertwiningMap (σ'.ρ.comp p') (π'.rep.comp (locU n w).subtype) :=
      ⟨f'.codRestrict π hfm', fun x => LinearMap.ext fun v => Subtype.ext (hf' x v)⟩
    have hF0 : F ≠ 0 := fun h =>
      hf0 (LinearMap.ext fun v => congrArg Subtype.val (DFunLike.congr_fun h v))
    have hF0' : F' ≠ 0 := fun h =>
      hf0' (LinearMap.ext fun v => congrArg Subtype.val (DFunLike.congr_fun h v))
    obtain ⟨-, h2⟩ := GlobalTheory.CuspRep.CompUniq.isotypic (UA E n) (locU n w) π σ.V σ'.V π'.rep (locU n w).subtype
      (σ.ρ.comp p) (σ'.ρ.comp p') π'.isIrreducible_rep
      (isIrreducible_comp_of_surjective σ.ρ p hps σ.irred)
      (isIrreducible_comp_of_surjective σ'.ρ p' hps' σ'.irred)
      (fun g => ⟨r g, fun y => hr2 g y⟩) F hF0
    obtain ⟨T⟩ := h2 F' hF0'
    refine ⟨{ toLinearEquiv := T.toLinearEquiv, isIntertwining' := fun g => ?_ }⟩
    have h1 : p (e.symm g) = g := by rw [hpe, e.apply_symm_apply]
    have h1' : p' (e.symm g) = g := by rw [hpe', e.apply_symm_apply]
    have := T.isIntertwining' (e.symm g)
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, h1, h1'] at this
    exact this

end GlobalTheory.BCT.LocCompU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpGLImageBallMemNhds
section
open NumberField MeasureTheory Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.GLFin

noncomputable section

namespace GlobalTheory.GLFin

theorem expGL_image_ball_mem_nhds : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), ∀ ε : ℝ, 0 < ε →
    (fun X : Lie E a => GlobalTheory.ExpDeriv.expGL X 1) '' {X | ‖X‖ < ε} ∈ nhds (1 : GL (Fin a) (Cinf E)) := by
  intro E _ _ _ a ε hε
  letI : NormedRing (Matrix (Fin a) (Fin a) (Cinf E)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin a) (Fin a) (Cinf E)) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix (Fin a) (Fin a) (Cinf E)) := FiniteDimensional.complete ℝ _
  have hd : HasStrictFDerivAt (NormedSpace.exp : Matrix (Fin a) (Fin a) (Cinf E) → _)
      ((ContinuousLinearEquiv.refl ℝ (Matrix (Fin a) (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E) →L[ℝ] _)) 0 :=
    hasStrictFDerivAt_exp_zero
  have hmap0 := hd.map_nhds_eq_of_equiv
  rw [NormedSpace.exp_zero] at hmap0
  have hmap : Filter.map (NormedSpace.exp : Matrix (Fin a) (Fin a) (Cinf E) → _) (nhds 0) =
      nhds (1 : Matrix (Fin a) (Fin a) (Cinf E)) := hmap0
  have hopen : IsOpen {X : Matrix (Fin a) (Fin a) (Cinf E) | ‖(Matrix.of.symm X : Lie E a)‖ < ε} :=
    isOpen_lt (continuous_norm.comp (continuous_id : Continuous fun X : Lie E a => X)) continuous_const
  have hball : {X : Matrix (Fin a) (Fin a) (Cinf E) | ‖(Matrix.of.symm X : Lie E a)‖ < ε} ∈
      nhds (0 : Matrix (Fin a) (Fin a) (Cinf E)) := hopen.mem_nhds (by simpa using hε)
  have himg : (NormedSpace.exp : Matrix (Fin a) (Fin a) (Cinf E) → _) ''
      {X : Matrix (Fin a) (Fin a) (Cinf E) | ‖(Matrix.of.symm X : Lie E a)‖ < ε} ∈
      nhds (1 : Matrix (Fin a) (Fin a) (Cinf E)) := hmap ▸ Filter.image_mem_map hball
  have hpre := Units.continuous_val.continuousAt.preimage_mem_nhds (x := (1 : GL (Fin a) (Cinf E))) himg
  refine Filter.mem_of_superset hpre ?_
  rintro u ⟨X, hX, hXu⟩
  refine ⟨Matrix.of.symm X, hX, Units.ext ?_⟩
  rw [GlobalTheory.ExpDeriv.expGL_val, one_smul]
  exact hXu

end GlobalTheory.GLFin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FaithfulOfDerivationsDualFamilyStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CentralOps
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.faithful_of_derivations_dualFamily : ∀ (U A ι : Type) [Ring U] [Algebra ℂ U] [CommRing A] [Algebra ℂ A] [Fintype ι] [DecidableEq ι] (e : ι → U), Algebra.adjoin ℂ (Set.range e) = ⊤ → (∀ a b, e a * e b - e b * e a ∈ Submodule.span ℂ (Set.range e)) → ∀ (π : U →ₐ[ℂ] Module.End ℂ A), (∀ k (x y : A), π (e k) (x * y) = π (e k) x * y + x * π (e k) y) → ∀ (χ : A →ₐ[ℂ] ℂ) (a : ι → A), (∀ k, χ (a k) = 0) → (∀ i k, χ (π (e i) (a k)) = if i = k then 1 else 0) → ∀ u : U, (∀ x : A, χ (π u x) = 0) → u = 0 := by
  first | exact @GlobalTheory.faithful_of_derivations_dual_family | exact GlobalTheory.faithful_of_derivations_dual_family | (intros; apply GlobalTheory.faithful_of_derivations_dual_family <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteClosedRingStableSubgroupAbelianNoTorsionStatement
section
open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_closed_ringStable_subgroup_abelian_no_torsion : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (B : Over (Sp k)) [GrpObj B] (act : OAct (𝓞 E) B) (π : 𝓞 E), IsAbelianScheme B → π ≠ 0 → ¬ IsUnit π → ∀ (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ B)) (Z : Set B.left), IsClosed Z → (∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) → (∀ (a : 𝓞 E), ∀ x ∈ C, x ≫ act.act a ∈ C) → (∀ x ∈ C, x ≫ act.act π = 1 → x = 1) → Finite C := by
  first | exact @GlobalTheory.OStableAbelian.finite_of_isClosed_of_no_torsion | exact GlobalTheory.OStableAbelian.finite_of_isClosed_of_no_torsion | (intros; apply GlobalTheory.OStableAbelian.finite_of_isClosed_of_no_torsion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteKottwitzClassesPerMinpolyAEqOne
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx.PeriodicClassFixedPoints

variable {p : ℕ} [Fact p.Prime]

theorem sh_mul' (G : HTGroup p) (a b : G.C) : sh G (a * b) = sh G b * sh G a := by
  simp only [sh, map_mul, MulOpposite.unop_mul]

theorem sh_one' (G : HTGroup p) : sh G 1 = 1 := by simp [sh]

theorem sh_mul_inv' (G : HTGroup p) (e : G.Cˣ) : sh G (e : G.C) * sh G ((e⁻¹ : G.Cˣ) : G.C) = 1 := by
  rw [← sh_mul', Units.inv_mul, sh_one']

theorem commute_ratio (G : HTGroup p) (β β₁ γ : G.Cˣ) (c : ℚ) (hc : c ≠ 0)
    (h : (γ : G.C) * β * sh G γ = algebraMap ℚ G.C c * β)
    (h₁ : (γ : G.C) * β₁ * sh G γ = algebraMap ℚ G.C c * β₁) :
    Commute ((β : G.C) * ((β₁⁻¹ : G.Cˣ) : G.C)) (γ : G.C) := by
  have hs : sh G γ = ((β₁⁻¹ : G.Cˣ) : G.C) * ((γ⁻¹ : G.Cˣ) : G.C) * (algebraMap ℚ G.C c * β₁) := by
    rw [← h₁]; simp [mul_assoc]
  rw [hs, ← Algebra.smul_def, ← Algebra.smul_def] at h
  simp only [mul_smul_comm] at h
  have h2 : (γ : G.C) * β * (((β₁⁻¹ : G.Cˣ) : G.C) * ((γ⁻¹ : G.Cˣ) : G.C) * β₁) = β := smul_right_injective G.C hc h
  have h3 : (γ : G.C) * β * ((β₁⁻¹ : G.Cˣ) : G.C) * ((γ⁻¹ : G.Cˣ) : G.C) = β * ((β₁⁻¹ : G.Cˣ) : G.C) := by
    conv_rhs => rw [← h2]
    simp [mul_assoc]
  show (β : G.C) * ((β₁⁻¹ : G.Cˣ) : G.C) * γ = γ * (β * ((β₁⁻¹ : G.Cˣ) : G.C))
  calc (β : G.C) * ((β₁⁻¹ : G.Cˣ) : G.C) * γ
      = ((γ : G.C) * β * ((β₁⁻¹ : G.Cˣ) : G.C) * ((γ⁻¹ : G.Cˣ) : G.C)) * γ := by rw [h3]
    _ = γ * (β * ((β₁⁻¹ : G.Cˣ) : G.C)) := by simp [mul_assoc]

theorem tau_ratio (G : HTGroup p) (β β₁ : G.Cˣ) (h : sh G β = β) (h₁ : sh G β₁ = β₁) :
    (β₁ : G.C) * sh G ((β : G.C) * ((β₁⁻¹ : G.Cˣ) : G.C)) * ((β₁⁻¹ : G.Cˣ) : G.C) =
      (β : G.C) * ((β₁⁻¹ : G.Cˣ) : G.C) := by
  have e : (β₁ : G.C) * sh G ((β₁⁻¹ : G.Cˣ) : G.C) = 1 := by
    conv_lhs => rw [← h₁]
    exact sh_mul_inv' G β₁
  rw [sh_mul', h, ← mul_assoc, e, one_mul]

theorem rel_of_same (G : HTGroup p) (β₁ γ₀ : G.Cˣ) (a₀ : G.C) (P Q : Pair G) (hP : P.γ = γ₀) (hQ : Q.γ = γ₀)
    (r r' : ℚˣ) (e e' : G.Cˣ) (he : Commute (e : G.C) γ₀) (he' : Commute (e' : G.C) γ₀)
    (hr : (0 < (r : ℚ)) ↔ (0 < (r' : ℚ)))
    (hPβ : (P.β : G.C) = algebraMap ℚ G.C r * ((e : G.C) * a₀ * β₁ * sh G (e : G.C)))
    (hQβ : (Q.β : G.C) = algebraMap ℚ G.C r' * ((e' : G.C) * a₀ * β₁ * sh G (e' : G.C))) : Pair.Rel P Q := by
  refine ⟨e' * e⁻¹, (r' : ℚ) / r, ?_, ?_, ?_⟩
  · rcases lt_or_gt_of_ne r.ne_zero with h | h
    · have hn : ¬ (0 < (r' : ℚ)) := fun h0 => absurd (hr.2 h0) (not_lt.2 h.le)
      exact div_pos_of_neg_of_neg (lt_of_le_of_ne (not_lt.1 hn) r'.ne_zero) h
    · exact div_pos (hr.1 h) h
  · rw [hQβ, hPβ, ← Algebra.smul_def, ← Algebra.smul_def, ← Algebra.smul_def]
    simp only [mul_smul_comm, smul_mul_assoc, smul_smul]
    have hrr : (r' : ℚ) / r * r = r' := by field_simp
    rw [hrr]
    congr 1
    rw [Units.val_mul, sh_mul']
    calc (e' : G.C) * a₀ * β₁ * sh G (e' : G.C)
        = (e' : G.C) * (((e⁻¹ : G.Cˣ) : G.C) * e) * a₀ * β₁ * (sh G (e : G.C) * sh G ((e⁻¹ : G.Cˣ) : G.C)) * sh G (e' : G.C) := by
          rw [Units.inv_mul, sh_mul_inv', mul_one, mul_one]
      _ = _ := by simp only [mul_assoc]
  · have hc : Commute ((e' * e⁻¹ : G.Cˣ) : G.C) (γ₀ : G.C) := by
      rw [Units.val_mul]; exact he'.mul_left he.units_inv_left
    ext
    rw [hP, hQ, Units.val_mul, Units.val_mul, hc.eq, mul_assoc, Units.mul_inv, mul_one]

theorem exists_point_of_term_ne_zero' {G : HTGroup p} (P : Pair G) (Kf : Subgroup G.GAf)
    (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ) (h : P.term Kf f r K φ ≠ 0) :
    ∃ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) (g : G.GAf),
      f (g⁻¹ * P.toAf x t hx P.self * g) ≠ 0 := by
  unfold Pair.term at h
  split_ifs at h with hd
  · unfold Pair.termAt pointSum at h
    obtain ⟨q, hq⟩ := not_forall.1 (fun hc => h (finsum_eq_zero_of_forall_eq_zero hc))
    refine ⟨_, _, P.trivAf.choose_spec.choose_spec, (Quotient.out q).1, fun h0 => hq ?_⟩
    rw [h0, zero_mul, mul_zero]
  · exact absurd rfl h

theorem finite_fixed (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ)
    (hf : IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f) (hreg : ∀ g, f g ≠ 0 → RegAf G g)
    (γ₀ : G.Cˣ) (c₀ : ℚˣ) :
    {q : Cls G | ∃ P : Pair G, (Quot.mk Pair.Rel P : Cls G) = q ∧ P.γ = γ₀ ∧ P.c = c₀ ∧
      ∃ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) (g : G.GAf),
        f (g⁻¹ * P.toAf x t hx P.self * g) ≠ 0}.Finite := by
  by_cases hne : ∃ P₁ : Pair G, P₁.γ = γ₀ ∧ P₁.c = c₀
  swap
  · refine Set.finite_empty.subset ?_
    rintro q ⟨P, -, hγ, hc, -⟩
    exact hne ⟨P, hγ, hc⟩
  obtain ⟨P₁, rfl, rfl⟩ := hne
  obtain ⟨S, hS⟩ := GlobalTheory.T.kottwitzPair_form_ratio_local_scalar_norm p G L f hf hreg P₁
  obtain ⟨A, hA⟩ := GlobalTheory.T.finite_fixed_unit_classes_centralizer_regular p G P₁.β P₁.sym P₁.γ P₁.c P₁.sim P₁.reg.2 P₁.reg.1 S
  let D : G.C × Bool → Pair G → Prop := fun ab P => P.γ = P₁.γ ∧ ∃ (r : ℚˣ) (e : G.Cˣ),
    Commute (e : G.C) P₁.γ ∧ decide (0 < (r : ℚ)) = ab.2 ∧
    (P.β : G.C) = algebraMap ℚ G.C r * ((e : G.C) * ab.1 * P₁.β * sh G (e : G.C))
  let ρ : G.C × Bool → Cls G := fun ab => if h : ∃ P, D ab P then Quot.mk _ h.choose else Quot.mk _ P₁
  refine (Finset.finite_toSet ((A ×ˢ (Finset.univ : Finset Bool)).image ρ)).subset ?_
  rintro q ⟨P, rfl, hγ, hc, x, t, hx, g, hg⟩
  have hcomm := commute_ratio G P.β P₁.β P₁.γ P₁.c P₁.c.ne_zero (by rw [← hγ, ← hc]; exact P.sim) P₁.sim
  have hτ := tau_ratio G P.β P₁.β P.sym P₁.sym
  have hu : IsUnit ((P.β : G.C) * ((P₁.β⁻¹ : G.Cˣ) : G.C)) := by
    simpa using (P.β * P₁.β⁻¹).isUnit
  obtain ⟨a₀, ha₀, r, e, he, hre⟩ := hA _ hu hcomm hτ (fun ℓ _ hℓ => hS P hγ hc x t hx g hg ℓ hℓ)
  have hβeq : (P.β : G.C) = algebraMap ℚ G.C r * ((e : G.C) * a₀ * P₁.β * sh G (e : G.C)) := by
    calc (P.β : G.C) = ((P.β : G.C) * ((P₁.β⁻¹ : G.Cˣ) : G.C)) * P₁.β := by simp [mul_assoc]
      _ = _ := by rw [hre]; simp [mul_assoc]
  have hex : ∃ P', D (a₀, decide (0 < (r : ℚ))) P' := ⟨P, hγ, r, e, he, rfl, hβeq⟩
  refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨(a₀, decide (0 < (r : ℚ))),
    Finset.mem_product.2 ⟨ha₀, Finset.mem_univ _⟩, ?_⟩)
  have hρ : ρ (a₀, decide (0 < (r : ℚ))) = Quot.mk _ hex.choose := dif_pos hex
  rw [hρ]
  obtain ⟨hγ', r', e', he', hb', hβ'⟩ := hex.choose_spec
  refine Quot.sound (rel_of_same G P₁.β P₁.γ a₀ _ P hγ' hγ r' r e' e he' he ?_ hβ' hβeq)
  rw [← decide_eq_decide]; exact hb'

theorem finite_classes_of_pol_a_one : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → (∀ g, f g ≠ 0 → RegAf G g) → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ P0 : Polynomial G.F, {q : Cls G | (Quot.out q).pol = P0 ∧ (∃ μ, (Quot.out q).Mark μ) ∧ (Quot.out q).term L.K.toSubgroup f 1 K' f' ≠ 0}.Finite := by
  intro p _ G _ L f hf hreg K' f' _ P0
  by_cases hne : {q : Cls G | (Quot.out q).pol = P0 ∧ (∃ μ, (Quot.out q).Mark μ) ∧
      (Quot.out q).term L.K.toSubgroup f 1 K' f' ≠ 0}.Nonempty
  · obtain ⟨q₀, hq₀⟩ := hne
    refine ((finite_fixed G L f hf hreg (Quot.out q₀).γ (Quot.out q₀).c).union
      (finite_fixed G L f hf hreg (Quot.out q₀).γ (-(Quot.out q₀).c))).subset ?_
    intro q hq
    obtain ⟨x, t, hx, g, hg⟩ := exists_point_of_term_ne_zero' _ _ _ _ _ _ hq.2.2
    obtain ⟨y, hy⟩ := GlobalTheory.LKCx.ClsReg.units_conj_of_minpoly_eq_of_separable G (Quot.out q).γ (Quot.out q₀).γ
      (hq.1.trans hq₀.1.symm) (Quot.out q₀).reg.2 (Quot.out q₀).reg.1
    obtain ⟨P', hrel, hγ, -, htr⟩ := GlobalTheory.LKMid.Pair.exists_conj p G (Quot.out q) y⁻¹
    obtain ⟨x', hx', he⟩ := htr x t hx
    have hq' : (Quot.mk Pair.Rel P' : Cls G) = q := by
      rw [← Quot.sound hrel]; exact Quot.out_eq q
    have hγ' : P'.γ = (Quot.out q₀).γ := by
      rw [hγ]; ext
      rw [Units.val_mul, Units.val_mul, hy]
      simp [mul_assoc]
    have hg' : f (g⁻¹ * P'.toAf x' t hx' P'.self * g) ≠ 0 := by rw [he]; exact hg
    rcases GlobalTheory.LKMid.Pair.c_eq_or_eq_neg p G (Quot.out q₀) P' hγ' with hc | hc
    · exact Or.inl ⟨P', hq', hγ', hc, x', t, hx', g, hg'⟩
    · exact Or.inr ⟨P', hq', hγ', hc, x', t, hx', g, hg'⟩
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne]; exact Set.finite_empty

end GlobalTheory.LKCx.PeriodicClassFixedPoints
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMinpolyDefinitePairsTermNeZeroStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_minpoly_definitePairs_term_ne_zero : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 →
    ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
      (∀ k ∈ L.K.toSubgroup, ∀ k' ∈ L.K.toSubgroup, ∀ g, f (k * g * k') = f g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      (∀ k ∈ K', ∀ k' ∈ K', ∀ g, f' (k * g * k') = f' g) →
      {P0 : Polynomial G.F | ∃ P : GlobalTheory.LKDef.DPair G, P.pol = P0 ∧ Irreducible P.pol ∧
        P.term L.K.toSubgroup f 1 K' f' ≠ 0}.Finite := by
  first | exact @GlobalTheory.LKDef.FinPol.finite_pol_term_ne_zero | exact GlobalTheory.LKDef.FinPol.finite_pol_term_ne_zero | (intros; apply GlobalTheory.LKDef.FinPol.finite_pol_term_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviDecompositionGradedIsotropicFlagStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leviDecomposition_gradedIsotropicFlag : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E) (d : Fin r → ℕ), Formalism.UG.cT (σ : E →+* E) X * J * X = 0 → Formalism.UG.cT (σ : E →+* E) Y * J * Y = 0 → Formalism.UG.cT (σ : E →+* E) X * J * Y = 1 → (∀ p ∈ parFlag σ J X d, ∃ u ∈ unipFlag σ J X d, ∃ m ∈ leviFlag σ J X Y d, p = u * m ∧ (p ∈ ratPts σ J → m ∈ ratPts σ J)) ∧ unipFlag σ J X d ⊓ leviFlag σ J X Y d = ⊥ ∧ leftGrp σ J X d = unipFlag σ J X d ⊔ (ratPts σ J ⊓ leviFlag σ J X Y d) ∧ ∀ (t : Fin r → ℝ) (a : GAd σ J), (∀ i, t i ≠ 0) → IsTorusElt σ J X Y t a → a ∈ leviFlag σ J X Y d := by
  first | exact @GlobalTheory.LeviFlag.levi_decomposition | exact GlobalTheory.LeviFlag.levi_decomposition | (intros; apply GlobalTheory.LeviFlag.levi_decomposition <;> assumption)
end

