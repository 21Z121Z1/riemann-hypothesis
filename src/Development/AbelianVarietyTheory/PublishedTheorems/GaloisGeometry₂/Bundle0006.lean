import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0017
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinGLMemOfPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0129
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.CaraianiAboveLHyp
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CarHyp

open GlobalTheory.TheRec

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}
  [IsAlgClosure E Ω] [IsCMField E]

structure IsAssoc (π : CuspSub E a) (ι : Qbar l ≃+* ℂ) (R : G E Ω →* GL (Fin a) (Qbar l)) : Prop where
  cont : Continuous R
  ss : IsSSRep R
  unr : ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (rc : IrrGL (w.adicCompletion E) → WD h), IsTheRec h rc → ∀ σ σ', π.IsLocComp w σ → SmGL.IsSpherical σ.ρ →
    Nonempty (σ'.ρ.Equiv (SmGL.contra σ.ρ)) → wdOf h hl ι R = rc (algNorm σ')

def IsTheRep (π : CuspSub E a) (ι : Qbar l ≃+* ℂ) (R : G E Ω →* GL (Fin a) (Qbar l)) : Prop :=
  IsAssoc π ι R ∧ ∀ R' : G E Ω →* GL (Fin a) (Qbar l), IsAssoc π ι R' →
    ∃ p : GL (Fin a) (Qbar l), ∀ g, R' g = p * R g * p⁻¹

end GlobalTheory.CarHyp

namespace GlobalTheory.Published

def CaraianiAboveLHyp : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 2 ≤ a →
    ∀ π : CuspSub E a, GlobalTheory.ContraPair.DualIsConj π → GKCoh.IsCohomological π →
    ∀ R : G E Ω →* GL (Fin a) (Qbar l), CarHyp.IsTheRep π ι R →
    ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw),
      IsPstAt P Bw (R.comp (Dec (F := E) A).subtype) →
      ∀ σ σ', π.IsLocComp w σ → Nonempty (σ'.ρ.Equiv (SmGL.contra σ.ρ)) → ∀ rc, TheRec.IsTheRec h rc →
        wdAt P ι Bw h hj (R.comp (Dec (F := E) A).subtype) = rc (algNorm σ')

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.CaraianiLocalGlobal
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Published

def CaraianiLocalGlobal : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 2 ≤ a →
    ∀ π : CuspSub E a, π.IsCsd → GKCoh.IsCohomological π →
    ∃ R : G E Ω →* GL (Fin a) (Qbar l), Continuous R ∧ IsSSRep R ∧
      (∀ (w : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
        (rc : IrrGL (w.adicCompletion E) → WD h), IsRec h rc → ∀ σ, π.IsLocComp w σ → IsWDOf ι R (rc (algNorm σ))) ∧
      ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
        ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
          (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
          (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw),
          IsPstAt P Bw (R.comp (Dec (F := E) A).subtype) ∧ ∀ σ, π.IsLocComp w σ → ∀ rc, IsRec h rc →
            wdAt P ι Bw h hj (R.comp (Dec (F := E) A).subtype) = rc (algNorm σ)

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.CaraianiLocalGlobalDual
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Published

def CaraianiLocalGlobalDual : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 2 ≤ a →
    ∀ π : CuspSub E a, GlobalTheory.ContraPair.DualIsConj π → GKCoh.IsCohomological π →
    ∃ R : G E Ω →* GL (Fin a) (Qbar l), Continuous R ∧ IsSSRep R ∧
      (∀ (w : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
        (rc : IrrGL (w.adicCompletion E) → WD h), IsRec h rc → ∀ σ, π.IsLocComp w σ → IsWDOf ι R (rc (algNorm σ))) ∧
      ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
        ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
          (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
          (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw),
          IsPstAt P Bw (R.comp (Dec (F := E) A).subtype) ∧ ∀ σ, π.IsLocComp w σ → ∀ rc, IsRec h rc →
            wdAt P ι Bw h hj (R.comp (Dec (F := E) A).subtype) = rc (algNorm σ)

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsCohomologicalRankOne
section
noncomputable section

open NumberField Matrix Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh
open scoped TensorProduct

namespace GlobalTheory.RegAlgPurityModel

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem chiInf_eq_prod (χ : HChar E) (n : (E →+* ℂ) → ℤ) (h : ∀ τ, expo χ τ = n τ) (u : (Cinf E)ˣ) :
    ((chiInf χ u : ℂˣ) : ℂ) = ∏ w : InfinitePlace E,
      (coord w.embedding u ^ n w.embedding *
        coord (ComplexEmbedding.conjugate w.embedding) u ^ n (ComplexEmbedding.conjugate w.embedding)) := by
  classical
  obtain ⟨z, rfl⟩ : ∃ z, u = expU z := ⟨_, (expU_log u).symm⟩
  have e : z = ∑ w : InfinitePlace E, atEmb w.embedding (z w) := by
    conv_lhs => rw [← Finset.univ_sum_single z]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp [atEmb]
  have c1 : ∀ w : InfinitePlace E, coord w.embedding z = z w := fun w => by simp [coord]
  have c2 : ∀ w : InfinitePlace E, coord (ComplexEmbedding.conjugate w.embedding) z = starRingEnd ℂ (z w) := fun w => by
    have := (InfType.conj_ne w.embedding).symm
    simp [coord, this]
  rw [chiInf_expU]
  conv_lhs => rw [e, map_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [← chiInf_expU, chiInf_expU_atEmb, InfType.coord_expU, InfType.coord_expU, c1, c2, h, h, Complex.exp_add,
    Complex.exp_int_mul, Complex.exp_int_mul]

omit [NumberField E] [IsTotallyComplex E] in

theorem zpow_mem (τ : E →+* ℂ) (m : ℤ) : (fun y : GL (Fin 1) (Cinf E) => coord τ y.val.det ^ m) ∈ regFun E 1 := by
  have h1 : (fun y : GL (Fin 1) (Cinf E) => coord τ y.val.det) ∈ regFun E 1 :=
    Algebra.subset_adjoin (Or.inl ⟨τ, 0, 0, by simp⟩)
  have h2 : (fun y : GL (Fin 1) (Cinf E) => (coord τ y.val.det)⁻¹) ∈ regFun E 1 :=
    Algebra.subset_adjoin (Or.inr ⟨τ, rfl⟩)
  rcases m with m | m
  · convert pow_mem h1 m using 1
    funext y; simp
  · convert pow_mem h2 (m + 1) using 1
    funext y; simp [zpow_negSucc]

def invRep (χ : HChar E) (n : (E →+* ℂ) → ℤ) (h : ∀ τ, expo χ τ = n τ) : AlgRep E 1 where
  d := 1
  mat := (Matrix.scalar (Fin 1)).toMonoidHom.comp ((Units.coeHom ℂ).comp ((chiDet 1 χ⁻¹).comp (infGL E 1)))
  reg i j := by
    have e : ∀ y : GL (Fin 1) (Cinf E), ((chiDet 1 χ⁻¹ (infGL E 1 y) : ℂˣ) : ℂ) = ∏ w : InfinitePlace E,
      (coord w.embedding y.val.det ^ (-n w.embedding) *
        coord (ComplexEmbedding.conjugate w.embedding) y.val.det ^ (-n (ComplexEmbedding.conjugate w.embedding))) := by
      intro y
      have e1 : chiDet 1 χ⁻¹ (infGL E 1 y) = (chiInf χ (GeneralLinearGroup.det y))⁻¹ :=
        congrArg (fun x => (χ.1 x)⁻¹) (det_infGL y)
      rw [e1, Units.val_inv_eq_inv_val, chiInf_eq_prod χ n h, ← Finset.prod_inv_distrib]
      simp [mul_comm]
    have := Subalgebra.prod_mem (regFun E 1) (t := Finset.univ) fun (w : InfinitePlace E) _ =>
      mul_mem (zpow_mem w.embedding (-n w.embedding)) (zpow_mem (ComplexEmbedding.conjugate w.embedding)
        (-n (ComplexEmbedding.conjugate w.embedding)))
    convert this using 1
    funext y
    rw [Finset.prod_apply]
    simp only [Pi.mul_apply]
    rw [← e, Subsingleton.elim i j]
    simp
  pos := one_pos
  irred W _ := by
    have : IsSimpleModule ℂ (Fin 1 → ℂ) := isSimpleModule_iff_finrank_eq_one.2 (by simp)
    exact eq_bot_or_eq_top W

theorem dchi_inv_add (χ : HChar E) (X : Lie E 1) :
    dchi χ⁻¹ (Matrix.of X).trace + dchi χ (Matrix.of X).trace = 0 := by
  have h := lie_mulChi χ X (mulChi 1 χ⁻¹ (oneFn E 1))
  rw [← mulChi_mul, inv_mul_cancel, mulChi_one, lie_oneFn, lie_mulChi, lie_oneFn, zero_add, map_smul, ← add_smul, map_smul,
    ← mulChi_mul, inv_mul_cancel, mulChi_one] at h
  exact (smul_eq_zero.1 h.symm).resolve_right oneFn_ne_zero

theorem dmat_invRep (χ : HChar E) (n : (E →+* ℂ) → ℤ) (h : ∀ τ, expo χ τ = n τ) (X : Lie E 1) :
    (invRep χ n h).dmat X = Matrix.scalar (Fin 1) (dchi χ⁻¹ (Matrix.of X).trace) := by
  have h1 := congrFun (congrArg Subtype.val (lie_mulChi χ⁻¹ X (oneFn E 1))) 1
  rw [lie_oneFn, zero_add] at h1
  have e : (extGL fun y => (invRep χ n h).mat y (0 : Fin 1) (0 : Fin 1)) = chart (mulChi 1 χ⁻¹ (oneFn E 1)).1 1 := by
    funext x
    unfold extGL chart
    split_ifs with hx
    · change _ = 1 * ((chiDet 1 χ⁻¹ (1 * _) : ℂˣ) : ℂ)
      rw [one_mul, one_mul]
      exact Matrix.diagonal_apply_eq _ (0 : Fin 1)
    · rfl
  ext i j
  obtain rfl : i = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
  obtain rfl : j = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
  change fderiv ℝ (extGL fun y => (invRep χ n h).mat y (0 : Fin 1) (0 : Fin 1)) _ X = _
  rw [e]
  refine h1.trans ?_
  change _ * 1 * ((chiDet 1 χ⁻¹ 1 : ℂˣ) : ℂ) = _
  simp

theorem isCohomological_char (χ : HChar E) (n : (E →+* ℂ) → ℤ) (h : ∀ τ, expo χ τ = n τ) :
    IsCohomological ((CuspSub.triv E le_rfl).twist χ) := by
  have := Submodule.nontrivial_iff_ne_bot.2 ((CuspSub.triv E le_rfl).twist χ).ne_bot
  obtain ⟨φ, hφ⟩ := exists_ne (0 : ((CuspSub.triv E le_rfl).twist χ).V)
  have key : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (v : V), v ⊗ₜ[ℂ] (fun _ : Fin 1 => (1 : ℂ)) = 0 → v = 0 :=
    fun v h => by
      have h1 := congrArg (fun x => TensorProduct.rid ℂ _ (LinearMap.lTensor _ (LinearMap.proj (0 : Fin 1)) x)) h
      simp only [LinearMap.lTensor_tmul, LinearMap.proj_apply, TensorProduct.rid_tmul, one_smul, map_zero] at h1
      exact h1
  have sc : ∀ c : ℂ, Matrix.scalar (Fin 1) c *ᵥ (fun _ : Fin 1 => (1 : ℂ)) = c • (fun _ : Fin 1 => (1 : ℂ)) := by
    intro c; funext i; simp [Matrix.mulVec, dotProduct, Subsingleton.elim i 0]
  refine ⟨invRep χ n h, hasCohomology_of_invariant (m := φ ⊗ₜ fun _ => 1) (fun h => hφ (key φ h)) (fun k => ?_)
    fun X => ?_⟩
  · rw [tensorK, TensorProduct.map_tmul, CuspSub.op_triv_twist, Matrix.toLin'_apply]
    have e := sc ((chiDet 1 χ⁻¹ (infGL E 1 (Unitary.toUnits k)) : ℂˣ) : ℂ)
    refine (congrArg (fun v : Fin 1 → ℂ => _ ⊗ₜ[ℂ] v) e).trans ?_
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_smul]
    have e2 : ((chiDet 1 χ⁻¹ (infGL E 1 (Unitary.toUnits k)) : ℂˣ) : ℂ) *
        (((opMul χ (.cpt k) : ℂˣ) : ℂ) * opTriv (E := E) (.cpt k) + opAdd χ (.cpt k)) = 1 := by
      change (((chiDet 1 χ (infGL E 1 (Unitary.toUnits k)))⁻¹ : ℂˣ) : ℂ) *
        (((chiDet 1 χ (infGL E 1 (Unitary.toUnits k)) : ℂˣ) : ℂ) * 1 + 0) = 1
      simp
    rw [e2, one_smul]
    rfl
  · rw [tensorLie_tmul, CuspSub.op_triv_twist, dmat_invRep]
    refine (congrArg (fun v : Fin 1 → ℂ => _ + φ ⊗ₜ[ℂ] v) (sc _)).trans ?_
    have e2 : (((opMul χ (.lie X) : ℂˣ) : ℂ) * opTriv (E := E) (.lie X) + opAdd χ (.lie X)) =
        -dchi χ⁻¹ (Matrix.of X).trace := by
      change _ * 0 + dchi χ (Matrix.of X).trace = _
      linear_combination dchi_inv_add χ X
    rw [e2, TensorProduct.tmul_smul, TensorProduct.smul_tmul', neg_smul, TensorProduct.neg_tmul]
    exact neg_add_cancel _

theorem isCohomological_rank_one (π : CuspSub E 1) (h : (CG.mk π).IsRegAlg) : IsCohomological π := by
  obtain ⟨χ, rfl⟩ := RankOne.exists_eq_twist π
  choose n hn using (CG.isRegAlg_ofChar χ).1 h
  exact isCohomological_char χ n hn

theorem absPow_model (m : ℤ) :
    let π := (CuspSub.triv E le_rfl).twist (GlobalTheory.HeckeGal.Model.absPow E m)
    (CG.mk π).IsRegAlg ∧ (∀ τ : E →+* ℂ, (CG.mk π).infChar ((starRingEnd ℂ).comp τ) =
      ((CG.mk π).infChar τ).map fun z => ((2 * m : ℤ) : ℂ) - z) ∧ IsCohomological π := by
  intro π
  have h := (InfType.expo_of_infType E _).2.1 m (GlobalTheory.HeckeGal.Model.absPow_isAbsPow E m)
  have hr : (CG.mk π).IsRegAlg := (CG.isRegAlg_ofChar _).2 fun τ => ⟨m, by rw [h]; simp⟩
  refine ⟨hr, fun τ => ?_, isCohomological_rank_one π hr⟩
  change (CG.ofChar _).infChar _ = ((CG.ofChar _).infChar _).map _
  rw [CG.infChar_ofChar, CG.infChar_ofChar, h, h, Multiset.map_singleton]
  congr 1; push_cast; ring

theorem not_isRegAlg_half : ¬ (CG.ofChar (GlobalTheory.HeckeGal.Model.absPow E (1 / 2))).IsRegAlg := by
  intro hr
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  obtain ⟨n, hn⟩ := (CG.isRegAlg_ofChar _).1 hr τ
  rw [(InfType.expo_of_infType E _).2.1 _ (GlobalTheory.HeckeGal.Model.absPow_isAbsPow E _)] at hn
  have h1 : (1 / 2 : ℝ) = n := by exact_mod_cast hn
  have h2 : (1 : ℤ) = 2 * n := by exact_mod_cast (by linarith : (1 : ℝ) = 2 * n)
  omega

theorem exists_gauss : ∃ (_ : IsCMField (CyclotomicField 4 ℚ)) (π : CuspSub (CyclotomicField 4 ℚ) 1),
    (CG.mk π).IsRegAlg ∧ (∀ τ, (CG.mk π).infChar ((starRingEnd ℂ).comp τ) =
      ((CG.mk π).infChar τ).map fun z => ((2 * 1 : ℤ) : ℂ) - z) ∧ IsCohomological π := by
  have : IsCMField (CyclotomicField 4 ℚ) := IsCyclotomicExtension.Rat.isCMField (S := {4}) _ ⟨4, rfl, by norm_num⟩
  exact ⟨this, _, absPow_model 1⟩

end GlobalTheory.RegAlgPurityModel

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.PolarizedGaloisRepPublished
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GalHyps

open GlobalTheory.TheRec

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}
  [IsAlgClosure E Ω] [IsCMField E]

structure Above (π : CuspSub E a) (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l))
    (HT : (E →+* Qbar l) → Multiset ℤ) (P : LocPrime l) {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}
    (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw) : Prop where

  deRham : IsdRAt P Bw (r.comp (Dec (F := E) A).subtype)

  jumps : ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
    IsJumpsAt P Bw (r.comp (Dec (F := E) A).subtype) τ (HT τ)

  iwahori : ∀ σ, π.IsLocComp w σ → PRep.fixed σ.ρ (SmGL.iwahori (w.adicCompletion E) (Fin a)) ≠ ⊥ →
    IsSstAt P Bw (r.comp (Dec (F := E) A).subtype) ∧
      ∀ rc, IsTheRec h rc → wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype) = rc (algNorm σ)

  crys : ∀ σ, π.IsLocComp w σ → SmGL.IsSpherical σ.ρ → IsCrysAt P Bw (r.comp (Dec (F := E) A).subtype)

structure Props (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)) (ι : Qbar l ≃+* ℂ)
    (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ) : Prop where

  cont : Continuous r

  ss : IsSSRep r

  pol : ∀ μ : G (maximalRealSubfield E) Ω →* (Qbar l)ˣ, IsLAdicCharOf ι χ μ → ∀ c : Ω ≃+* Ω, IsCMConjOm E Ω c →
    IsConjDual c r (cycBar E Ω l ^ (1 - (a : ℤ)) * μ.comp (AlgEquiv.restrictScalarsHom (maximalRealSubfield E)))

  away : ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (rc : IrrGL (w.adicCompletion E) → WD h), IsTheRec h rc → ∀ σ, π.IsLocComp w σ → wdOf h hl ι r = rc (algNorm σ)

  pure : ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w),
    ((wdOf h hl ι r).lpTw ((wt : ℝ) / 2)).tempered

  weights : ∀ (τ : E →+* Qbar l) (m : Multiset ℂ), π.HasInfChar (ι.toRingHom.comp τ) m →
    (HT τ).map (fun n : ℤ => (n : ℂ)) = m.map fun z => ((a : ℂ) - 1) / 2 - z

  weights_conj : ∀ τ : E →+* Qbar l,
    HT (τ.comp (IsCMField.complexConj E).toRingEquiv.toRingHom) = (HT τ).map (wt - ·)

  above : ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw), Above π ι r HT P h Bw hj

end GlobalTheory.GalHyps

namespace GlobalTheory.Published

def PolarizedGaloisRepPublished : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.PolarizedPair π χ →
      ∃ (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ),
        GalHyps.Props π χ ι r wt HT

end GlobalTheory.Published

end
end

