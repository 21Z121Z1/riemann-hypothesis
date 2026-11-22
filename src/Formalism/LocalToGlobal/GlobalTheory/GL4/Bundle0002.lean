import Mathlib
import Formalism.LocalToGlobal.LatticeGeometry.GeometryDefinitions.GaloisCuspidalOfInput
import Formalism.LocalToGlobal.LatticeGeometry.GeometryDefinitions.Bundle0001
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ReductionSecondStep
import Formalism.SizeWindowBrackets.ChainSlopeWindows.TruncatedLatticeHolds
import Formalism.SharpRestriction.GlobalSchurBounds.FlipTwoThree
import Formalism.LocalToGlobal.GlobalTheory.GL4.Bundle0001
import Formalism.LocalToGlobal.GlobalTheory.GL4.PLemTLat

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL4.MemDualCrdLat
section
open Module NumberField IsDedekindDomain
open scoped Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.HN Formalism.MainNotions.flipTwoThree Formalism.L2.Herm Formalism.L2.Geo.Def Formalism.L2.Geo.Def.G1
open Formalism.LFunctionChainParameters.slopeLatticeData (FinPl)

def finPlEquiv (K : Type) [Field K] [NumberField K] : FinPl K ≃ HeightOneSpectrum (𝓞 K) where
  toFun := toH
  invFun w := ⟨w.asIdeal, w.isMaximal⟩
  left_inv _ := rfl
  right_inv _ := rfl

section E

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

private lemma hform_crd_lemma (S : HSpace E) (a b : S.V) :
    Formalism.DivisionValues.hform S.gram (crd S a) (crd S b) = S.hT a b := by
  conv_rhs => rw [← S.frame.sum_equivFun a, ← S.frame.sum_equivFun b]
  simp only [Formalism.DivisionValues.hform, Matrix.toLinearMapₛₗ₂'_apply, map_sum, LinearMap.sum_apply,
    LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, crd, HSpace.gram, RingHom.id_apply,
    Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem mem_dual_crdLat (hc : CMData F E) (S : HSpace E) (L : Submodule (𝓞 E) S.V) (x : S.V) :
    crd S x ∈ Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform S.gram) (crdLat S L) ↔ x ∈ dualSub S L := by
  unfold dualSub
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply, Submodule.mem_one, crdLat, Submodule.mem_map,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, LinearEquiv.coe_coe,
    LinearMap.coe_restrictScalars, hform_crd_lemma, Submodule.mem_mk, AddSubmonoid.mem_mk,
    AddSubsemigroup.mem_mk, Set.mem_setOf_eq, RingHom.mem_range]
  exact Iff.rfl

theorem relIndex_crdLat (hc : CMData F E) (S : HSpace E) (L : Submodule (𝓞 E) S.V) :
    (crdLat S L).toAddSubgroup.relIndex (Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform S.gram) (crdLat S L)).toAddSubgroup =
      L.toAddSubgroup.relIndex (dualSub S L) := by
  let f : S.V →+ (Fin S.rank → E) := (crd S).toAddEquiv.toAddMonoidHom
  have hf : Function.Injective f := (crd S).injective
  have hL : (crdLat S L).toAddSubgroup = L.toAddSubgroup.map f := by
    ext z
    exact Iff.rfl
  have hD : (Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform S.gram) (crdLat S L)).toAddSubgroup =
      (dualSub S L).map f := by
    ext z
    obtain ⟨x, rfl⟩ := (crd S).surjective z
    rw [Submodule.mem_toAddSubgroup, mem_dual_crdLat hc S L x]
    constructor
    · intro h
      exact ⟨x, h, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      exact hf hyx ▸ hy
  rw [hD, hL, ← AddSubgroup.relIndex_comap, AddSubgroup.comap_map_eq_self_of_injective hf]

variable [IsTotallyComplex E]

theorem eLat_mu (hc : CMData F E) (S : HSpace E) (hsig : S.SigOK) (hpos : S.IsPosDef) (hn : 0 < S.rank)
    (L : Submodule (𝓞 E) S.V) (hL : Submodule.IsLattice E L) (q : ℕ) (hq : q ≠ 0) (hLT : LatT S q L) :
    muDef (Pi.basisFun E (Fin S.rank)) (fun v => frameOf (S.gram.map v.embedding)) (crdLat S L) =
      -Real.log q / ((finrank ℚ E : ℝ) * S.rank) := by
  have hM := crdLat_lattice S L hL
  have hY : ∀ v : InfinitePlace E, IsUnit (frameOf (S.gram.map v.embedding)).det ∧
      ((frameOf (S.gram.map v.embedding))⁻¹).conjTranspose * (frameOf (S.gram.map v.embedding))⁻¹ = S.gram.map v.embedding := by
    intro v
    apply frameOf_spec
    apply exists_frame_of_sig _ S.rank
    have h1 := hsig v.embedding
    rwa [hpos v.embedding] at h1
  have hCM : Formalism.DivisionValues.IsCMSub (⊤ : Subfield E) := fun σ a _ => hc.cmUnram.2.1 σ a
  have hRat : Formalism.DivisionValues.IsRatHerm (⊤ : Subfield E) S.gram (fun v => frameOf (S.gram.map v.embedding)) :=
    ⟨fun _ _ => Subfield.mem_top _, hY⟩
  obtain ⟨-, h2⟩ := Formalism.DivisionValues.ratHermLcv_of Formalism.DivisionValues.covolume_via_basis Formalism.DivisionValues.index_change_formula
    Formalism.DivisionValues.semilocal_basis_exists E ⊤ hCM S.rank S.gram _ hRat _ hM
  set M := crdLat S L with hMdef
  set Md := Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform S.gram) M with hMd
  have hle : M ≤ Md := by
    intro z hz
    obtain ⟨x, rfl⟩ := (crd S).surjective z
    exact (mem_dual_crdLat hc S L x).2 (hLT.1 x ((crdLat_mem S L x).1 hz))
  have hidx : M.toAddSubgroup.relIndex Md.toAddSubgroup = q := by
    rw [hMd, hMdef, relIndex_crdLat hc S L]; exact hLT.2
  have hjw : ∀ w : HeightOneSpectrum (𝓞 E), (Formalism.DivisionValues.jw S.gram w M : ℝ) = -(Formalism.HermitianLatticesTheory.locLen w.asIdeal Md M : ℝ) := by
    intro w
    unfold Formalism.DivisionValues.jw Formalism.HermitianLatticesTheory.jIdx Formalism.HermitianLatticesTheory.lidx
    rw [← hMd, inf_eq_left.2 hle]
    have h0 : Formalism.HermitianLatticesTheory.locLen w.asIdeal M M = 0 := by
      unfold Formalism.HermitianLatticesTheory.locLen
      rw [Submodule.comap_subtype_self]
      simp
    rw [h0]
    push_cast
    ring
  obtain ⟨-, -, h3⟩ := Formalism.LFunctionChainParameters.LLcv.index_local_length E (Fin S.rank → E) Md M hle (by rw [hidx]; exact hq)
  rw [hidx] at h3
  have hnE : (0 : ℝ) < (finrank ℚ E : ℝ) := by exact_mod_cast (Module.finrank_pos : 0 < finrank ℚ E)
  have h4 : (∑ᶠ w : HeightOneSpectrum (𝓞 E), Formalism.DivisionValues.lw w * (Formalism.DivisionValues.jw S.gram w M : ℝ)) = -(Real.log q / (finrank ℚ E : ℝ)) := by
    rw [h3, ← finsum_comp_equiv (finPlEquiv E), div_eq_mul_inv, ← mul_neg, finsum_mul]
    refine finsum_congr fun p => ?_
    rw [hjw]
    unfold Formalism.DivisionValues.lw
    show Real.log (Ideal.absNorm p.1 : ℝ) / (finrank ℚ E : ℝ) * -(Formalism.HermitianLatticesTheory.locLen (toH p).asIdeal Md M : ℝ) =
      Real.log (Ideal.absNorm p.1 : ℝ) * (Formalism.HermitianLatticesTheory.locLen (toH p).asIdeal Md M : ℝ) * -(finrank ℚ E : ℝ)⁻¹
    ring
  rw [h4, neg_neg] at h2
  have hrk : rkK M = S.rank := by
    show finrank E (Submodule.span E (M : Set (Fin S.rank → E))) = _
    rw [hM.span_eq_top]
    simp
  have h5 := lcv_eq_mu hn _ (fun v => (hY v).1) M hM.fg hrk
  rw [h2] at h5
  have hr : (0 : ℝ) < (S.rank : ℝ) := by exact_mod_cast hn
  field_simp
  field_simp at h5
  linarith

end E

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL4.PLemTSpan
section
noncomputable section

open NumberField Matrix Module
open scoped InnerProductSpace

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality.LT

open Formalism.BasicNotions Formalism.MainNotions.flipTwoThree

variable {E : Type} [Field E] [NumberField E] [StarRing E]

abbrev UU {S : HSpace E} (M : Model S) (L : Submodule (𝓞 E) S.V) {ι : Type} [Fintype ι] (e : Basis ι ℤ L) :
    Submodule ℝ (EuclideanSpace ℝ (Idx S)) :=
  Submodule.span ℝ (Set.range fun i ↦ psi M (e i : S.V))

section U

variable (S : HSpace E) (hσ : ∀ (φ : E →+* ℂ) a, φ (star a) = star (φ a)) (hsig : S.SigOK)
    (hpos : S.IsPosDef) (M : Model S) (L : Submodule (𝓞 E) S.V) {ι : Type} [Fintype ι] [DecidableEq ι]
    (e : Basis ι ℤ L)

def bU : Basis ι ℝ (UU M L e) := Basis.span (psi_e_linInd S hσ hsig hpos M L e)

theorem bU_coe (i : ι) : ((bU S hσ hsig hpos M L e i : UU M L e) : EuclideanSpace ℝ (Idx S)) = psi M (e i : S.V) :=
  by simp [bU, Basis.span_apply]

abbrev abelian₂ : Submodule ℤ (UU M L e) := Submodule.span ℤ (Set.range (bU S hσ hsig hpos M L e))

theorem psi_eq_sum (l : S.V) (hl : l ∈ L) :
    psi M l = ∑ i, (e.repr ⟨l, hl⟩ i) • psi M (e i : S.V) := by
  have h := congrArg (fun t : L ↦ (t : S.V)) (e.sum_repr ⟨l, hl⟩)
  simp only [Submodule.coe_sum] at h
  have h' : ∑ i, (e.repr ⟨l, hl⟩ i) • (e i : S.V) = l :=
    calc ∑ i, (e.repr ⟨l, hl⟩ i) • (e i : S.V) = ∑ i, ((e.repr ⟨l, hl⟩ i • e i : L) : S.V) :=
          Finset.sum_congr rfl fun i _ ↦ by simp
      _ = l := h
  conv_lhs => rw [← h']
  exact psi_sum_int M L e _

theorem psi_mem_U (l : S.V) (hl : l ∈ L) : psi M l ∈ UU M L e := by
  rw [psi_eq_sum S M L e l hl]
  exact Submodule.sum_mem _ fun i _ ↦ zsmul_mem (Submodule.subset_span (Set.mem_range_self i)) _

theorem mem_Lam_of (l : S.V) (hl : l ∈ L) :
    (⟨psi M l, psi_mem_U S M L e l hl⟩ : UU M L e) ∈ abelian₂ S hσ hsig hpos M L e := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine ⟨fun i ↦ e.repr ⟨l, hl⟩ i, Subtype.ext ?_⟩
  simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, bU_coe]
  rw [psi_eq_sum S M L e l hl]

theorem exists_of_mem_Lam (u : UU M L e) (hu : u ∈ abelian₂ S hσ hsig hpos M L e) :
    ∃ l ∈ L, (u : EuclideanSpace ℝ (Idx S)) = psi M l := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hu
  refine ⟨∑ i, c i • (e i : S.V), Submodule.sum_mem _ fun i _ ↦ zsmul_mem (e i).2 _, ?_⟩
  rw [psi_sum_int M L e, ← hc]
  simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, bU_coe]

theorem dual_vector_of_integral_pairing (y : UU M L e) (hy0 : y ≠ 0)
    (hy : ∀ x ∈ abelian₂ S hσ hsig hpos M L e, ∃ n : ℤ, ⟪x, y⟫_ℝ = (n : ℝ)) :
    ∃ z : S.V, TrDual S L z ∧ z ≠ 0 ∧ (y : EuclideanSpace ℝ (Idx S)) = psi M z := by
  set b := bU S hσ hsig hpos M L e with hb
  have hbmem : ∀ j, b j ∈ abelian₂ S hσ hsig hpos M L e := fun j ↦ Submodule.subset_span ⟨j, rfl⟩
  choose n hn using fun j ↦ hy (b j) (hbmem j)
  set c : ι → ℝ := fun i ↦ b.repr y i with hc
  have hyc : (y : EuclideanSpace ℝ (Idx S)) = ∑ i, c i • psi M (e i : S.V) := by
    have := congrArg (fun t : UU M L e ↦ (t : EuclideanSpace ℝ (Idx S))) (b.sum_repr y)
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, hb, bU_coe] at this
    rw [← this]
  have hGc : (GR S L e) *ᵥ c = fun j ↦ (n j : ℝ) := by
    ext j
    rw [← hn j]
    change _ = ⟪(b j : EuclideanSpace ℝ (Idx S)), (y : EuclideanSpace ℝ (Idx S))⟫_ℝ
    rw [hyc, inner_sum, hb, bU_coe]
    simp only [real_inner_smul_right, inner_e hσ M L e, Matrix.mulVec, dotProduct, GR_apply]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  set c' : ι → ℚ := (GQ S L e)⁻¹ *ᵥ fun j ↦ (n j : ℚ) with hc'
  have hdet := GQ_det S hσ hsig hpos M L e
  have hGc' : (GQ S L e) *ᵥ c' = fun j ↦ (n j : ℚ) := by
    rw [hc', Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet), Matrix.one_mulVec]
  have hGR' : (GR S L e) *ᵥ (fun i ↦ (c' i : ℝ)) = fun j ↦ (n j : ℝ) := by
    ext j
    have := RingHom.map_mulVec (Rat.castHom ℝ) (GQ S L e) c' j
    rw [hGc'] at this
    simpa [GR, Function.comp_def] using this.symm
  have hcc : c = fun i ↦ (c' i : ℝ) := by
    have h0 : (GR S L e) *ᵥ (c - fun i ↦ (c' i : ℝ)) = 0 := by
      rw [Matrix.mulVec_sub, hGc, hGR', sub_self]
    exact sub_eq_zero.1 (Matrix.eq_zero_of_mulVec_eq_zero (GR_det S hσ hsig hpos M L e) h0)
  set z : S.V := ∑ i, (c' i : E) • (e i : S.V) with hz
  have hyz : (y : EuclideanSpace ℝ (Idx S)) = psi M z := by
    rw [hyc, hz, psi_sum_rat M L e, hcc]
  refine ⟨z, ?_, ?_, hyz⟩
  · intro l hl
    obtain ⟨m, hm⟩ := hy _ (mem_Lam_of S hσ hsig hpos M L e l hl)
    have h1 : ⟪psi M l, psi M z⟫_ℝ = (m : ℝ) := by
      rw [← hyz]; exact hm
    rw [inner_psi hσ, trR_eq] at h1
    refine ⟨m, ?_⟩
    have : ((Algebra.trace ℚ E (S.hT l z) : ℚ) : ℝ) = ((m : ℚ) : ℝ) := by rw [h1]; simp
    rw [eq_intCast]
    exact_mod_cast this.symm
  · intro h0
    apply hy0
    apply Subtype.ext
    rw [hyz, h0, map_zero]
    rfl

end U

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality.LT
end
end

