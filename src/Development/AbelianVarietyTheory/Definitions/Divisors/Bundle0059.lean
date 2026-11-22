import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1557
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1515
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1544
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1552
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Definitions.Divisors.CompEqOneIffPush
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.DetNeZeroOfIsWittBasis
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open Formalism.UG (cT)

namespace GlobalTheory.SWInt

open GlobalTheory.SWLit GlobalTheory.SWWeil

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E}

def blockColumnMatrix {R : Type} {k : ℕ} (a b : Matrix (Fin n) (Fin k) R) : Matrix (Fin (n + n)) (Fin k) R :=
  (Matrix.fromRows a b).submatrix finSumFinEquiv.symm id

omit [NumberField E] in

theorem mem_unipN_iff (g : UA σ J₂) : g ∈ unipN σ J₂ ↔ (mat g - 1) * blockColumnMatrix (1 : Matrix (Fin n) (Fin n) (AE F E)) 1 = 0 := by
  have e : ∀ i j, (mat g * blockColumnMatrix (1 : Matrix (Fin n) (Fin n) (AE F E)) 1) i j =
      mat g i (finSumFinEquiv (.inl j)) + mat g i (finSumFinEquiv (.inr j)) := fun i j => by
    rw [Matrix.mul_apply, ← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
    simp only [blockColumnMatrix, Matrix.submatrix_apply, Equiv.symm_apply_apply, id]
    simp [Matrix.one_apply]
  rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero, mem_unipOf, mem_siegelOf, keepsDiag_iff]
  constructor
  · rintro ⟨h1, h2⟩
    ext i j
    have h3 : ∀ i, mat g (finSumFinEquiv (.inl i)) (finSumFinEquiv (.inl j)) +
      mat g (finSumFinEquiv (.inl i)) (finSumFinEquiv (.inr j)) = (1 : Matrix (Fin n) (Fin n) (AE F E)) i j :=
      fun i => congrFun (congrFun h2 i) j
    obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective i <;> rw [e] <;>
      simp only [blockColumnMatrix, Matrix.submatrix_apply, Equiv.symm_apply_apply, id]
    · exact h3 i
    · exact (h1 i j).trans (h3 i)
  · intro h
    have h3 : ∀ i j, mat g (finSumFinEquiv i) (finSumFinEquiv (.inl j)) +
      mat g (finSumFinEquiv i) (finSumFinEquiv (.inr j)) = Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) 1 i j :=
      fun i j => by
        rw [← e, h]
        simp only [blockColumnMatrix, Matrix.submatrix_apply, Equiv.symm_apply_apply, id]
    exact ⟨fun i j => (h3 (.inr i) j).trans (h3 (.inl i) j).symm, Matrix.ext fun i j => h3 (.inl i) j⟩

theorem cocompact_unipN (hcm : IsCMExt F E σ) {J : Matrix (Fin n) (Fin n) E} {l : E} (hl : l ≠ 0)
    (hJ : ∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) (hdet : J.det ≠ 0) (h₂ : J₂ = dblGram finSumFinEquiv J) :
    LocallyCompactSpace (unipN σ J₂) ∧
      ∃ C : Set (unipN σ J₂), IsCompact C ∧ ∀ g : unipN σ J₂, ∃ γ : ratN σ J₂, γ • g ∈ C := by
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.SiegelSet.sigma_sigma hcm
  obtain ⟨δ, hδ, hδs⟩ := GlobalTheory.CMImag.exists_imag_ne_zero F E σ hcm
  have hc : δ * σ l⁻¹ ≠ 0 := mul_ne_zero hδ ((map_ne_zero σ).2 (inv_ne_zero hl))
  set c := δ * σ l⁻¹ with hcd
  set H : Matrix (Fin n) (Fin n) E := c • J.map σ with hH
  have hHd : H.det ≠ 0 := by
    rw [hH, Matrix.det_smul]
    refine mul_ne_zero (pow_ne_zero _ hc) ?_
    rw [show (J.map σ).det = σ J.det from ((σ : E →+* E).map_det J).symm]
    exact (map_ne_zero σ).2 hdet
  have hHh : ∀ i j, σ (H j i) = H i j := fun i j => by
    have h := congrArg σ (hJ i j)
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul, map_neg, hσ] at h
    simp only [hH, hcd, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, hσ, hδs]
    linear_combination (-δ) * h
  have hG : c • J₂.map σ = dblGram finSumFinEquiv H := by
    rw [h₂, dblGram, dblGram, blkMat_map _ _ (map_zero σ), Matrix.map_neg _ (map_neg σ), hH]
    change (c • Matrix.fromBlocks (J.map σ) 0 0 (-J.map σ)).submatrix _ _ = _
    rw [Matrix.fromBlocks_smul, smul_zero, smul_neg, blkMat]
  have hN : IsHermND σ (c • J₂.map σ) := by
    rw [hG]
    refine ⟨fun i j => ?_, ?_⟩
    · obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective i <;> obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective j <;>
        simp only [dblGram, blkMat, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁,
          Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, map_zero,
          Matrix.neg_apply, map_neg, hHh]
    · rw [dblGram, det_blkMat, Matrix.det_neg]
      exact mul_ne_zero hHd (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) hHd)
  let C : Matrix (Fin (n + n)) (Fin n) E := blockColumnMatrix 1 1
  let D : Matrix (Fin (n + n)) (Fin n) E := blockColumnMatrix H⁻¹ 0
  have hi : H * H⁻¹ = 1 := Matrix.mul_nonsing_inv _ (IsUnit.mk0 _ hHd)
  have hi' : H⁻¹ * H = 1 := mul_eq_one_comm.1 hi
  have hCJ : cT (σ : E →+* E) C * (c • J₂.map σ) = (Matrix.fromCols H (-H)).submatrix id finSumFinEquiv.symm := by
    have : cT (σ : E →+* E) C = (Matrix.fromCols 1 1).submatrix id finSumFinEquiv.symm := by
      ext i j
      obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective j <;>
        simp only [C, cT, blockColumnMatrix, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
          id, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr,
          Matrix.one_apply, apply_ite (σ : E →+* E), map_one, map_zero, eq_comm (a := i)]
    rw [this, hG, dblGram, blkMat, Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromBlocks]
    simp
  have xy : cT (σ : E →+* E) C * (c • J₂.map σ) * D = 1 := by
    rw [hCJ]
    simp only [D, blockColumnMatrix]
    rw [Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromRows, hi]
    simp
  have xx : cT (σ : E →+* E) C * (c • J₂.map σ) * C = 0 := by
    rw [hCJ]
    simp only [C, blockColumnMatrix]
    rw [Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromRows]
    simp
  have hP : 1 - D * (cT (σ : E →+* E) C * (c • J₂.map σ)) =
      C * ((Matrix.fromCols (0 : Matrix (Fin n) (Fin n) E) (1 : Matrix (Fin n) (Fin n) E)).submatrix id finSumFinEquiv.symm :
        Matrix (Fin n) (Fin (n + n)) E) := by
    rw [hCJ]
    simp only [C, D, blockColumnMatrix]
    rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id,
      Matrix.fromRows_mul_fromCols, Matrix.fromRows_mul_fromCols, ← Matrix.submatrix_one_equiv finSumFinEquiv.symm,
      ← Matrix.fromBlocks_one]
    ext i j
    obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective i <;> obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective j <;>
      simp only [Matrix.sub_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply] <;> simp [hi']
  have hC : GlobalTheory.UAut.IsIsoCols σ (c • J₂.map σ) C := by
    refine ⟨Matrix.mulVec_injective_iff.1 fun x y h => funext fun i => ?_, xx⟩
    have := congrFun h (finSumFinEquiv (.inl i))
    simpa only [C, blockColumnMatrix, Matrix.submatrix_mulVec_equiv, Matrix.mulVec, Matrix.submatrix_apply, Equiv.symm_apply_apply, id,
      Matrix.fromRows_apply_inl, Matrix.one_apply, dotProduct, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true] using this
  have hCa : GlobalTheory.SiegelSet.adMat F C = blockColumnMatrix (1 : Matrix (Fin n) (Fin n) (AE F E)) 1 := by
    simp only [C, blockColumnMatrix, GlobalTheory.SiegelSet.adMat, ← Matrix.submatrix_map, Matrix.fromRows_map,
      Matrix.map_one _ (map_zero _) (map_one _)]
  set e := GlobalTheory.ThK.SquareIntegrability.toGAd hσ J₂ hc with he
  have hmem : ∀ g : UA σ J₂, g ∈ unipN σ J₂ ↔ e g ∈ GlobalTheory.SiegelSet.unipRad σ (c • J₂.map σ) C := fun g => by
    rw [mem_unipN_iff, GlobalTheory.EisCT.mem_unipRad_iff_dual xy, hP, ← hCa]
    refine ⟨fun h => ⟨h, 0, ?_⟩, fun h => h.1⟩
    rw [GlobalTheory.SiegelSet.adMat, Matrix.map_mul, ← Matrix.mul_assoc, Matrix.mul_zero]
    exact (congrArg (· * _) h).trans (Matrix.zero_mul _)
  have hrat := GlobalTheory.RatCorr.ratU_iff_ratPts F E σ hσ _ J₂ c hc
  haveI := GlobalTheory.UAut.locallyCompact_unipRad hcm hN hC
  obtain ⟨K', hK', hcov'⟩ := GlobalTheory.UAut.cocompact_unipRad hcm hN hC
  have hec : Continuous e := continuous_subtype_val.subtype_mk _
  have hes : Continuous e.symm := continuous_subtype_val.subtype_mk _
  let eH : unipN σ J₂ ≃ₜ GlobalTheory.SiegelSet.unipRad σ (c • J₂.map σ) C :=
    { toFun := fun x => ⟨e x, (hmem x).1 x.2⟩
      invFun := fun y => ⟨e.symm y, (hmem _).2 (by rw [e.apply_symm_apply]; exact y.2)⟩
      left_inv := fun x => by ext; simp
      right_inv := fun y => by ext; simp
      continuous_toFun := (hec.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (hes.comp continuous_subtype_val).subtype_mk _ }
  refine ⟨eH.isClosedEmbedding.locallyCompactSpace, eH ⁻¹' K', eH.isCompact_preimage.2 hK', fun g => ?_⟩
  obtain ⟨γ', hγ', hK⟩ := hcov' (eH g)
  refine ⟨⟨eH.symm γ', ?_⟩, ?_⟩
  · show e.symm (γ' : _) ∈ ratU σ J₂
    rw [hrat, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_subgroupOf.1 hγ'
  · show eH (eH.symm γ' * g) ∈ K'
    have : eH (eH.symm γ' * g) = γ' * eH g := by
      apply Subtype.ext
      show e (e.symm (γ' : _) * (g : _)) = (γ' : _) * e g
      rw [map_mul, MulEquiv.apply_symm_apply]
    rw [this]
    exact hK

theorem existsUnique_isNormN (hcm : IsCMExt F E σ) {J : Matrix (Fin n) (Fin n) E} {l : E} (hl : l ≠ 0)
    (hJ : ∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) (hdet : J.det ≠ 0) (h₂ : J₂ = dblGram finSumFinEquiv J) :
    ∃! νN : Measure (unipN σ J₂), IsNormN σ νN := by
  obtain ⟨hLC, C, hC, hcov⟩ := cocompact_unipN hcm hl hJ hdet h₂
  obtain ⟨hTG, -, hSC, hT2⟩ := GlobalTheory.UnipMass.topUA σ J₂
  haveI : BorelSpace (UA σ J₂) := ⟨rfl⟩
  haveI : Countable (ratN σ J₂) := GlobalTheory.UnipMass.countable_ratU' σ J₂ (unipN σ J₂)
  haveI : DiscreteTopology (ratN σ J₂) := GlobalTheory.T.discrete_rational_points_subgroup F E σ _ J₂ (unipN σ J₂)
  obtain ⟨ν, 𝓓, h1, h2, h3⟩ := GlobalTheory.T.cocompact_lattice_unit_covolume _ (ratN σ J₂) C hC hcov
  refine ⟨ν, ⟨h1, 𝓓, h2, h3⟩, ?_⟩
  rintro ν' ⟨h1', 𝓓', h2', h3'⟩
  have e := Measure.isMulLeftInvariant_eq_smul ν' ν
  haveI : MeasurableConstSMul (ratN σ J₂) (unipN σ J₂) :=
    ⟨fun γ => (continuous_const.mul continuous_id : Continuous fun x : unipN σ J₂ => (γ : unipN σ J₂) * x).measurable⟩
  haveI : SMulInvariantMeasure (ratN σ J₂) (unipN σ J₂) ν' := ⟨fun γ A _ => measure_preimage_mul ν' (γ : unipN σ J₂) A⟩
  have h4 : IsFundamentalDomain (ratN σ J₂) 𝓓 ν' := h2.mono (by rw [e]; exact Measure.smul_absolutelyContinuous)
  have h5 : ν' 𝓓 = 1 := (h4.measure_eq h2').trans h3'
  rw [e, Measure.smul_apply, h3, ENNReal.smul_def, smul_eq_mul, mul_one, ENNReal.coe_eq_one] at h5
  rw [e, h5, one_smul]

end GlobalTheory.SWInt

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.KottwitzDimSignatureOneOne
section
noncomputable section

namespace GlobalTheory.UPel.Sm.Model

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel

section Univ
variable {F : Type} [Field F] [NumberField F] [IsCMField F] {D : Datum F} {p N : ℕ}

theorem infUniv_of_rep {X : Scheme.{0}} {s : X ⟶ Sp (D.OEp p)} (univ : Obj D p N s)
    (h : ∀ (S : Scheme.{0}) (s' : S ⟶ Sp (D.OEp p)) (o : Obj D p N s'),
      ∃! f : S ⟶ X, f ≫ s = s' ∧ Nonempty (ObjMap o univ f)) : InfUniv univ := by
  intro C C₀ _ _ _ _ π _ _ t o o₀ x₀ hx₀ ⟨m⟩ h₀
  obtain ⟨x, ⟨hx, ⟨mx⟩⟩, hu⟩ := h _ t o
  obtain ⟨y, -, hy⟩ := h _ _ o₀
  refine ⟨x, ⟨?_, hx, ⟨mx⟩⟩, fun x' h' => hu x' h'.2⟩
  exact (hy _ ⟨by rw [Category.assoc, hx], ⟨m.comp mx⟩⟩).trans (hy _ ⟨hx₀, h₀⟩).symm

theorem InfUniv.lift_point {X : Scheme.{0}} {s : X ⟶ Sp (D.OEp p)} {univ : Obj D p N s} (h : InfUniv univ)
    (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀)
    (hπ : Function.Surjective π) (hsq : RingHom.ker π ^ 2 = ⊥) (t : Sp C ⟶ Sp (D.OEp p))
    (hl : ∀ o₀ : Obj D p N (spMap π ≫ t), ∃ o : Obj D p N t, Nonempty (ObjMap o₀ o (spMap π)))
    (x₀ : Sp C₀ ⟶ X) (hx₀ : x₀ ≫ s = spMap π ≫ t) : ∃ x : Sp C ⟶ X, spMap π ≫ x = x₀ ∧ x ≫ s = t := by
  have : ∃ o₀ : Obj D p N (spMap π ≫ t), Nonempty (ObjMap o₀ univ x₀) :=
    hx₀ ▸ Pull.exists_objMap F D p N _ _ s univ x₀
  obtain ⟨o₀, h₀⟩ := this
  obtain ⟨o, ho⟩ := hl o₀
  obtain ⟨x, hx, -⟩ := h C C₀ π hπ hsq t o o₀ x₀ hx₀ ho h₀
  exact ⟨x, hx.1, hx.2.1⟩

theorem not_infUniv_const {k : Type} [Field k] {b : Sp k ⟶ Sp (D.OEp p)} (o : Obj D p N b)
    (u : Obj D p N (spMap (algebraMap k (DualNumber k)) ≫ b))
    (m : ObjMap u o (spMap (algebraMap k (DualNumber k)))) : ¬ InfUniv u := by
  intro h
  let π : DualNumber k →+* k := (TrivSqZeroExt.fstHom k k k).toRingHom
  let j : k →+* DualNumber k := algebraMap k (DualNumber k)
  haveI : IsArtinianRing (DualNumber k) :=
    haveI : Module.Finite k (DualNumber k) := inferInstanceAs (Module.Finite k (k × k))
    IsArtinianRing.of_finite k _
  have hs : Function.Surjective π := fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  have hsq : RingHom.ker π ^ 2 = ⊥ := by
    rw [pow_two, eq_bot_iff, Ideal.mul_le]
    intro a ha c hc
    have ha' : a.fst = 0 := ha
    have hc' : c.fst = 0 := hc
    rw [Ideal.mem_bot]
    ext <;> simp [ha', hc']
  have e1 : spMap π ≫ spMap j = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]; rfl
  obtain ⟨o₀, h₀⟩ := Pull.exists_objMap F D p N _ _ _ u (spMap π)
  obtain ⟨x, -, hu⟩ := h (DualNumber k) k π hs hsq _ u o₀ (spMap π) rfl h₀ h₀
  have e2 : (spMap j ≫ spMap π) ≫ spMap j = spMap j := by rw [Category.assoc, e1, Category.comp_id]
  have a1 := hu (𝟙 _) ⟨Category.comp_id _, Category.id_comp _, ⟨ObjMap.refl u⟩⟩
  have a2 := hu (spMap j ≫ spMap π) ⟨by rw [← Category.assoc, e1, Category.id_comp],
    by rw [← Category.assoc, e2], objMap_cancel F D p N _ _ _ _ _ _ u u o _ _ m (e2.symm ▸ m)⟩
  have a3 : 𝟙 _ = spMap j ≫ spMap π := a1.trans a2.symm
  rw [← Spec.map_comp, ← Spec.map_id] at a3
  have a4 := congrArg (fun f => (CommRingCat.Hom.hom f DualNumber.eps : DualNumber k).snd) (Spec.map_injective a3)
  simp [π, j] at a4

theorem exists_not_infUniv : ∃ (D : Datum HostModel.E21) (p : ℕ), Good HostModel.E21 p 5 ∧
    ∃ (s : Sp (DualNumber ℂ) ⟶ Sp (D.OEp p)) (u : Obj D p 5 s), ¬ InfUniv u := by
  obtain ⟨D, p, -, -, hg, o, -⟩ := exists_datum_good_obj
  obtain ⟨u, ⟨m⟩⟩ := Pull.exists_objMap _ D p 5 _ _ _ o (spMap (algebraMap ℂ (DualNumber ℂ)))
  exact ⟨D, p, hg, _, u, not_infUniv_const o u m⟩

end Univ

section KS
variable {k H O : Type*} [Field k] [AddCommGroup H] [Module k H] [Ring O]
  {ρ : O →+* Module.End k H} {φ : LinearMap.BilinForm k H} {Fil Z : Submodule k H}

def ksSub (ρ : O →+* Module.End k H) (φ : LinearMap.BilinForm k H) (Fil Z : Submodule k H) :
    Submodule k (H →ₗ[k] H) where
  carrier := {f | IsKS ρ φ Fil Z f}
  zero_mem' := ⟨by simp, by simp, by simp⟩
  add_mem' {f g} hf hg := ⟨fun a x hx => by
      convert add_mem (hf.1 a x hx) (hg.1 a x hx) using 1
      simp only [LinearMap.add_apply, map_add]; abel,
    fun x hx => add_mem (hf.2.1 x hx) (hg.2.1 x hx), fun x hx y hy => by
      have h1 := hf.2.2 x hx y hy
      have h2 := hg.2.2 x hx y hy
      simp only [LinearMap.add_apply, map_add]
      linear_combination h1 + h2⟩
  smul_mem' c f hf := ⟨fun a x hx => by
      convert Fil.smul_mem c (hf.1 a x hx) using 1
      simp only [LinearMap.smul_apply, map_smul, smul_sub],
    fun x hx => Fil.smul_mem c (hf.2.1 x hx), fun x hx y hy => by
      have h1 := hf.2.2 x hx y hy
      simp only [LinearMap.smul_apply, map_smul, smul_eq_mul]
      linear_combination c * h1⟩

def cls (Fil : Submodule k H) : (H →ₗ[k] H) →ₗ[k] (Fil →ₗ[k] H ⧸ Fil) where
  toFun f := Fil.mkQ ∘ₗ f ∘ₗ Fil.subtype
  map_add' f g := by ext; simp
  map_smul' c f := by ext; simp

theorem cls_eq_iff (f g : H →ₗ[k] H) : cls Fil f = cls Fil g ↔ ∀ x ∈ Fil, f x - g x ∈ Fil := by
  simp [cls, LinearMap.ext_iff, Submodule.Quotient.eq]

theorem KSDim.rank_eq {d : ℕ} (h : KSDim ρ φ Fil Z d) :
    Module.rank k ((ksSub ρ φ Fil Z).map (cls Fil)) = d := by
  obtain ⟨f, hf, hu⟩ := h
  have key : ∀ (g : H →ₗ[k] H) (c : Fin d → k), (∀ x ∈ Fil, g x - ∑ i, c i • f i x ∈ Fil) ↔
      cls Fil g = ∑ i, c i • cls Fil (f i) := fun g c => by
    simp only [← map_smul, ← map_sum, cls_eq_iff, LinearMap.sum_apply, LinearMap.smul_apply]
  have li : LinearIndependent k fun i => cls Fil (f i) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    obtain ⟨c₀, -, h₀⟩ := hu 0 (ksSub ρ φ Fil Z).zero_mem
    have := (h₀ c ((key 0 c).2 (by rw [hc, map_zero]))).trans (h₀ 0 ((key 0 0).2 (by simp))).symm
    exact congrFun this
  have : (ksSub ρ φ Fil Z).map (cls Fil) = Submodule.span k (Set.range fun i => cls Fil (f i)) := by
    apply le_antisymm
    · rintro _ ⟨g, hg, rfl⟩
      obtain ⟨c, hc, -⟩ := hu g hg
      rw [(key g c).1 hc]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨f i, hf i, rfl⟩
  rw [this, rank_span li, ← Cardinal.lift_inj.{_, 0}, Cardinal.mk_range_eq_of_injective li.injective]
  simp

theorem KSDim.unique {d e : ℕ} (h : KSDim ρ φ Fil Z d) (h' : KSDim ρ φ Fil Z e) : d = e := by
  exact_mod_cast (KSDim.rank_eq h).symm.trans (KSDim.rank_eq h')

end KS

section Examples
variable (k : Type) [Field k]

def ω₂ : LinearMap.BilinForm k (k × k) :=
  LinearMap.mk₂ k (fun x y => x.1 * y.2 - x.2 * y.1) (by intros; simp; ring) (by intros; simp; ring)
    (by intros; simp; ring) (by intros; simp; ring)

def L₁ : Submodule k (k × k) := LinearMap.ker (LinearMap.snd k k k)

theorem mem_L₁ (x : k × k) : x ∈ L₁ k ↔ x.2 = 0 := Iff.rfl

theorem ksDim_plane : KSDim (Int.castRingHom (Module.End k (k × k))) (ω₂ k) (L₁ k) ⊥ 1 := by
  refine ⟨fun _ => LinearMap.inr k k k ∘ₗ LinearMap.fst k k k, fun _ => ⟨?_, ?_, ?_⟩, fun g _ => ?_⟩
  · intro a x _; simp [mem_L₁]
  · intro x hx; simp [(Submodule.mem_bot k).1 hx, mem_L₁]
  · rintro ⟨a, b⟩ hx ⟨c, d⟩ hy
    rw [mem_L₁] at hx hy; simp at hx hy; simp [ω₂, hx, hy, mul_comm]
  · refine ⟨fun _ => (g (1, 0)).2, ?_, fun c hc => ?_⟩
    · rintro ⟨a, b⟩ hx
      rw [mem_L₁] at hx; simp at hx; subst hx
      have : ((a, 0) : k × k) = a • (1, 0) := by simp
      rw [mem_L₁, this, map_smul]; simp; ring
    · have := hc (1, 0) rfl
      rw [mem_L₁] at this
      funext i
      obtain rfl : i = 0 := Subsingleton.elim _ _
      simp at this
      exact (sub_eq_zero.1 this).symm

theorem ksDim_plane_fixed : KSDim (Int.castRingHom (Module.End k (k × k))) (ω₂ k) (L₁ k) (L₁ k) 0 :=
  ⟨Fin.elim0, fun i => i.elim0, fun g hg => ⟨Fin.elim0, fun x hx => by simpa using hg.2.1 x hx,
    fun _ _ => Subsingleton.elim _ _⟩⟩

def diag : (k × k) →+* Module.End k (k × k) := (Algebra.lmul k (k × k)).toRingHom

theorem ksDim_plane_cm : KSDim (diag k) (ω₂ k) (L₁ k) ⊥ 0 := by
  refine ⟨Fin.elim0, fun i => i.elim0, fun g hg => ⟨Fin.elim0, fun x hx => ?_, fun _ _ => Subsingleton.elim _ _⟩⟩
  have := hg.1 (1, 0) x hx
  obtain ⟨a, b⟩ := x
  rw [mem_L₁] at hx; simp at hx; subst hx
  rw [mem_L₁] at this ⊢
  simpa [diag] using this

theorem not_ksDim_plane_zero : ¬ KSDim (Int.castRingHom (Module.End k (k × k))) (ω₂ k) (L₁ k) ⊥ 0 :=
  fun h => absurd (KSDim.unique h (ksDim_plane k)) (by norm_num)

def ω₄ : LinearMap.BilinForm k (Fin 4 → k) :=
  LinearMap.mk₂ k (fun x y => x 0 * y 2 + x 1 * y 3 - x 2 * y 0 - x 3 * y 1) (by intros; simp; ring)
    (by intros; simp; ring) (by intros; simp; ring) (by intros; simp; ring)

def act₄ : (k × k) →+* Module.End k (Fin 4 → k) :=
  (Algebra.lmul k (Fin 4 → k)).toRingHom.comp
    (RingHom.pi ![RingHom.fst k k, RingHom.fst k k, RingHom.snd k k, RingHom.snd k k])

def F₄ : Submodule k (Fin 4 → k) := LinearMap.ker (LinearMap.proj 1) ⊓ LinearMap.ker (LinearMap.proj 2)

theorem mem_F₄ (x : Fin 4 → k) : x ∈ F₄ k ↔ x 1 = 0 ∧ x 2 = 0 := Iff.rfl

theorem act₄_apply (a : k × k) (x : Fin 4 → k) : act₄ k a x = ![a.1 * x 0, a.1 * x 1, a.2 * x 2, a.2 * x 3] := by
  funext i; fin_cases i <;> rfl

theorem kottwitzDim_signatureOneOne : KSDim (act₄ k) (ω₄ k) (F₄ k) ⊥ 1 := by
  let f : (Fin 4 → k) →ₗ[k] (Fin 4 → k) :=
    LinearMap.pi ![0, LinearMap.proj 0, -LinearMap.proj 3, 0]
  have hf : ∀ x, f x = ![0, x 0, -x 3, 0] := fun x => by funext i; fin_cases i <;> rfl
  refine ⟨fun _ => f, fun _ => ⟨?_, ?_, ?_⟩, fun g hg => ?_⟩
  · intro a x _; simp [mem_F₄, hf, act₄_apply]
  · intro x hx; simp [(Submodule.mem_bot k).1 hx]
  · intro x hx y hy
    rw [mem_F₄] at hx hy; simp [ω₄, hf, hx, hy, mul_comm]
  · let e : Fin 4 → k := ![1, 0, 0, 0]
    let e' : Fin 4 → k := ![0, 0, 0, 1]
    have he : e ∈ F₄ k := ⟨rfl, rfl⟩
    have he' : e' ∈ F₄ k := ⟨rfl, rfl⟩
    have h1 := hg.1 (1, 0) e he
    have h2 := hg.1 (0, 1) e' he'
    have h3 := hg.2.2 e he e' he'
    have a1 : act₄ k (1, 0) e = e := by simp [act₄_apply, e]
    have a2 : act₄ k (0, 1) e' = e' := by simp [act₄_apply, e']
    rw [a1, mem_F₄] at h1
    rw [a2, mem_F₄] at h2
    simp [act₄_apply] at h1 h2
    have h3' : g e 1 + g e' 2 = 0 := by simpa [ω₄, e, e'] using h3
    refine ⟨fun _ => g e 1, fun x hx => ?_, fun c hc => ?_⟩
    · have : x = x 0 • e + x 3 • e' := by
        funext i; fin_cases i <;> simp [e, e', hx.1, hx.2, ((mem_F₄ k x).1 hx).1, ((mem_F₄ k x).1 hx).2]
      have hgx : g x = x 0 • g e + x 3 • g e' := by conv_lhs => rw [this, map_add, map_smul, map_smul]
      rw [mem_F₄, hgx]
      simp [hf, h1, h2]
      constructor
      · ring
      · linear_combination x 3 * h3'
    · have := (hc e he).1
      funext i
      obtain rfl : i = 0 := Subsingleton.elim _ _
      simp [hf, e] at this
      exact (sub_eq_zero.1 this).symm

end Examples

end GlobalTheory.UPel.Sm.Model
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.Subsingleton
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField

namespace GlobalTheory.IwLevel

open GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {S S' : Scheme.{0}}

def htAct {s : S ⟶ Sp R} (o : Obj b N s) : Out.RingAct o.A D.O :=
  ⟨o.act.act, o.act.hom, o.act.one, o.act.mul, o.act.add⟩

@[simp] theorem htAct_act {s : S ⟶ Sp R} (o : Obj b N s) (c : D.O) : (htAct o).act c = o.act.act c := rfl

abbrev HTIw {s : S ⟶ Sp R} (o : Obj b N s) (w : Ideal (𝓞 D.F)) : Type 1 :=
  Chain (htAct o) (w.map (algebraMap (𝓞 D.F) D.O)) (Ideal.absNorm w ^ D.m) D.n

def HTIwMap {s' : S' ⟶ Sp R} {s : S ⟶ Sp R} {o' : Obj b N s'} {o : Obj b N s} {w : Ideal (𝓞 D.F)}
    (C' : HTIw o' w) (C : HTIw o w) (f : S' ⟶ S) : Prop :=
  ∃ m : ObjMap o' o f, Nonempty (ChainMap C' C f m.φ)

theorem HTIw.exists_pull {s' : S' ⟶ Sp R} {s : S ⟶ Sp R} {o' : Obj b N s'} {o : Obj b N s}
    {w : Ideal (𝓞 D.F)} (C : HTIw o w) {f : S' ⟶ S} (m : ObjMap o' o f) :
    ∃ C' : HTIw o' w, HTIwMap C' C f := by
  obtain ⟨C', ⟨e⟩⟩ := Chain.exists_pull (ρ' := htAct o') C m.cart m.act
  exact ⟨C', m, ⟨e⟩⟩

theorem HTIwMap.subsingleton {s' : S' ⟶ Sp R} {s : S ⟶ Sp R} {o' : Obj b N s'} {o : Obj b N s}
    {w : Ideal (𝓞 D.F)} (C' : HTIw o' w) (C : HTIw o w) (f : S' ⟶ S) (m : ObjMap o' o f) :
    Subsingleton (ChainMap C' C f m.φ) := inferInstance

def IsPlaceOf (b : Base D R) (i : Fin D.a) (w : Ideal (𝓞 D.F)) : Prop :=
  w.IsMaximal ∧ ((p : 𝓞 D.F) ∈ w) ∧
    ∀ (k : Type) [Field k] [CharP k p] (β : R →+* k), RingHom.ker (β.comp (b.t i)) = w

structure HTIwRep (b : Base D R) (N : ℕ) (w : Ideal (𝓞 D.F)) where

  X : Scheme.{0}

  s : X ⟶ Sp R

  univ : Obj b N s

  univC : HTIw univ w

  rep : ∀ (S : Scheme.{0}) (s' : S ⟶ Sp R) (o : Obj b N s') (C : HTIw o w),
    ∃! f : S ⟶ X, f ≫ s = s' ∧ HTIwMap C univC f

section Basic₂

example {s : S ⟶ Sp R} {o : Obj b N s} {w : Ideal (𝓞 D.F)} (C : HTIw o w) :
    IsIsogDeg (C.π (Fin.last D.n)) (Ideal.absNorm w ^ (D.m * D.n)) := by
  rw [pow_mul]; simpa using C.π_deg (Fin.last D.n)

example {s : S ⟶ Sp R} {o : Obj b N s} {w : Ideal (𝓞 D.F)} (C : HTIw o w) {T : Over S} (x : T ⟶ o.A)
    (h : x ≫ C.π (Fin.last D.n) = 1) (c : 𝓞 D.F) (hc : c ∈ w) : x ≫ o.act.act (algebraMap _ _ c) = 1 :=
  (C.ker_last T x).1 h _ (Ideal.mem_map_of_mem _ hc)

example {s : S ⟶ Sp R} {o : Obj b N s} {w : Ideal (𝓞 D.F)} (C : HTIw o w) (i : Fin (D.n + 1)) (c : 𝓞 D.F)
    (hc : c ∈ w) : ∃ g : C.B i ⟶ o.A, C.π i ≫ g = o.act.act (algebraMap _ _ c) :=
  (C.existsUnique_close i (Ideal.mem_map_of_mem _ hc)).exists

end Basic₂

end GlobalTheory.IwLevel
end
end

