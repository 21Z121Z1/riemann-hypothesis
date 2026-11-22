import Formalism.LocalToGlobal.LatticeGeometry.GeometryDefinitions.GlobLatUnimod
import Formalism.LocalToGlobal.LatticeGeometry.GeometryDefinitions.SingleFacts
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0003
import Formalism.LocalToGlobal.LatticeGeometry.GeometryDefinitions.DefsNN

-- bundled from Formalism.LocalToGlobal.LatticeGeometry.GeometryDefinitions.ExistsFrameOfSig
section
noncomputable section

open Module Matrix NumberField IsDedekindDomain Formalism.UG Formalism.BasicNotions Formalism.HN
open scoped TensorProduct

namespace Formalism.L2.Geo.Def.G1

section Frames

theorem exists_frame_of_sig {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (p : ℕ)
    (h : HasSignature M p 0) : ∃ Y : Matrix ι ι ℂ, IsUnit Y.det ∧ (Y⁻¹).conjTranspose * Y⁻¹ = M := by
  obtain ⟨e, P, hP⟩ := h
  set A : Matrix (Fin p ⊕ Fin 0) (Fin p ⊕ Fin 0) ℂ := (P : Matrix (Fin p ⊕ Fin 0) (Fin p ⊕ Fin 0) ℂ) with hA
  have hJ : Jpq p 0 = 1 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · simp [Jpq, Matrix.one_apply]
    · exact j.elim0
    · exact i.elim0
    · exact i.elim0
  have hcT : cT (starRingEnd ℂ) A = A.conjTranspose := by
    ext i j; simp [cT, Matrix.conjTranspose_apply]
  rw [hJ, hcT] at hP
  have hdetA : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det _).1 P.isUnit
  have hM' : M.reindex e e = (A⁻¹).conjTranspose * A⁻¹ := by
    have h1 : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hdetA
    calc M.reindex e e = (A * A⁻¹).conjTranspose * M.reindex e e * (A * A⁻¹) := by
          rw [h1, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
      _ = (A⁻¹).conjTranspose * (A.conjTranspose * M.reindex e e * A) * A⁻¹ := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = (A⁻¹).conjTranspose * A⁻¹ := by rw [hP, Matrix.mul_one]
  refine ⟨A.submatrix e e, ?_, ?_⟩
  · rw [Matrix.det_submatrix_equiv_self]; exact hdetA
  · rw [Matrix.inv_submatrix_equiv, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, ← hM']
    ext i j
    simp

theorem frameOf_spec {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ)
    (h : ∃ Y : Matrix ι ι ℂ, IsUnit Y.det ∧ (Y⁻¹).conjTranspose * Y⁻¹ = M) :
    IsUnit (frameOf M).det ∧ ((frameOf M)⁻¹).conjTranspose * (frameOf M)⁻¹ = M := by
  rw [frameOf, dif_pos h]
  exact h.choose_spec

end Frames

section Space

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

open Formalism.L2.Herm

theorem crdLat_mem (S : HSpace E) (L : Submodule (𝓞 E) S.V) (x : S.V) : crd S x ∈ crdLat S L ↔ x ∈ L := by
  simp only [crdLat, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨y, hy, hyx⟩
    rwa [(crd S).injective hyx] at hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem crdLat_lattice (S : HSpace E) (L : Submodule (𝓞 E) S.V) (hL : Submodule.IsLattice E L) :
    Submodule.IsLattice E (crdLat S L) := by
  refine ⟨hL.fg.map _, ?_⟩
  have hset : (crdLat S L : Set (Fin S.rank → E)) =
      (crd S : S.V →ₗ[E] (Fin S.rank → E)) '' (L : Set S.V) := by
    ext u; simp [crdLat]
  rw [hset, Submodule.span_image, hL.span_eq_top, Submodule.map_top]
  exact LinearMap.range_eq_top.2 (crd S).surjective

end Space

section Twist

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {E : Type} [Field E] [NumberField E] [StarRing E]

end Twist

end Formalism.L2.Geo.Def.G1
end
end

-- bundled from Formalism.LocalToGlobal.LatticeGeometry.GeometryDefinitions.KroneckerProductDet
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions

noncomputable section

namespace Formalism.L2.Geo.Def

def TensorFockProduct : Prop :=
  ∀ (T σ : Type) [Fintype T] [DecidableEq T] (p q : T → MvPolynomial σ ℂ),
    Formalism.REAL.fockF (∏ τ, rename (Prod.mk τ) (p τ)) (∏ τ, rename (Prod.mk τ) (q τ)) = ∏ τ, Formalism.REAL.fockF (p τ) (q τ)

def KroneckerProductDet : Prop :=
  ∀ (R T : Type) [CommRing R] [Fintype T] [DecidableEq T] (I : T → Type) [∀ τ, Fintype (I τ)]
    [∀ τ, DecidableEq (I τ)] (A : ∀ τ, Matrix (I τ) (I τ) R),
    (Matrix.of fun i j : (∀ τ, I τ) => ∏ τ, A τ (i τ) (j τ)).det =
      ∏ τ, (A τ).det ^ (∏ τ' ∈ Finset.univ.erase τ, Fintype.card (I τ'))

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def LocalFibreLattice (D : D7) : Prop :=
  ∀ (ell : D.what₂.Tau → HLat D.what₂.LL), (∀ τ, (ell τ).Good ∧ (ell τ).rank = 1) →
    ∀ (κ : D.what₂.Tau → DomWeight (nW D)) (c : XDef D) (w : HeightOneSpectrum (𝓞 D.what₂.LL))
      (B : D.what₂.Tau → GL (Fin (nW D)) D.what₂.LL),
      (∀ τ, Formalism.HermitianLatticesTheory.loc (K := D.what₂.LL) w.asIdeal (TxLat D ell c τ) =
        Formalism.HermitianLatticesTheory.loc (K := D.what₂.LL) w.asIdeal (colSpan D (B τ))) →
      ∀ F : MvPolynomial (VarT D) D.what₂.LL,
        F ∈ Formalism.HermitianLatticesTheory.loc (K := D.what₂.LL) w.asIdeal (FibLat D ell κ c) ↔
          twAct D B (fun τ => (κ τ).detShift) F ∈ Formalism.HermitianLatticesTheory.loc (K := D.what₂.LL) w.asIdeal (intLat D κ)

end Formalism.L2.Geo.Def
end
end

