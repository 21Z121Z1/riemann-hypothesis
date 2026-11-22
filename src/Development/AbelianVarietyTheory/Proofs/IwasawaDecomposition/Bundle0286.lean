import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0222
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.LatticeIdealNonzero
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0008
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanRangeMulVec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMtTieCoord
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0012
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemRangeSrcForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0119
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IwasawaDecompositionFiniteAdelesGL
section
open NumberField IsDedekindDomain Matrix
open scoped RestrictedProduct

noncomputable section

namespace GlobalTheory.IwasawaFinAd

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

def coordV (v : HeightOneSpectrum (𝓞 F)) : FiniteAdeleRing (𝓞 F) F →+* v.adicCompletion F where
  toFun a := a v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def locM (v : HeightOneSpectrum (𝓞 F)) (M : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) :
    Matrix (Fin n) (Fin n) (v.adicCompletion F) :=
  RingHom.mapMatrix (coordV v) M

def locGL (v : HeightOneSpectrum (𝓞 F)) :
    GL (Fin n) (FiniteAdeleRing (𝓞 F) F) →* GL (Fin n) (v.adicCompletion F) :=
  Units.map (RingHom.mapMatrix (coordV v)).toMonoidHom

theorem locM_mul (v : HeightOneSpectrum (𝓞 F)) (M N : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) :
    locM v (M * N) = locM v M * locM v N := map_mul _ _ _

theorem locM_one (v : HeightOneSpectrum (𝓞 F)) :
    locM v (1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) = 1 := map_one _

theorem matrix_ext_loc {M N : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)}
    (h : ∀ v, locM v M = locM v N) : M = N := by
  refine Matrix.ext fun i j => FiniteAdeleRing.ext F fun v => ?_
  exact congrFun (congrFun (h v) i) j

theorem gl_ext_loc {g h : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)} (e : ∀ v, locGL v g = locGL v h) :
    g = h :=
  Units.ext (matrix_ext_loc fun v => congrArg Units.val (e v))

def IntAt (v : HeightOneSpectrum (𝓞 F)) (M : Matrix (Fin n) (Fin n) (v.adicCompletion F)) : Prop :=
  ∀ i j, M i j ∈ v.adicCompletionIntegers F

theorem intAt_one (v : HeightOneSpectrum (𝓞 F)) : IntAt v (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
  intro i j
  rw [Matrix.one_apply]
  split_ifs
  · exact (v.adicCompletionIntegers F).one_mem
  · exact (v.adicCompletionIntegers F).zero_mem

def glueM (x : ∀ v : HeightOneSpectrum (𝓞 F), Matrix (Fin n) (Fin n) (v.adicCompletion F))
    (hx : ∀ᶠ v in Filter.cofinite, IntAt v (x v)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F) :=
  Matrix.of fun i j =>
    (⟨fun v => x v i j, hx.mono fun v h => h i j⟩ :
      Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F])

theorem locM_glueM (x : ∀ v : HeightOneSpectrum (𝓞 F), Matrix (Fin n) (Fin n) (v.adicCompletion F))
    (hx : ∀ᶠ v in Filter.cofinite, IntAt v (x v)) (v : HeightOneSpectrum (𝓞 F)) :
    locM v (glueM x hx) = x v := by
  ext i j
  rfl

def glueGL (x : ∀ v : HeightOneSpectrum (𝓞 F), GL (Fin n) (v.adicCompletion F))
    (hx : ∀ᶠ v in Filter.cofinite, IntAt v (x v).val ∧ IntAt v (x v)⁻¹.val) :
    GL (Fin n) (FiniteAdeleRing (𝓞 F) F) where
  val := glueM (fun v => (x v).val) (hx.mono fun _ h => h.1)
  inv := glueM (fun v => (x v)⁻¹.val) (hx.mono fun _ h => h.2)
  val_inv := matrix_ext_loc fun v => by
    rw [locM_mul, locM_glueM, locM_glueM, locM_one]; exact Units.mul_inv (x v)
  inv_val := matrix_ext_loc fun v => by
    rw [locM_mul, locM_glueM, locM_glueM, locM_one]; exact Units.inv_mul (x v)

theorem locGL_glueGL (x : ∀ v : HeightOneSpectrum (𝓞 F), GL (Fin n) (v.adicCompletion F))
    (hx : ∀ᶠ v in Filter.cofinite, IntAt v (x v).val ∧ IntAt v (x v)⁻¹.val) (v : HeightOneSpectrum (𝓞 F)) :
    locGL v (glueGL x hx) = x v :=
  Units.ext (locM_glueM _ (hx.mono fun _ h => h.1) v)

theorem eventually_intAt (M : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) :
    ∀ᶠ v in Filter.cofinite, IntAt v (locM v M) := by
  unfold IntAt
  rw [Filter.eventually_all]
  intro i
  rw [Filter.eventually_all]
  intro j
  exact (M i j).2

theorem upper_eq_uni_mul_diag {K : Type} [Field K] (b : GL (Fin n) K) (hb : b.val.BlockTriangular id) :
    ∃ u t : GL (Fin n) K, PIW.ClassFinD.IsUpperUni u.val ∧ PIW.ClassFinD.IsDiagM t.val ∧ b = u * t := by
  have hdet0 : b.val.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp b.isUnit).ne_zero
  have hne : ∀ i, b.val i i ≠ 0 := by
    intro i h
    apply hdet0
    rw [Matrix.det_of_upperTriangular hb]
    exact Finset.prod_eq_zero (Finset.mem_univ i) h
  let t : GL (Fin n) K :=
    ⟨diagonal (fun i => b.val i i), diagonal (fun i => (b.val i i)⁻¹),
      by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; exact mul_inv_cancel₀ (hne i),
      by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; exact inv_mul_cancel₀ (hne i)⟩
  have hU : ∀ i j, (b * t⁻¹).val i j = b.val i j * (b.val j j)⁻¹ := by
    intro i j
    change (b.val * diagonal (fun i => (b.val i i)⁻¹)) i j = _
    rw [mul_diagonal]
  refine ⟨b * t⁻¹, t, ⟨fun i j hij => ?_, fun i => ?_⟩, fun i j hij => ?_, by group⟩
  · rw [hU, hb hij, zero_mul]
  · rw [hU, mul_inv_cancel₀ (hne i)]
  · exact diagonal_apply_ne _ hij

theorem isUpperUni_one {K : Type} [CommRing K] : PIW.ClassFinD.IsUpperUni (1 : Matrix (Fin n) (Fin n) K) :=
  ⟨fun i j hij => Matrix.one_apply_ne (ne_of_gt hij), fun i => Matrix.one_apply_eq i⟩

theorem isDiagM_one {K : Type} [CommRing K] : PIW.ClassFinD.IsDiagM (1 : Matrix (Fin n) (Fin n) K) :=
  fun i j hij => Matrix.one_apply_ne hij

theorem intAt_of_glint (v : HeightOneSpectrum (𝓞 F)) (k : GL (Fin n) (v.adicCompletion F))
    (hk : k ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v)) : IntAt v k.val ∧ IntAt v k⁻¹.val := by
  obtain ⟨K, rfl⟩ := hk
  refine ⟨fun i j => (K.val i j).2, fun i j => ?_⟩
  rw [← map_inv]
  exact ((K⁻¹).val i j).2

end GlobalTheory.IwasawaFinAd

namespace GlobalTheory.IwasawaFinAd

open PIW.ClassFinD

theorem iwasawaAf : PIW.ClassFinD.IwasawaAf := by
  classical
  intro F _ _ n g
  let good : HeightOneSpectrum (𝓞 F) → Prop := fun v =>
    IntAt v (locGL v g).val ∧ IntAt v (locGL v g)⁻¹.val
  have hgood : ∀ᶠ v in Filter.cofinite, good v := by
    refine (eventually_intAt g.val).and ((eventually_intAt (g⁻¹).val).mono fun v h => ?_)
    rw [← map_inv]
    exact h
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F), ∃ u t k : GL (Fin n) (v.adicCompletion F),
      IsUpperUni u.val ∧ IsDiagM t.val ∧ IntAt v k.val ∧ IntAt v k⁻¹.val ∧ locGL v g = u * t * k ∧
      (good v → u = 1 ∧ t = 1 ∧ k = locGL v g) := by
    intro v
    by_cases hv : good v
    · exact ⟨1, 1, locGL v g, isUpperUni_one, isDiagM_one, hv.1, hv.2, by rw [one_mul, one_mul],
        fun _ => ⟨rfl, rfl, rfl⟩⟩
    · obtain ⟨b, k, hb, hk, hbk⟩ := Formalism.UG.P.spherical_iwasawa F v (locGL v g)
      obtain ⟨u, t, hu, ht, rfl⟩ := upper_eq_uni_mul_diag b hb
      obtain ⟨hk1, hk2⟩ := intAt_of_glint v k hk
      exact ⟨u, t, k, hu, ht, hk1, hk2, hbk, fun h => absurd h hv⟩
  choose uL tL kL huL htL hkL hkL' hgL hgoodL using hloc
  have hu : ∀ᶠ v in Filter.cofinite, IntAt v (uL v).val ∧ IntAt v (uL v)⁻¹.val :=
    hgood.mono fun v hv => by
      rw [(hgoodL v hv).1, inv_one]
      exact ⟨intAt_one v, intAt_one v⟩
  have ht : ∀ᶠ v in Filter.cofinite, IntAt v (tL v).val ∧ IntAt v (tL v)⁻¹.val :=
    hgood.mono fun v hv => by
      rw [(hgoodL v hv).2.1, inv_one]
      exact ⟨intAt_one v, intAt_one v⟩
  have hk : ∀ᶠ v in Filter.cofinite, IntAt v (kL v).val ∧ IntAt v (kL v)⁻¹.val :=
    Filter.Eventually.of_forall fun v => ⟨hkL v, hkL' v⟩
  refine ⟨glueGL uL hu, glueGL tL ht, glueGL kL hk, ⟨fun i j hij => ?_, fun i => ?_⟩, fun i j hij => ?_,
    ⟨fun i j v => hkL v i j, fun i j v => hkL' v i j⟩, ?_⟩
  · refine FiniteAdeleRing.ext F fun v => ?_
    change coordV v ((glueGL uL hu).val i j) = coordV v 0
    rw [map_zero]
    exact (huL v).1 i j hij
  · refine FiniteAdeleRing.ext F fun v => ?_
    change coordV v ((glueGL uL hu).val i i) = coordV v 1
    rw [map_one]
    exact (huL v).2 i
  · refine FiniteAdeleRing.ext F fun v => ?_
    change coordV v ((glueGL tL ht).val i j) = coordV v 0
    rw [map_zero]
    exact htL v i j hij
  · refine gl_ext_loc fun v => ?_
    rw [map_mul, map_mul, locGL_glueGL, locGL_glueGL, locGL_glueGL]
    exact hgL v

end GlobalTheory.IwasawaFinAd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeJwIndexEqConcreteLiftIndex
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.JwLift

theorem mem_dual_iff {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (x : V) :
    x ∈ Formalism.HermitianLatticesTheory.dual h L ↔ ∀ y ∈ L, ∃ c : 𝓞 K, algebraMap (𝓞 K) K c = h y x := by
  unfold Formalism.HermitianLatticesTheory.dual Formalism.E.hdual
  simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars, Submodule.mem_one]

theorem jwIdx_eq_jw : ∀ (D : D7) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} (A : FamIn D.what₂.LL G Pl0 T D.R.m) (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (tup : T → D.what₂.Tup) (eMt : ∀ (i : Fin D.R.m) (t : T), (Fin (lDim D A P0 ψ0 i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1)) (i : Fin D.R.m) (t : T) (hP : Formalism.DivisionValues.IsOrthProj (lH D A P0 ψ0 i t) (lZ0 D A P0 ψ0 Zs i t) (lPrj D A P0 ψ0 Zs i t)) (hF : FormsTie D.what₂.embLL ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap) (lH D A P0 ψ0 i t) (lE D A P0 ψ0 i t) (D.what₂.eMt (tup t) ((i : ℕ) + 1))) (hHZ : (lZ0 D A P0 ψ0 Zs i t)ᴴ * lH D A P0 ψ0 i t * lZ0 D A P0 ψ0 Zs i t = (A.side P0 ψ0 Zs).HT i t) (hsp : Submodule.span D.what₂.LL (↑((A.side P0 ψ0 Zs).Tl i t) : Set (Fin ((A.side P0 ψ0 Zs).dZ i t) → D.what₂.LL)) = ⊤) (hT : Idx.TjL D (tup t) ((i : ℕ) + 1) = (Formalism.DivisionValues.matLat (lZ0 D A P0 ψ0 Zs i t) ((A.side P0 ψ0 Zs).Tl i t)).map ((eMt i t).toLinearMap.restrictScalars (𝓞 D.what₂.LL))) (w : D.what₂.places.Pl), Idx.jwIdx D (tup t) ((i : ℕ) + 1) w = Formalism.DivisionValues.jw ((A.side P0 ψ0 Zs).HT i t) (D.plEq w) ((A.side P0 ψ0 Zs).Tl i t) := by
  intro D G _ _ Pl0 T A P0 ψ0 Zs tup eMt i t hP hF hHZ hsp hT w
  set HT := (A.side P0 ψ0 Zs).HT i t with hHTdef
  set Tl := (A.side P0 ψ0 Zs).Tl i t with hTldef
  let Z : Matrix (Fin (lDim D A P0 ψ0 i t)) (Fin ((A.side P0 ψ0 Zs).dZ i t)) D.what₂.LL := lZ0 D A P0 ψ0 Zs i t
  let Pr : Matrix (Fin ((A.side P0 ψ0 Zs).dZ i t)) (Fin (lDim D A P0 ψ0 i t)) D.what₂.LL := lPrj D A P0 ψ0 Zs i t
  have hP1 : Pr * Z = 1 := hP.1
  have hHZ' : Zᴴ * lH D A P0 ψ0 i t * Z = HT := hHZ
  have hT' : Idx.TjL D (tup t) ((i : ℕ) + 1) = (Tl.map ((Matrix.mulVecLin Z).restrictScalars (𝓞 D.what₂.LL))).map
      ((eMt i t).toLinearMap.restrictScalars (𝓞 D.what₂.LL)) := hT
  let f : (Fin ((A.side P0 ψ0 Zs).dZ i t) → D.what₂.LL) →ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1) :=
    (eMt i t).toLinearMap ∘ₗ Matrix.mulVecLin Z
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 : Z *ᵥ x = Z *ᵥ y := (eMt i t).injective hxy
    have h2 : Pr *ᵥ (Z *ᵥ x) = Pr *ᵥ (Z *ᵥ y) := by rw [h1]
    rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hP1, Matrix.one_mulVec, Matrix.one_mulVec] at h2
  have hTL : Idx.TjL D (tup t) ((i : ℕ) + 1) = Tl.map (f.restrictScalars (𝓞 D.what₂.LL)) := by
    rw [hT', ← Submodule.map_comp]
    rfl
  have hTV : Idx.TjV D (tup t) ((i : ℕ) + 1) = LinearMap.range f := by
    unfold Idx.TjV
    rw [hTL, Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, hsp, Submodule.map_top]
  have hin : ∀ y z, inner ℂ (D.what₂.jMt (tup t) ((i : ℕ) + 1) (f y)) (D.what₂.jMt (tup t) ((i : ℕ) + 1) (f z)) =
      D.what₂.embLL (Formalism.DivisionValues.hform HT y z) := by
    intro y z
    have := hF.inner (Z *ᵥ y) (Z *ᵥ z)
    have e1 : Formalism.DivisionValues.hform (lH D A P0 ψ0 i t) (Z *ᵥ y) (Z *ᵥ z) = Formalism.DivisionValues.hform HT y z := by
      rw [GlobalTheory.Mem.LiftForms.hform_dot HT, ← hHZ']
      exact GlobalTheory.Mem.LiftForms.hform_mulVec _ Z Z y z
    rw [← e1]
    exact this
  have hDual : Idx.TjDual D (tup t) ((i : ℕ) + 1) =
      (Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform HT) Tl).map (f.restrictScalars (𝓞 D.what₂.LL)) := by
    ext x
    constructor
    · rintro ⟨hx, hx2⟩
      rw [hTV] at hx
      obtain ⟨z, rfl⟩ := hx
      refine ⟨z, (mem_dual_iff _ _ _).2 fun y hy => ?_, rfl⟩
      obtain ⟨c, hc⟩ := hx2 (f y) (by rw [hTL]; exact ⟨y, hy, rfl⟩)
      rw [hin] at hc
      exact ⟨c, (D.what₂.embLL.injective hc).symm⟩
    · rintro ⟨z, hz, rfl⟩
      refine ⟨by rw [hTV]; exact ⟨z, rfl⟩, ?_⟩
      rintro a ha
      rw [hTL] at ha
      obtain ⟨y, hy, rfl⟩ := ha
      obtain ⟨c, hc⟩ := (mem_dual_iff _ _ _).1 hz y hy
      refine ⟨c, ?_⟩
      change _ = D.what₂.embLL (algebraMap (𝓞 D.what₂.LL) D.what₂.LL c)
      rw [hc]
      exact hin y z
  unfold Idx.jwIdx Formalism.DivisionValues.jw Formalism.HermitianLatticesTheory.jIdx
  rw [hTL, hDual]
  exact Formalism.BasicNotions.SkeletonIndexLemmas.lidx_map (D.plEq w) f hf _ _

end GlobalTheory.Mem.JwLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeTjEqImageOfCoordinateLattice
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.LiftForms

theorem TjL_eq_map_matLat : ∀ (D : D7) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} (A : FamIn D.what₂.LL G Pl0 T D.R.m) (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (tup : T → D.what₂.Tup) (eMt : ∀ (i : Fin D.R.m) (t : T), (Fin (lDim D A P0 ψ0 i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1)) (i : Fin D.R.m) (t : T) (hP : Formalism.DivisionValues.IsOrthProj (lH D A P0 ψ0 i t) (lZ0 D A P0 ψ0 Zs i t) (lPrj D A P0 ψ0 Zs i t)) (hF : FormsTie D.what₂.embLL ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap) (lH D A P0 ψ0 i t) (lE D A P0 ψ0 i t) (D.what₂.eMt (tup t) ((i : ℕ) + 1))) (hL : OLatTie D.what₂.embLL (D.what₂.MtLat (tup t) ((i : ℕ) + 1)) ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap) (lNab D A P0 ψ0 i t)) (hZ : Idx.Z0 D (tup t) ((i : ℕ) + 1) = Submodule.span ℂ (Set.range fun k => D.what₂.jMt (tup t) ((i : ℕ) + 1) (eMt i t ((lZ0 D A P0 ψ0 Zs i t).mulVec (Pi.single k 1))))) (hθ : ∀ x, D.what₂.thetaP (tup t) ((i : ℕ) + 1) (D.what₂.jMt (tup t) ((i : ℕ) + 1) (eMt i t x)) = D.what₂.thetaP (tup t) ((i : ℕ) + 1) (D.what₂.jMt (tup t) ((i : ℕ) + 1) (eMt i t ((lZ0 D A P0 ψ0 Zs i t).mulVec ((lPrj D A P0 ψ0 Zs i t).mulVec x))))), Idx.TjL D (tup t) ((i : ℕ) + 1) = (Formalism.DivisionValues.matLat (lZ0 D A P0 ψ0 Zs i t) ((A.side P0 ψ0 Zs).Tl i t)).map ((eMt i t).toLinearMap.restrictScalars (𝓞 D.what₂.LL)) := by
  intro D G _ _ Pl0 T A P0 ψ0 Zs tup eMt i t hP hF hL hZ hθ
  classical
  set J := (D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap with hJdef
  have hJ : ∀ x, J x = D.what₂.jMt (tup t) ((i : ℕ) + 1) (eMt i t x) := fun x => rfl
  have hspan : Idx.Z0 D (tup t) ((i : ℕ) + 1) =
      Submodule.span ℂ (J '' Set.range fun z => lZ0 D A P0 ψ0 Zs i t *ᵥ z) := by
    rw [hZ, span_range_mulVec]
    rfl

  have hproj : ∀ x, (Idx.Z0 D (tup t) ((i : ℕ) + 1)).starProjection (J x) =
      J (lZ0 D A P0 ψ0 Zs i t *ᵥ (lPrj D A P0 ψ0 Zs i t *ᵥ x)) := by
    intro x
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · rw [hspan]
      exact Submodule.subset_span ⟨_, ⟨_, rfl⟩, rfl⟩
    · intro w hw
      rw [hspan] at hw
      have hle : Submodule.span ℂ (J '' Set.range fun z => lZ0 D A P0 ψ0 Zs i t *ᵥ z) ≤
          (Submodule.span ℂ {J x - J (lZ0 D A P0 ψ0 Zs i t *ᵥ (lPrj D A P0 ψ0 Zs i t *ᵥ x))})ᗮ := by
        rw [Submodule.span_le]
        rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_left, inner_sub_right, hF.inner, hF.inner,
          hform_orth hP, sub_self]
      exact Submodule.mem_orthogonal_singleton_iff_inner_right.1 (hle hw)

  have hθall : ∀ y, D.what₂.thetaP (tup t) ((i : ℕ) + 1) y =
      D.what₂.thetaP (tup t) ((i : ℕ) + 1) ((Idx.Z0 D (tup t) ((i : ℕ) + 1)).starProjection y) := by
    have h := LinearMap.ext_on_range hF.span (f := D.what₂.thetaP (tup t) ((i : ℕ) + 1))
      (g := (D.what₂.thetaP (tup t) ((i : ℕ) + 1)).comp
        ((Idx.Z0 D (tup t) ((i : ℕ) + 1)).starProjection : D.what₂.Mt (tup t) ((i : ℕ) + 1) →L[ℂ] _).toLinearMap)
      (fun k => by
        show D.what₂.thetaP (tup t) ((i : ℕ) + 1) (J (Pi.single k 1)) =
          D.what₂.thetaP (tup t) ((i : ℕ) + 1) ((Idx.Z0 D (tup t) ((i : ℕ) + 1)).starProjection (J (Pi.single k 1)))
        rw [hproj]
        exact hθ _)
    intro y
    exact LinearMap.congr_fun h y
  have hle1 : (Idx.Z0 D (tup t) ((i : ℕ) + 1))ᗮ ≤ LinearMap.ker (D.what₂.thetaP (tup t) ((i : ℕ) + 1)) := by
    intro w hw
    rw [LinearMap.mem_ker, hθall, (Submodule.starProjection_apply_eq_zero_iff _).2 hw, map_zero]
  have hZj : D.what₂.Zj (tup t) ((i : ℕ) + 1) = Idx.Z0 D (tup t) ((i : ℕ) + 1) := by
    have h1 : D.what₂.Zj (tup t) ((i : ℕ) + 1) = (LinearMap.ker (D.what₂.thetaP (tup t) ((i : ℕ) + 1)))ᗮ := by
      rw [LinearMap.orthogonal_ker]
      rfl
    rw [h1]
    apply le_antisymm
    · have := Submodule.orthogonal_le hle1
      rwa [Submodule.orthogonal_orthogonal] at this
    · exact inf_le_left
  have hfix : ∀ y ∈ LinearMap.range (D.what₂.eMt (tup t) ((i : ℕ) + 1)), D.what₂.eMt (tup t) ((i : ℕ) + 1) y = y := by
    rintro _ ⟨y, rfl⟩
    exact congrArg (fun f : D.what₂.Mt (tup t) ((i : ℕ) + 1) →ₗ[ℂ] D.what₂.Mt (tup t) ((i : ℕ) + 1) => f y) (D.what₂.eMt_idem _ _)
  have h4' : ∀ y, D.what₂.eMt (tup t) ((i : ℕ) + 1) ((D.what₂.Zj (tup t) ((i : ℕ) + 1)).starProjection y) =
      (Idx.Z0 D (tup t) ((i : ℕ) + 1)).starProjection y := by
    intro y
    simp only [hZj]
    exact hfix _ (inf_le_right (a := (LinearMap.ker (D.what₂.thetaP (tup t) ((i : ℕ) + 1)))ᗮ)
      (Submodule.starProjection_apply_mem (Idx.Z0 D (tup t) ((i : ℕ) + 1)) y))

  have h6 : Submodule.span (𝓞 D.what₂.LL)
      {x | D.what₂.jMt (tup t) ((i : ℕ) + 1) x ∈ (D.what₂.MtLat (tup t) ((i : ℕ) + 1)).carrier} =
      (lNab D A P0 ψ0 i t).map ((eMt i t).toLinearMap.restrictScalars (𝓞 D.what₂.LL)) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro u hu
      obtain ⟨c, hc⟩ := hu
      refine ⟨(eMt i t).symm u, (hL.2 _).2 ⟨fun v => ⟨D.what₂.OtoLL (c v), D.O_int _⟩, ?_⟩, by simp⟩
      rw [hJ, LinearEquiv.apply_symm_apply, hc]
      rfl
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨c, hc⟩ := (hL.2 x).1 hx
      have hc' : D.what₂.jMt (tup t) ((i : ℕ) + 1) (eMt i t x) =
          ∑ v ∈ (D.what₂.MtLat (tup t) ((i : ℕ) + 1)).gen, D.what₂.embLL (c v : D.what₂.LL) • v := hc
      have key : ∃ y ∈ Submodule.span (𝓞 D.what₂.LL)
          {x | D.what₂.jMt (tup t) ((i : ℕ) + 1) x ∈ (D.what₂.MtLat (tup t) ((i : ℕ) + 1)).carrier},
          D.what₂.jMt (tup t) ((i : ℕ) + 1) y =
            ∑ v ∈ (D.what₂.MtLat (tup t) ((i : ℕ) + 1)).gen, D.what₂.embLL (c v : D.what₂.LL) • v := by
        refine Finset.sum_induction _ (fun m => ∃ y ∈ Submodule.span (𝓞 D.what₂.LL)
          {x | D.what₂.jMt (tup t) ((i : ℕ) + 1) x ∈ (D.what₂.MtLat (tup t) ((i : ℕ) + 1)).carrier},
            D.what₂.jMt (tup t) ((i : ℕ) + 1) y = m) ?_ ⟨0, zero_mem _, map_zero _⟩ fun v hv => ?_
        · rintro _ _ ⟨y, hy, rfl⟩ ⟨z, hz, rfl⟩
          exact ⟨y + z, add_mem hy hz, map_add _ _ _⟩
        · obtain ⟨y, hy⟩ := D.what₂.MtLat_sub (tup t) ((i : ℕ) + 1) v hv
          refine ⟨c v • y, Submodule.smul_mem _ _ (Submodule.subset_span ?_), by rw [Idx.smul_def, map_smulₛₗ, hy]⟩
          refine ⟨fun u => if u = v then 1 else 0, ?_⟩
          rw [hy, Finset.sum_eq_single v]
          · simp
          · intro u _ hu
            simp [hu]
          · intro h; exact absurd hv h
      obtain ⟨y, hy, hyx⟩ := key
      have hxy : y = eMt i t x := jMt_injective _ _ (hyx.trans hc'.symm)
      change eMt i t x ∈ _
      rw [← hxy]
      exact hy

  let π : D.what₂.MtL (tup t) ((i : ℕ) + 1) →ₗ[𝓞 D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1) :=
    ((eMt i t).toLinearMap ∘ₗ (lZ0 D A P0 ψ0 Zs i t).mulVecLin ∘ₗ
      (lPrj D A P0 ψ0 Zs i t).mulVecLin ∘ₗ (eMt i t).symm.toLinearMap).restrictScalars (𝓞 D.what₂.LL)
  have hπe : ∀ x, π (eMt i t x) = eMt i t (lZ0 D A P0 ψ0 Zs i t *ᵥ (lPrj D A P0 ψ0 Zs i t *ᵥ x)) := by
    intro x
    show eMt i t (lZ0 D A P0 ψ0 Zs i t *ᵥ (lPrj D A P0 ψ0 Zs i t *ᵥ (eMt i t).symm (eMt i t x))) = _
    rw [LinearEquiv.symm_apply_apply]
  have hπ : ∀ x, D.what₂.jMt (tup t) ((i : ℕ) + 1) (π x) = D.what₂.eMt (tup t) ((i : ℕ) + 1)
      ((D.what₂.Zj (tup t) ((i : ℕ) + 1)).starProjection (D.what₂.jMt (tup t) ((i : ℕ) + 1) x)) := by
    intro x
    obtain ⟨x, rfl⟩ := (eMt i t).surjective x
    rw [h4', ← hJ, hproj, hπe]
    rfl
  have hset : {x | D.what₂.jMt (tup t) ((i : ℕ) + 1) x ∈ D.what₂.TjSet (tup t) ((i : ℕ) + 1)} =
      π '' {x | D.what₂.jMt (tup t) ((i : ℕ) + 1) x ∈ (D.what₂.MtLat (tup t) ((i : ℕ) + 1)).carrier} := by
    ext x
    constructor
    · rintro ⟨m, hm, hx⟩
      obtain ⟨u, rfl⟩ := carrier_subset _ _ m hm
      exact ⟨u, hm, jMt_injective _ _ ((hπ u).trans hx)⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨_, hu, (hπ u).symm⟩
  unfold Idx.TjL
  rw [hset, ← Submodule.map_span, h6]
  ext x
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨_, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, (hπe y).symm⟩
  · rintro ⟨_, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩
    exact ⟨_, ⟨y, hy, rfl⟩, hπe y⟩

end GlobalTheory.Mem.LiftForms

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftLawImpliesAdelicExtensionBaseLevel
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.LiftSpan

theorem end_smul_smul {W : Type} [AddCommGroup W] [Module ℂ W] (L : Module.End ℂ W) (a b : ℂ) (x : W) :
    L (a • b • x) = (a * b) • L x := by
  rw [map_smul, map_smul, smul_smul]

set_option maxHeartbeats 16000000 in

theorem ext_mem_levSubV_of_lift : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.models_cV → R.grp_red_L → ∀ (i : Fin D.R.m) (t : T) (Φ : Bridge.Gf (Vc D i) → (R.cV i).W), (∀ (κ : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q) (hu : (R.B.L i t).act_tie.red κ ∈ F.P0) (h : Bridge.Gf (Vc D i)), Φ (h * κ) = (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch κ : ℂˣ) : ℂ) • D.what₂.embLL ((F.ψ0⁻¹ ⟨_, hu⟩ : D.what₂.LLˣ) : D.what₂.LL) • Φ h) → (R.cV i).ext Φ ∈ levSubV (Vc D i) (R.cV i).W (levS _ (R.βV i) (datVP R i t (R.levR F false))) (levChi _ (R.βV i) (datVP R i t (R.levR F false))) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hcV hred i t Φ hΦ
  intro k hk g
  have hkG : k ∈ GfC (Vc D i) := hk.1
  have hpar : finE (Vc D i) k ∈ Formalism.L2.DIV.parLev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t) := hk.2.1
  have hH : Formalism.L2.DIV.rTup (R.βV i) (R.datVt i t) (finE (Vc D i) k) ∈ (R.levR F false).H := hk.2.2
  have hq : (finHom (Vc D i)).rangeRestrict k ∈ (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q := by
    show Formalism.UG.bc (swapAE D) (finHom (Vc D i) k) ∈
      Formalism.L2.DIV.lev D.sp.cm (Vc D i).gram (R.βV i) (flagL (R.datVt i t))
    rw [← finE_eq]
    exact ⟨hpar, Subgroup.mem_top _⟩
  set κ : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q := ⟨_, hq⟩ with hκdef
  have hred' : R.eG ((R.B.L i t).act_tie.red κ) = Formalism.L2.DIV.rTup (R.βV i) (R.datVt i t) (finE (Vc D i) k) :=
    hred i t κ
  have hu : (R.B.L i t).act_tie.red κ ∈ F.P0 := by
    have h2 : R.eG.symm (Formalism.L2.DIV.rTup (R.βV i) (R.datVt i t) (finE (Vc D i) k)) ∈ F.P0 := hH
    rw [← hred', MulEquiv.symm_apply_apply] at h2
    exact h2
  have hlaw := hΦ κ hu ((finHom (Vc D i)).rangeRestrict g)
  have hchi : levChi _ (R.βV i) (datVP R i t (R.levR F false)) k =
      (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch κ : ℂˣ) : ℂ) •
        D.what₂.embLL ((F.ψ0⁻¹ ⟨_, hu⟩ : D.what₂.LLˣ) : D.what₂.LL) := by
    have hH' : Formalism.L2.DIV.rTup (R.βV i) (R.datVt i t) (finE (Vc D i) k) ∈ (R.levR F false).conj.H := hH
    have hP : (⟨R.eG.symm (Formalism.L2.DIV.rTup (R.βV i) (R.datVt i t) (finE (Vc D i) k)), hH⟩ : F.P0) =
        ⟨(R.B.L i t).act_tie.red κ, hu⟩ := Subtype.ext (by
          show R.eG.symm (Formalism.L2.DIV.rTup (R.βV i) (R.datVt i t) (finE (Vc D i) k)) = (R.B.L i t).act_tie.red κ
          rw [← hred', MulEquiv.symm_apply_apply])
    have hw := levFn_withP (V := Vc D i) (β := R.βV i) (L := R.datVt i t) (R.levR F false).conj (finE (Vc D i) k)
    have he := Formalism.L2.DIV.extendOne_of_mem (R.levR F false).conj.chi hH'
    have hw2 : Formalism.L2.DIV.levFn (R.βV i) (withP (R.datVt i t) (R.levR F false).conj) (finE (Vc D i) k) =
        (R.levR F false).conj.chi ⟨_, hH'⟩ * Formalism.L2.DIV.levFn (R.βV i) (flagL (R.datVt i t)) (finE (Vc D i) k) :=
      hw.trans (congrArg (fun u => u * Formalism.L2.DIV.levFn (R.βV i) (flagL (R.datVt i t)) (finE (Vc D i) k)) he)
    show ((Formalism.L2.DIV.levFn (R.βV i) (withP (R.datVt i t) (R.levR F false).conj) (finE (Vc D i) k) : ℂˣ) : ℂ) = _
    rw [hw2, Units.val_mul, mul_comm, smul_eq_mul]
    congr 1
    · show (((Units.map D.what₂.embLL.toMonoidHom (F.ψ0 ⟨R.eG.symm _, hH⟩))⁻¹ : ℂˣ) : ℂ) = _
      rw [hP]
      rfl
  have e1 := Formalism.IndefR.Eqv.Act.coefExt_mul (R.cV i) (hcV i) Φ g k hkG
  have e3 : (R.cV i).ext Φ g = (R.cV i).ρ g⁻¹ (Φ ((finHom (Vc D i)).rangeRestrict g)) := rfl
  rewrite [e1, hchi, hlaw, e3, smul_eq_mul]
  exact @end_smul_smul _ _ _ _ _ _ _

end GlobalTheory.LiftSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyClassMapAboveLastStep
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC

noncomputable def clDown {B : Base} {X : PreX B.toPre} (I : TC B X) (u : B.Word) (a : I.ι) (i : ℕ) (hi : B.R.m < i)
    (c : (I.stp u a i).Cl) : (I.stp u I.mu0 i).Cl :=
  (I.stp u I.mu0 i).cl (Idx.top I.sel (I.tup I.mu0) (I.idx I.mu0) (le_of_lt hi))
    ⟨(extTo (I.Q I.mu0) ((I.stp u a i).rep c).1.1, ∅), by
      rw [ysAt_ys_of_ne I.sel (I.tup I.mu0) (I.cst I.mu0) (by omega)]
      rfl⟩

theorem nonempty_clDown : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ), B.R.m < i →
    Nonempty ((I.stp u a i).Cl → (I.stp u I.mu0 i).Cl) :=
  fun I _ u a i hi => ⟨I.clDown u a i hi⟩

end GlobalTheory.Mem.Col2.TC
end

