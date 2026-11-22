import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1625
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1626
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1583
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1613
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1623
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1637
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1627
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1631
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1628

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqualizerSectionsClosedIdealStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equalizer_sections_closed_ideal : ∀ (R : Type) [CommRing R] (X : Over (Sp R)), IsSeparated X.hom → ∀ (x y : Sp R ⟶ X.left), x ≫ X.hom = 𝟙 _ → y ≫ X.hom = 𝟙 _ → ∃ I : Ideal R, ∀ (T : Type) [CommRing T] (ψ : R →+* T), (spMap ψ ≫ x = spMap ψ ≫ y ↔ ∀ r ∈ I, ψ r = 0) := by
  first | exact @GlobalTheory.sections_eqLocus_ideal | exact GlobalTheory.sections_eqLocus_ideal | (intros; apply GlobalTheory.sections_eqLocus_ideal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EulerCharLineBundleFibreModpEqRatProjectiveStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eulerChar_lineBundle_fibre_modp_eq_rat_projective : ∀ (k : Type) [CommRing k] (W : Scheme.{0}) (q : W ⟶ Sp k) (D : ℕ), IsArithVar q D → ∀ (p : ℕ) [Fact p.Prime] (N : LB W), N.IsLB → (letI := GlobalTheory.algebraΓOfHom (pullback.snd (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p)))); chi (ZMod p) (toMod (N.pull (pullback.fst (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p)))))) = chi ℚ (toMod (N.pull (ratFibre.fst q))) ∧ chi (ZMod p) (structureModule (pullback (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p))))) = chi ℚ (structureModule (ratFibre q))) := by
  first | exact @GlobalTheory.ChiFibre.chi_fibre_eq | exact GlobalTheory.ChiFibre.chi_fibre_eq | (intros; apply GlobalTheory.ChiFibre.chi_fibre_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsC1DensityForLinePairStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_C1_density_for_line_pair : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (V L L' : X.Modules) (r : ℕ) (h : Met p σ V r) (l : L ⟶ V) (l' : L' ⟶ V), h.IsCInf → IsSubbundle l → IsSubbundle l' → IsVB L 1 → IsVB L' 1 → ∀ n : ℕ, ∃ m : AlgChart p σ 1 → CxPts p σ → ℂ, (∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, ContDiffAt ℝ 1 (fun v => m c (c.e.symm v)) (c.e y)) ∧ (∀ (c c' : AlgChart p σ 1) (y : CxPts p σ), y ∈ c.e.source → y ∈ c'.e.source → m c y = ChartGlue.transDet c.e c'.e y * m c' y) ∧ ∀ (U : X.Opens) (t : Γ(L, U)) (t' : Γ(L', U)), IsFrame (fun _ : Fin 1 => t) → IsFrame (fun _ : Fin 1 => t') → ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, y ∈ ptsIn p σ U → m c y = angleForm n (fun v => (h.form (l.app U t) (l.app U t) (c.e.symm v)).re) (fun v => (h.form (l'.app U t') (l'.app U t') (c.e.symm v)).re) (fun v => h.form (l'.app U t') (l.app U t) (c.e.symm v)) (EuclideanSpace.single 0 1) (c.e y) := by
  first | exact @GlobalTheory.angleForm_global | exact GlobalTheory.angleForm_global | (intros; apply GlobalTheory.angleForm_global <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousUnitaryDiagonalEmbeddingDoubled
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.DiagEmbU

section Gen

variable {A : Type} [CommRing A] {n : ℕ}

def dg (M : Matrix (Fin n) (Fin n) A) : Matrix (Fin (n + n)) (Fin (n + n)) A :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks M 0 0 1)

theorem dg_mul (M N : Matrix (Fin n) (Fin n) A) : dg (M * N) = dg M * dg N := by
  simp only [dg, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp

theorem dg_one : dg (1 : Matrix (Fin n) (Fin n) A) = 1 := by
  simp [dg, Matrix.fromBlocks_one]

theorem dg_sub_one_apply (M : Matrix (Fin n) (Fin n) A) (i j : Fin (n + n)) :
    (dg M - 1) i j = Sum.elim (fun a => Sum.elim (fun b => (M - 1) a b) (fun _ => 0)) (fun _ _ => 0)
      (finSumFinEquiv.symm i) (finSumFinEquiv.symm j) := by
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rw [← dg_one]
  rcases i with a | a <;> rcases j with b | b <;> simp only [dg, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.map_apply, Matrix.transpose_apply, Matrix.sub_apply, Formalism.UG.cT] <;> simp

theorem det_dg (M : Matrix (Fin n) (Fin n) A) : (dg M).det = M.det := by
  rw [dg, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

theorem continuous_dg [TopologicalSpace A] : Continuous (dg (A := A) (n := n)) :=
  (Continuous.matrix_fromBlocks continuous_id continuous_const continuous_const continuous_const).matrix_reindex _ _

def dgHom : Matrix (Fin n) (Fin n) A →* Matrix (Fin (n + n)) (Fin (n + n)) A where
  toFun := dg
  map_one' := dg_one
  map_mul' := dg_mul

def diagGL : GL (Fin n) A →* GL (Fin (n + n)) A := Units.map (dgHom (A := A) (n := n))

theorem continuous_diagGL [TopologicalSpace A] : Continuous (diagGL (A := A) (n := n)) :=
  Continuous.units_map _ continuous_dg

theorem dg_map {B : Type} [CommRing B] (φ : A →+* B) (M : Matrix (Fin n) (Fin n) A) :
    (dg M).map φ = dg (M.map φ) := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases i with a | a <;> rcases j with b | b <;> simp only [dg, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.map_apply, Matrix.transpose_apply, Matrix.sub_apply, Formalism.UG.cT] <;> simp [Matrix.one_apply]

theorem bc_diagGL {B : Type} [CommRing B] (φ : A →+* B) (g : GL (Fin n) A) :
    Formalism.UG.bc φ (diagGL g) = diagGL (Formalism.UG.bc φ g) := by
  ext : 1
  exact dg_map φ _

theorem cT_dg (s : A →+* A) (M : Matrix (Fin n) (Fin n) A) :
    Formalism.UG.cT s (dg M) = Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (Formalism.UG.cT s M) 0 0 1) := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases i with a | a <;> rcases j with b | b <;> simp only [dg, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.map_apply, Matrix.transpose_apply, Matrix.sub_apply, Formalism.UG.cT] <;> simp [Matrix.one_apply, eq_comm]

theorem diagGL_mem (s : A →+* A) (J K : Matrix (Fin n) (Fin n) A) {g : GL (Fin n) A}
    (hg : g ∈ Formalism.UG.UJ s J) :
    diagGL g ∈ Formalism.UG.UJ s (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks J 0 0 K)) := by
  have hg' : Formalism.UG.cT s (g : Matrix (Fin n) (Fin n) A) * J * (g : Matrix (Fin n) (Fin n) A) = J := hg
  show Formalism.UG.cT s (dg (g : Matrix (Fin n) (Fin n) A)) * _ * dg (g : Matrix (Fin n) (Fin n) A) = _
  rw [cT_dg, dg]
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp [hg']

end Gen

end GlobalTheory.DiagEmbU

namespace GlobalTheory.DiagEmbU

open GlobalTheory.WeilSchrodinger.DblTarget

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem JR_dblG (R : Type) [CommRing R] [Algebra F R] {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    JR (F := F) R (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (JR (F := F) R J) 0 0 (-JR (F := F) R J)) := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases i with a | a <;> rcases j with b | b <;>
    simp only [JR, GlobalTheory.WeilSchrodinger.DblTargetF.dblG, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_apply_apply, Matrix.map_apply] <;> simp [dbl]

theorem dblG_eq {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    GlobalTheory.WeilSchrodinger.DblTargetF.dblG J =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks J 0 0 (-J)) := rfl

def diagU (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    Formalism.IndefR.DatumF.GAF σ J →* Formalism.IndefR.DatumF.GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J) :=
  ((diagGL (A := AF F ⊗[F] E)).comp (Formalism.IndefR.DatumF.matHomF σ J)).codRestrict
    (HR (AF F) σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J)) fun g => by
      have hg : (show HR (AF F) σ J from g).1 ∈ Formalism.UG.UJ (sigR (AF F) σ) (JR (F := F) (AF F) J) :=
        (show HR (AF F) σ J from g).2
      have := diagGL_mem (sigR (AF F) σ) (JR (F := F) (AF F) J) (-JR (F := F) (AF F) J) hg
      show _ ∈ Formalism.UG.UJ (sigR (AF F) σ) (JR (F := F) (AF F) (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J))
      rw [JR_dblG]
      exact this

theorem mtF_diagU (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (h : Formalism.IndefR.DatumF.GAF σ J) :
    Formalism.IndefR.DatumF.mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J) (diagU σ J h) =
      dg (Formalism.IndefR.DatumF.mtF σ J h) := rfl

end Main

end GlobalTheory.DiagEmbU

namespace GlobalTheory.DiagEmbU

open GlobalTheory.WeilSchrodinger.DblTarget

theorem exists_diagEmb : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n : ℕ) (J : Matrix (Fin n) (Fin n) E),
      ∃ ι : Formalism.IndefR.DatumF.GAF σ J →* Formalism.IndefR.DatumF.GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J),
        Continuous ι ∧
        (∀ h, Formalism.IndefR.DatumF.mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J) (ι h) =
          Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (Formalism.IndefR.DatumF.mtF σ J h) 0 0 1)) ∧
        (∀ γ ∈ Formalism.IndefR.DatumF.GQF σ J, ι γ ∈ Formalism.IndefR.DatumF.GQF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J)) ∧
        (∀ e h, Formalism.IndefR.DatumF.SuppAtF σ e J h → Formalism.IndefR.DatumF.SuppAtF σ e (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J) (ι h)) ∧
        (∀ e h y, Formalism.IndefR.DatumF.IsDetAtF σ e J h y →
          Formalism.IndefR.DatumF.IsDetAtF σ e (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J) (ι h) y) := by
  intro F E _ _ _ _ _ σ n J
  refine ⟨diagU σ J, ?_, fun h => mtF_diagU σ J h, ?_, ?_, ?_⟩
  · exact Continuous.subtype_mk (continuous_diagGL.comp continuous_subtype_val) _
  · intro γ hγ
    have h1 : (show HR (AF F) σ J from γ).1 ∈ HFin (AF F) σ J := Subgroup.mem_subgroupOf.mp hγ
    obtain ⟨γ₀, hγ₀, he⟩ := Subgroup.mem_map.mp h1
    refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map.mpr ⟨diagGL γ₀, ?_, ?_⟩)
    · rw [dblG_eq]
      exact diagGL_mem _ J (-J) hγ₀
    · rw [bc_diagGL, he]
      rfl
  · intro e h hs i j
    rw [mtF_diagU]
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    rw [dg_sub_one_apply]
    rcases i with a | a <;> rcases j with b | b <;> simp only [Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr, mul_zero]
    exact hs a b
  · intro e h y hy
    show (y : Formalism.IndefR.DatumF.AEF F E) = e * (Formalism.IndefR.DatumF.mtF σ _ (diagU σ J h)).det + (1 - e)
    rw [mtF_diagU, det_dg]
    exact hy

end GlobalTheory.DiagEmbU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagLagrangian
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.WeilSchrodinger.DiagLagr

def fold (n : ℕ) (i : Fin (n + n)) : Fin n := Sum.elim id id (finSumFinEquiv.symm i)

theorem diagCols_mul {A : Type} [CommRing A] {n m : ℕ} (u : Matrix (Fin n) (Fin m) A) :
    ((diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) A).submatrix finSumFinEquiv.symm id) * u =
      u.submatrix (fold n) id := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  rcases i with i | i <;>
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, fold, Equiv.symm_apply_apply] <;>
    simp [diagCols, Matrix.one_apply]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hTens_fold (σ : E →ₐ[F] E) {n m : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (JB : Matrix (Fin m) (Fin m) (AF F ⊗[F] E)) (u v : Matrix (Fin n) (Fin m) (AF F ⊗[F] E)) :
    hTens (cA σ) (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J)ᵀ) JB (u.submatrix (fold n) id)
      (v.submatrix (fold n) id) = 0 := by
  simp only [hTens, ← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, Matrix.submatrix_apply, fold,
    GlobalTheory.WeilSchrodinger.DblTargetF.dblG, incM, Matrix.map_apply, Matrix.transpose_apply, Matrix.reindex_apply,
    Equiv.symm_apply_apply, id]
  simp [dbl]

def repL (F : Type) [Field F] [NumberField F] [Algebra F E] (n m : ℕ) :
    Matrix (Fin n) (Fin m) E →ₗ[F] Matrix (Fin (n + n)) (Fin m) (AF F ⊗[F] E) where
  toFun x := (incM F x).submatrix (fold n) id
  map_add' x y := by ext i j; simp [incM]
  map_smul' a x := by
    ext i j
    simp [incM, inclR, TensorProduct.tmul_smul]

theorem repL_injective (n m : ℕ) : Function.Injective (repL (E := E) F n m) := by
  intro x y h
  have : Nontrivial (AF F) :=
    (NumberField.AdeleRing.algebraMap_injective (NumberField.RingOfIntegers F) F).nontrivial
  have hi : Function.Injective (inclR (F := F) (E := E) (AF F)) := by
    have : Nontrivial (AF F ⊗[F] E) :=
      (Algebra.TensorProduct.includeLeft_injective (R := F) (S := F) (A := AF F) (B := E)
        (algebraMap F E).injective).nontrivial
    exact RingHom.injective _
  ext i j
  have := congrFun (congrFun h (finSumFinEquiv (Sum.inl i))) j
  simp only [repL, LinearMap.coe_mk, AddHom.coe_mk, Matrix.submatrix_apply, fold, Equiv.symm_apply_apply, incM,
    Matrix.map_apply, Sum.elim_inl, id] at this
  exact hi this

theorem exists_diag_lagrangian : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (nS nT : ℕ) (JT : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E)
    (κ : Type) [Fintype κ]
    (co : Darboux (symp (cA σ) ξ (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) (incM F JB)) κ),
    (∀ x : Matrix (Fin (nT + nT)) (Fin nS) E, ∃ y z : κ → F,
      co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    ∃ L : Submodule F ((κ → F) × (κ → F)), (∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) ∧
      Module.finrank F L = Fintype.card κ ∧
      ∀ (t : AF F), ∀ w ∈ L, ∃ u : Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E),
        co.e (((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) * u) = t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i))) := by
  intro F E _ _ _ _ _ σ nS nT JT JB ξ κ _ co hrat
  have hinj := NumberField.AdeleRing.algebraMap_injective (NumberField.RingOfIntegers F) F
  have : Nontrivial (AF F) := hinj.nontrivial
  let i1 : (κ → F) →ₗ[F] (κ → AF F) := (Algebra.linearMap F (AF F)).compLeft κ
  let ι : ((κ → F) × (κ → F)) →ₗ[F] ((κ → AF F) × (κ → AF F)) := i1.prodMap i1
  have hι : ∀ w, ι w = ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i))) :=
    fun _ => rfl
  have hιi : Function.Injective ι := by
    intro a b h
    rw [hι, hι, Prod.mk.injEq] at h
    exact Prod.ext (funext fun i => hinj (congrFun h.1 i)) (funext fun i => hinj (congrFun h.2 i))
  let g : Matrix (Fin nT) (Fin nS) E →ₗ[F] ((κ → AF F) × (κ → AF F)) :=
    (co.e.toLinearMap.restrictScalars F) ∘ₗ repL F nT nS
  have hg : ∀ x, g x = co.e ((incM F x).submatrix (fold nT) id) := fun _ => rfl
  have hgi : Function.Injective g := co.e.injective.comp (repL_injective nT nS)
  have hle : LinearMap.range g ≤ LinearMap.range ι := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, z, h⟩ := hrat (x.submatrix (fold nT) id)
    exact ⟨(y, z), h.symm⟩
  refine ⟨(LinearMap.range g).comap ι, ?_, ?_, ?_⟩
  · rintro a ⟨x, hx⟩ b ⟨x', hx'⟩
    have h := co.form ((incM F x).submatrix (fold nT) id) ((incM F x').submatrix (fold nT) id)
    rw [symp, hTens_fold, mul_zero, map_zero, ← hg, ← hg, hx, hx', hι, hι, eq_comm, sub_eq_zero] at h
    apply hinj
    simpa only [dotProduct, map_sum, map_mul] using h
  · have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
    have h1 : Module.finrank F ((LinearMap.range g).comap ι) = nT * nS * Module.finrank F E := by
      rw [(Submodule.equivMapOfInjective ι hιi _).finrank_eq, Submodule.map_comap_eq_of_le hle,
        LinearMap.finrank_range_of_inj hgi, Module.finrank_matrix]
      simp
    have h2 := co.e.finrank_eq
    rw [Module.finrank_matrix, Module.finrank_baseChange, Module.finrank_prod, Module.finrank_fintype_fun_eq_card] at h2
    simp only [Fintype.card_fin] at h2
    rw [h1]
    nlinarith [h2]
  · rintro t w ⟨x, hx⟩
    refine ⟨t • incM F x, ?_⟩
    rw [← hι, ← hx, hg, diagCols_mul, ← map_smul]
    rfl

end GlobalTheory.WeilSchrodinger.DiagLagr

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDominantOpenNatCastIsUnitNonZeroDivisorStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dominant_natCast_isUnit_of_nonZeroDivisor : ∀ (T : Scheme.{0}) (c : ℕ), (∀ (U : T.Opens) (f : Γ(T, U)), (c : Γ(T, U)) * f = 0 → f = 0) → ∃ (U : Scheme.{0}) (j : U ⟶ T), IsSchemeTheoreticallyDominant j ∧ IsUnit (c : Γ(U, ⊤)) := by
  first | (exact @GlobalTheory.exists_schemeTheoreticallyDominant_isUnit_natCast) | (exact GlobalTheory.exists_schemeTheoreticallyDominant_isUnit_natCast) | (intros; apply GlobalTheory.exists_schemeTheoreticallyDominant_isUnit_natCast  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionKillingFiniteTateModuleImag
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbVarRedCut

theorem exists_finiteDimensional_galTate_eq_one : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], LocallyOfFiniteType A.hom →
    ∀ (l : ℕ) [Fact l.Prime] (I : Set (Ω ≃ₐ[K] Ω)), (galTate A l '' I).Finite →
      ∃ L : IntermediateField K Ω, FiniteDimensional K L ∧
        ∀ σ ∈ I, (∀ a ∈ L, σ a = a) → galTate A l σ = 1 := by
  intro K Ω _ _ _ _ A _ _ hA l _ I hI
  classical
  have key : ∀ s : Module.End ℤ_[l] (Tate l (ptOver K Ω ⟶ A)), ∃ F : Finset Ω,
      ∀ σ : Ω ≃ₐ[K] Ω, galTate A l σ = s → (∀ a ∈ F, σ a = a) → s = 1 := by
    intro s
    by_cases hs : s = 1
    · exact ⟨∅, fun _ _ _ => hs⟩
    · have hex : ∃ (t : Tate l (ptOver K Ω ⟶ A)) (n : ℕ), (s t).lev n ≠ t.lev n := by
        by_contra h
        push_neg at h
        exact hs (LinearMap.ext fun t => Tate.ext fun n => h t n)
      obtain ⟨t, n, htn⟩ := hex
      obtain ⟨F, hF⟩ := GlobalTheory.T.exists_finset_fixing_point_locallyFiniteType K Ω A hA (t.lev n)
      refine ⟨F, fun σ hσ hfix => ?_⟩
      exfalso
      apply htn
      rw [← hσ, lev_galTate]
      exact hF σ hfix
  choose F hF using key
  refine ⟨IntermediateField.adjoin K ((hI.toFinset.biUnion F : Finset Ω) : Set Ω), ?_, ?_⟩
  · exact IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  · intro σ hσ hfix
    refine hF (galTate A l σ) σ rfl fun a ha => hfix a (IntermediateField.subset_adjoin _ _ ?_)
    rw [Finset.mem_coe]
    exact Finset.mem_biUnion.2 ⟨_, hI.mem_toFinset.2 ⟨σ, hσ, rfl⟩, ha⟩

end GlobalTheory.AbVarRedCut
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFockMapSignaturesDependOnPlaceStatement
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fockMap_signatures_depend_on_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ), IsCMExt F E σ → IsStd ψ → FramedD τ JA JB a b A C →
    ∃ Φ, IsFockMapD ψ τ d A C Φ := by
  first | exact @GlobalTheory.HoweD.exists_isFockMapD | exact GlobalTheory.HoweD.exists_isFockMapD | (intros; apply GlobalTheory.HoweD.exists_isFockMapD <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundDomainRationalPointsAdeleTupleFinitePoStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fundDomain_rationalPointsAdeleTuple_finite_pos : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∃ 𝓕₁ : Set (κ → AF F), @IsAddFundamentalDomain (GlobalTheory.ThetaParseval.ratVec F κ) _ _ _ (borel _) 𝓕₁ μ ∧ μ 𝓕₁ ≠ 0 ∧ μ 𝓕₁ ≠ ⊤ := by
  first | exact @GlobalTheory.RatVecDomain.exists_fundamentalDomain | exact GlobalTheory.RatVecDomain.exists_fundamentalDomain | (intros; apply GlobalTheory.RatVecDomain.exists_fundamentalDomain <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisSmulEqValuationSubringOverDvr
section
open scoped Pointwise
open GlobalTheory.Published GlobalTheory.Published.AbVarRed

namespace GlobalTheory.ValConj

theorem isLocallyConstant_apply {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] (x : Ω) :
    IsLocallyConstant (fun g : Ω ≃ₐ[K] Ω => g x) := by
  let : TopologicalSpace Ω := ⊥
  have : DiscreteTopology Ω := ⟨rfl⟩
  have : ContinuousSMul (Ω ≃ₐ[K] Ω) Ω :=
    continuousSMul_iff_stabilizer_isOpen.mpr fun y => stabilizer_isOpen_of_isIntegral y
  rw [IsLocallyConstant.iff_continuous]
  exact (continuous_id.smul continuous_const : Continuous fun g : Ω ≃ₐ[K] Ω => g • x)

theorem exists_smul_eq_of_isAbove (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] (Ω : Type) [Field Ω] [Algebra K Ω] [IsGalois K Ω]
    (V V' : ValuationSubring Ω) (hV : IsAbove R K V.toSubring) (hV' : IsAbove R K V'.toSubring) :
    ∃ g : Ω ≃ₐ[K] Ω, g • V = V' := by
  classical
  have key := (isCompact_univ (X := Ω ≃ₐ[K] Ω)).inter_iInter_nonempty
    (fun x : Ω => {g : Ω ≃ₐ[K] Ω | g x ∈ V' ↔ x ∈ V})
    (fun x => ((isLocallyConstant_apply (K := K) x).comp (fun y => y ∈ V' ↔ x ∈ V)).isClosed_fiber True
      |> fun h => by simpa using h)
    (fun u => by
      let L : IntermediateField K Ω := (FiniteGaloisIntermediateField.adjoin K (u : Set Ω)).toIntermediateField
      have hL : ∀ x ∈ u, x ∈ L := fun x hx => FiniteGaloisIntermediateField.subset_adjoin K (u : Set Ω) hx
      have hc : ∀ W : ValuationSubring Ω, IsAbove R K W.toSubring →
          IsAbove R K (W.comap (algebraMap L Ω)).toSubring := fun W hW => by
        unfold IsAbove at hW ⊢
        rw [← hW]
        ext y
        rfl
      obtain ⟨τ, hτ⟩ := GlobalTheory.T.galois_transitive_on_valuation_rings R K L _ _ (hc V hV) (hc V' hV')
      refine ⟨τ.liftNormal Ω, trivial, Set.mem_iInter₂.2 fun x hx => ?_⟩
      have h1 : τ.liftNormal Ω x = algebraMap L Ω (τ ⟨x, hL x hx⟩) := τ.liftNormal_commutes Ω ⟨x, hL x hx⟩
      change τ.liftNormal Ω x ∈ V' ↔ x ∈ V
      rw [h1, ← ValuationSubring.mem_comap, ← hτ]
      exact ValuationSubring.smul_mem_pointwise_smul_iff (g := τ) (x := (⟨x, hL x hx⟩ : L))
        (S := V.comap (algebraMap L Ω)))
  obtain ⟨g, -, hg⟩ := key
  refine ⟨g, ?_⟩
  ext y
  obtain ⟨x, rfl⟩ := g.surjective y
  have := Set.mem_iInter.1 hg x
  exact (ValuationSubring.smul_mem_pointwise_smul_iff (g := g) (x := x)).trans (Iff.symm this)

end GlobalTheory.ValConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGluedQuotientMapOfLocalQuotientsStatement
section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gluedQuotientMap_of_local_quotients : ∀ (S : Scheme.{0}) (𝒰 : S.OpenCover.{0}) (A H : Over S) [GrpObj A] [GrpObj H] (i : H ⟶ A)
    (B : ∀ j, Over (𝒰.X j)) (q : ∀ j, (Over.pullback (𝒰.f j)).obj A ⟶ B j) (b : ∀ j k, pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f k) ⟶ (B k).left)
    (G : Scheme.{0}) (F : G ⟶ S) (ψ : ∀ j, (B j).left ⟶ G),
    (∀ (j k : 𝒰.I₀) (T : Scheme.{0}) (y : T ⟶ pullback A.hom (𝒰.f j)) (z : T ⟶ pullback A.hom (𝒰.f k))
        (w : T ⟶ pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f k)), y ≫ pullback.fst _ _ = z ≫ pullback.fst _ _ →
        w ≫ pullback.fst _ _ = y ≫ (q j).left → w ≫ pullback.snd _ _ = z ≫ pullback.snd _ _ → w ≫ b j k = z ≫ (q k).left) →
    (∀ j k, pullback.fst _ _ ≫ ψ j = b j k ≫ ψ k) → (∀ j, ψ j ≫ F = (B j).hom ≫ 𝒰.f j) →
    ∃ Qm : A.left ⟶ G, Qm ≫ F = A.hom ∧ ∀ j, (q j).left ≫ ψ j = pullback.fst A.hom (𝒰.f j) ≫ Qm := by
  first | (exact @GlobalTheory.QuotGlue.exists_glueMap) | (exact GlobalTheory.QuotGlue.exists_glueMap) | (intros; apply GlobalTheory.QuotGlue.exists_glueMap  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInertiaElementRestrictingToFiniteGaloisStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inertia_element_restricting_to_finite_galois : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ (L : IntermediateField K Ω) [FiniteDimensional K L] [IsGalois K L] (τ : L ≃ₐ[K] L), τ ∈ inertia K (V.comap (algebraMap L Ω)) → ∃ σ ∈ inertia K V, ∀ y : L, σ (y : Ω) = (τ y : Ω) := by
  first | exact @GlobalTheory.InertiaRestrict.exists_mem_inertia_eq_on | exact GlobalTheory.InertiaRestrict.exists_mem_inertia_eq_on | (intros; apply GlobalTheory.InertiaRestrict.exists_mem_inertia_eq_on <;> assumption)
end

