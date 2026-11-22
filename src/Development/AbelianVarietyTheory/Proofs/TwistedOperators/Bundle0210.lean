import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0197
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0196
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0176
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0185
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0147
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0198
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0025
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0201
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousOfIwasawaContinuousStatement
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagLeviGroup GlobalTheory.GKModule GlobalTheory.RealInd
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_of_iwasawa_continuous : ∀ (n a : ℕ) (ε : Fin n → Bool) (j : Fin a → ℕ) (W : Flag n a), IsIsoFlag ε j W →
    ∀ (Y : Type) [TopologicalSpace Y] (F : UJ ε → Y),
      Continuous (fun q : parab ε W × KG ε => F ((q.1 : UJ ε) * (q.2 : UJ ε))) → Continuous F := by
  first | exact @GlobalTheory.ParabCompact.continuous_of_continuous_mul | exact GlobalTheory.ParabCompact.continuous_of_continuous_mul | (intros; apply GlobalTheory.ParabCompact.continuous_of_continuous_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousSectionLeviEquivariantStatement
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagLeviGroup GlobalTheory.GKModule GlobalTheory.RealInd
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_section_levi_equivariant : ∀ (n : ℕ) (ε : Fin n → Bool) (D : Datum ε), ∃ φ : UJ ε → D.V, Continuous φ ∧ φ 1 ≠ 0 ∧
    ∀ m ∈ leviOne ε D.W, m ∈ KG ε → ∀ g, φ (m * g) = D.σ (uMat m) (φ g) := by
  first | exact @GlobalTheory.RealInd.exists_kLevi_equivariant_ne_zero | exact GlobalTheory.RealInd.exists_kLevi_equivariant_ne_zero | (intros; apply GlobalTheory.RealInd.exists_kLevi_equivariant_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoordEquivApply
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.TrUnitLat

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ} (P : PPol σ r)

def powB : Module.Basis (Fin r) E (Fld P) :=
  (AdjoinRoot.powerBasis P.2.2.1.ne_zero).basis.reindex
    (finCongr ((AdjoinRoot.powerBasis_dim P.2.2.1.ne_zero).trans P.2.2.2.1))

def gramOne : Matrix (Fin r) (Fin r) E :=
  Matrix.of fun i j => Algebra.trace E (Fld P) (powB P j * star' P (powB P i))

variable (k : Type) [CommRing k] [Algebra F k]

def coordF (i : Fin r) : k ⊗[F] Fld P →ₗ[F] k ⊗[F] E :=
  LinearMap.lTensor k (((powB P).coord i).restrictScalars F)

theorem coordF_tmul (i : Fin r) (a : k) (z : Fld P) : coordF P k i (a ⊗ₜ[F] z) = a ⊗ₜ[F] (powB P).repr z i := rfl

theorem smul_eq_map_mul (c : k ⊗[F] E) (y : k ⊗[F] Fld P) :
    c • y = Algebra.TensorProduct.map (AlgHom.id F k) (IsScalarTower.toAlgHom F E (Fld P)) c * y :=
  Algebra.smul_def c y

theorem coordF_smul (i : Fin r) (c : k ⊗[F] E) (y : k ⊗[F] Fld P) : coordF P k i (c • y) = c * coordF P k i y := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | add c c' h h' => rw [add_smul, map_add, h, h', add_mul]
  | tmul a e =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' h h' => rw [smul_add, map_add, h, h', map_add, mul_add]
    | tmul a' z =>
      rw [smul_eq_map_mul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_mul_tmul, coordF_tmul,
        coordF_tmul, Algebra.TensorProduct.tmul_mul_tmul]
      congr 1
      change (powB P).repr (algebraMap E (Fld P) e * z) i = e * _
      rw [← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul]

def coordInv (w : Fin r → k ⊗[F] E) : k ⊗[F] Fld P := ∑ i, w i • ((1 : k) ⊗ₜ[F] powB P i)

theorem coordF_coordInv (w : Fin r → k ⊗[F] E) (j : Fin r) : coordF P k j (coordInv P k w) = w j := by
  simp only [coordInv, map_sum, coordF_smul, coordF_tmul, Module.Basis.repr_self]
  rw [Finset.sum_eq_single j (fun i _ h => by rw [Finsupp.single_apply, if_neg h, TensorProduct.tmul_zero, mul_zero])
    (by simp), Finsupp.single_eq_same, ← Algebra.TensorProduct.one_def, mul_one]

theorem coordInv_coordF (y : k ⊗[F] Fld P) : coordInv P k (fun i => coordF P k i y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp [coordInv]
  | add y y' h h' =>
    conv_rhs => rw [← h, ← h']
    simp only [coordInv, map_add, add_smul, Finset.sum_add_distrib]
  | tmul a z =>
    simp only [coordInv, coordF_tmul, smul_eq_map_mul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      mul_one, AlgHom.id_apply, IsScalarTower.coe_toAlgHom']
    rw [← TensorProduct.tmul_sum]
    congr 1
    conv_rhs => rw [← (powB P).sum_repr z]
    exact Finset.sum_congr rfl fun i _ => (Algebra.smul_def _ _).symm

def coordEquiv : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin r → k ⊗[F] E) where
  toFun y i := coordF P k i y
  map_add' y y' := funext fun i => map_add _ _ _
  map_smul' c y := funext fun i => coordF_smul P k i c y
  invFun := coordInv P k
  left_inv y := coordInv_coordF P k y
  right_inv w := funext fun j => coordF_coordInv P k w j

theorem coordEquiv_apply (y : k ⊗[F] Fld P) (i : Fin r) : coordEquiv P k y i = coordF P k i y := rfl

end GlobalTheory.TrUnitLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CxRootsInjective
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.TrEll.RealTorus

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ}
  (P : PPol σ r) {w : InfinitePlace F} (τ : EmbOver E w)

theorem cxRoots_root (i : Fin r) : eval₂ τ.1 (cxRoots τ.1 P i) P.1 = 0 := by
  rw [← eval_map, cxRoots_spec, eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

theorem cxRoots_injective : Function.Injective (cxRoots τ.1 P) := by
  have hs : (P.1.map τ.1).Separable := (PerfectField.separable_of_irreducible P.2.2.1).map
  have hn := nodup_roots hs
  rw [cxRoots_spec, ← Finset.prod_map_val,
    show Multiset.map (fun i => X - C (cxRoots τ.1 P i)) Finset.univ.val =
      Multiset.map (fun a => X - C a) (Finset.univ.val.map (cxRoots τ.1 P)) by rw [Multiset.map_map]; rfl,
    roots_multiset_prod_X_sub_C] at hn
  exact fun i j h => (Multiset.nodup_map_iff_inj_on Finset.univ.nodup).1 hn i (by simp) j (by simp) h

theorem finrank_Fld : Module.finrank E (Fld P) = r :=
  ((AdjoinRoot.powerBasis P.2.2.1.ne_zero).finrank.trans (AdjoinRoot.powerBasis_dim _)).trans P.2.2.2.1

def psiL (i : Fin r) : Fld P →+* ℂ := AdjoinRoot.lift τ.1 (cxRoots τ.1 P i) (cxRoots_root P τ i)

@[simp] theorem psiL_algebraMap (i : Fin r) (e : E) : psiL P τ i (algebraMap E (Fld P) e) = τ.1 e :=
  AdjoinRoot.lift_of _

@[simp] theorem psiL_alpha (i : Fin r) : psiL P τ i (alpha P) = cxRoots τ.1 P i := AdjoinRoot.lift_root _

theorem psiL_algebraMap_F (i : Fin r) (a : F) : psiL P τ i (algebraMap F (Fld P) a) = w.embedding a := by
  rw [IsScalarTower.algebraMap_apply F E (Fld P), psiL_algebraMap]
  exact RingHom.congr_fun τ.2 a

def Psi (i : Fin r) : w.Completion ⊗[F] Fld P →+* ℂ :=
  letI : Algebra F ℂ := w.embedding.toAlgebra
  (Algebra.TensorProduct.productMap
    ({ InfinitePlace.Completion.extensionEmbedding w with
        commutes' := fun a => InfinitePlace.Completion.extensionEmbedding_coe w ((WithAbs.equiv w.1).symm a) } :
      w.Completion →ₐ[F] ℂ)
    ({ psiL P τ i with commutes' := fun a => psiL_algebraMap_F P τ i a } : Fld P →ₐ[F] ℂ)).toRingHom

@[simp] theorem Psi_tmul (i : Fin r) (a : w.Completion) (y : Fld P) :
    Psi P τ i (a ⊗ₜ[F] y) = InfinitePlace.Completion.extensionEmbedding w a * psiL P τ i y := rfl

def PsiAll : w.Completion ⊗[F] Fld P →+* (Fin r → ℂ) := Pi.ringHom (Psi P τ)

@[simp] theorem PsiAll_apply (y : w.Completion ⊗[F] Fld P) (i : Fin r) : PsiAll P τ y i = Psi P τ i y := rfl

end GlobalTheory.TrEll.RealTorus
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DatumLevelHyperspecialOffFinitePlacesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.datumLevel_hyperspecial_off_finite_places : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (Lv : LevDat D.host.E ℂ V.rank) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))), IsBaseFrame V β Λ 1 → (∀ PP, PP ∈ Lv.Pg ∨ PP ∈ Lv.Q → PP.under (𝓞 D.host.F) ∈ Sb) → SphOff (levG V β Lv : Set (GA D V)) (levChi V β Lv) Sb ∧ (∀ g ∈ GfC V, g ∈ levG V β Lv ↔ (∃ k ∈ levG V β Lv, ∀ v ∈ Sb, projV V v g = projV V v k) ∧ ∀ v ∉ Sb, projV V v g ∈ Kv V v) ∧ (∀ g : GA D V, {v | projV V v g ∉ Kv V v}.Finite) ∧ ∀ k ∈ levG V β Lv, ‖levChi V β Lv k‖ = 1 := by
  first | exact @GlobalTheory.FinZeta.LevelOff.level_offS | exact GlobalTheory.FinZeta.LevelOff.level_offS | (intros; apply GlobalTheory.FinZeta.LevelOff.level_offS <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesPureInnerProductsTensorProduct
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Chain.RealIt

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem exists_finite_support {ι : Type} {E : ι → Type} [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)]
    (x : ⨂[ℂ] i, E i) : ∃ F : ∀ i, Submodule ℂ (E i), (∀ i, FiniteDimensional ℂ (F i)) ∧
      ∀ G : ∀ i, Submodule ℂ (E i), (∀ i, F i ≤ G i) →
        x ∈ LinearMap.range (PiTensorProduct.map fun i => (G i).subtype) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    refine ⟨fun i => ℂ ∙ f i, fun i => inferInstance, fun G hG => ?_⟩
    refine LinearMap.mem_range.mpr
      ⟨r • PiTensorProduct.tprod ℂ (fun i => (⟨f i, hG i (Submodule.mem_span_singleton_self (f i))⟩ : G i)), ?_⟩
    rw [map_smul, PiTensorProduct.map_tprod]
    rfl
  | add x y hx hy =>
    obtain ⟨F₁, h₁, k₁⟩ := hx
    obtain ⟨F₂, h₂, k₂⟩ := hy
    refine ⟨fun i => F₁ i ⊔ F₂ i, fun i => ?_, fun G hG => ?_⟩
    · haveI := h₁ i
      haveI := h₂ i
      infer_instance
    · exact add_mem (k₁ G fun i => le_trans le_sup_left (hG i)) (k₂ G fun i => le_trans le_sup_right (hG i))

theorem ellT_pure (M : DSModel V S) (w v : ∀ τ, M.H τ) :
    ellT M w (PiTensorProduct.tprod ℂ v) = ∏ τ, ⟪w τ, v τ⟫_ℂ := by
  unfold ellT
  rw [PiTensorProduct.lift.tprod]
  simp

private lemma eq_zero_of_ellT_map_eq_zero (M : DSModel V S) {K : D.what₂.Tau → Type} [∀ τ, NormedAddCommGroup (K τ)]
    [∀ τ, InnerProductSpace ℂ (K τ)] [hK : ∀ τ, FiniteDimensional ℂ (K τ)] (j : ∀ τ, K τ →ₗ[ℂ] M.H τ)
    (hj : ∀ τ a b, ⟪j τ a, j τ b⟫_ℂ = ⟪a, b⟫_ℂ) (z : ⨂[ℂ] τ, K τ)
    (hz : ∀ w, ellT M w (PiTensorProduct.map j z) = 0) : z = 0 := by
  classical
  let b := fun τ => stdOrthonormalBasis ℂ (K τ)
  let B := Basis.piTensorProduct (fun τ => (b τ).toBasis)
  have key : ∀ p, B.coord p = ellT M (fun τ => j τ (b τ (p τ))) ∘ₗ PiTensorProduct.map j := by
    intro p
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, Module.Basis.coord_apply, B,
      Basis.piTensorProduct_repr_tprod_apply, PiTensorProduct.map_tprod, ellT_pure, hj,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
  refine B.forall_coord_eq_zero_iff.mp fun p => ?_
  rw [key, LinearMap.comp_apply]
  exact hz _

theorem ellT_separates (M : DSModel V S) (x : ⨂[ℂ] τ, M.H τ) (hx : ∀ w, ellT M w x = 0) : x = 0 := by
  obtain ⟨F, hF, hx'⟩ := exists_finite_support x
  obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp (hx' F fun _ => le_rfl)
  have hy : y = 0 := eq_zero_of_ellT_map_eq_zero M (K := fun τ => F τ) (hK := hF) (fun τ => (F τ).subtype)
    (fun τ a b => rfl) y hx
  rw [hy, map_zero]

theorem inclT_injective (M : DSModel V S) : Function.Injective (inclT M) := by
  unfold inclT
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨F, hF, hy'⟩ := exists_finite_support y
  obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp (hy' F fun _ => le_rfl)
  have hz : z = 0 := eq_zero_of_ellT_map_eq_zero M (K := fun τ => F τ) (hK := hF)
    (fun τ => (M.sm τ).subtype ∘ₗ (F τ).subtype) (fun τ a b => rfl) z (by
      intro w
      rw [PiTensorProduct.map_comp, LinearMap.comp_apply, hy, map_zero])
  rw [hz, map_zero]

theorem fr_conj_mem (M : DSModel V S) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) : M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.MainNotions.S.UJset (M.ε τ) := by
  have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ)
  have hPQ : M.fr τ * (M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have hg' : gᴴ * gramAt D V τ * g = gramAt D V τ := hg
  rw [← M.fr_gram τ] at hg'
  show Formalism.REAL.inUJ (M.ε τ) _
  unfold Formalism.REAL.inUJ
  calc (M.fr τ * g * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * g * (M.fr τ)⁻¹)
      = ((M.fr τ)⁻¹)ᴴ * (gᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * g) * (M.fr τ)⁻¹ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = ((M.fr τ)⁻¹)ᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * (M.fr τ)⁻¹ := by rw [hg']
    _ = (M.fr τ * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.REAL.Jm (M.ε τ) := by rw [hPQ]; simp

open Classical in
theorem actT_pure (M : DSModel V S) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (v : ∀ ρ, M.H ρ) :
    actT M τ g (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ (Function.update v τ (M.rep τ g (v τ))) := by
  unfold actT
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext ρ
  by_cases h : ρ = τ
  · subst h
    simp
  · simp [Function.update_of_ne h]

theorem tensorLaw : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), TensorLaw M := by
  intro D V S M
  classical
  refine ⟨fun x hx => ellT_separates M x hx, inclT_injective M, ?_, ?_, ?_⟩
  · intro τ
    obtain ⟨-, -, ⟨⟨h1, -⟩, -⟩, -⟩ := M.ds τ
    have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ)
    have hr : M.rep τ 1 = 1 := by
      show M.σ τ (M.fr τ * 1 * (M.fr τ)⁻¹) = 1
      rw [Matrix.mul_one, Matrix.mul_nonsing_inv _ hd, h1]
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.id_apply]
    rw [actT_pure]
    simp [hr]
  · intro τ g hg g' hg'
    obtain ⟨-, -, ⟨⟨-, hmul⟩, -⟩, -⟩ := M.ds τ
    have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ)
    have hQP : (M.fr τ)⁻¹ * M.fr τ = 1 := Matrix.nonsing_inv_mul _ hd
    have hsplit : M.fr τ * (g * g') * (M.fr τ)⁻¹ =
        (M.fr τ * g * (M.fr τ)⁻¹) * (M.fr τ * g' * (M.fr τ)⁻¹) := by
      calc M.fr τ * (g * g') * (M.fr τ)⁻¹ = M.fr τ * g * ((M.fr τ)⁻¹ * M.fr τ) * g' * (M.fr τ)⁻¹ := by
            rw [hQP, Matrix.mul_one, Matrix.mul_assoc (M.fr τ) g g']
        _ = _ := by simp only [Matrix.mul_assoc]
    have hr : M.rep τ (g * g') = (M.rep τ g).comp (M.rep τ g') := by
      show M.σ τ (M.fr τ * (g * g') * (M.fr τ)⁻¹) = (M.σ τ (M.fr τ * g * (M.fr τ)⁻¹)).comp (M.σ τ (M.fr τ * g' * (M.fr τ)⁻¹))
      rw [hsplit]
      exact hmul _ (fr_conj_mem M τ hg) _ (fr_conj_mem M τ hg')
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply]
    rw [actT_pure, actT_pure, actT_pure, hr]
    congr 1
    simp [Function.update_idem]
  · intro τ g _ w
    obtain ⟨hc, -⟩ := M.ds τ
    haveI : CompleteSpace (M.H τ) := hc
    refine ⟨Function.update w τ (ContinuousLinearMap.adjoint (M.rep τ g) (w τ)), ?_⟩
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply]
    rw [actT_pure, ellT_pure, ellT_pure]
    refine Finset.prod_congr rfl fun ρ _ => ?_
    by_cases h : ρ = τ
    · subst h
      simp [ContinuousLinearMap.adjoint_inner_left]
    · simp [Function.update_of_ne h]

end GlobalTheory.Chain.RealIt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqExpFockGaussianFormOfHeisenbergDerivativeEqStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_exp_fockGaussianForm_of_heisenbergDerivative_eq : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (J : (V × V) →ₗ[ℝ] (V × V)), IsUnit (GlobalTheory.FockFamily.blockB J) → ∀ g : V → ℂ, Differentiable ℝ g →
    (∀ w x, GlobalTheory.GaussLine.dHeis β (J w) g x = Complex.I * GlobalTheory.GaussLine.dHeis β w g x) →
    ∀ x, g x = g 0 * Complex.exp (GlobalTheory.FockFamily.fockForm β J x x) := by
  first | exact @GlobalTheory.FockFamily.solution_eq_gauss | exact GlobalTheory.FockFamily.solution_eq_gauss | (intros; apply GlobalTheory.FockFamily.solution_eq_gauss <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqMulProdOfPartial
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.RealLine

structure CoverW {p q r s : ℕ} {T₁ : GrpData p q} {T₂ : GrpData r s} (R₁ : DSRep T₁) (R₂ : DSRep T₂)
    (B : Pol p q r s →ₗ[ℂ] R₂.HK.V →ₛₗ[starRingEnd ℂ] R₁.HK.V) : Prop where
  adj : ∀ P x, ∃ b, ∀ y, ⟪R₁.ι x, R₁.ι (B P y)⟫_ℂ = ⟪R₂.ι y, R₂.ι b⟫_ℂ
  src : ∀ Z ∈ upq p q, ∀ P y, B (fockAct1 p q r s Z P) y = R₁.HK.act Z (B P y)
  tgt : ∀ Z ∈ upq r s, ∀ P y, B (fockAct2 p q r s Z P) y + B P (R₂.HK.act Z y) = 0

variable {D : D7} {V W : HSp D} {S S' : D.what₂.Tau → SPar} (M : DSModel V S) (M' : DSModel W S')

structure SemiW (τ : D.what₂.Tau) (aS aT : ℚ) (A : PolF D W.rank V.rank →ₗ[ℂ] M'.sm τ →ₗ[ℂ] M.H τ) : Prop where
  bdd : ∀ φ u, ∃ c : ℝ, ∀ y : M'.sm τ, ‖⟪u, A φ y⟫_ℂ‖ ≤ c * ‖(y : M'.H τ)‖
  eqK : ∀ h ∈ Formalism.REAL.Kset (M.ε τ), ∀ φ, ∃ φ', φ'.totalDegree ≤ φ.totalDegree ∧ ∀ y, A φ' y = M.σ τ h (A φ y)
  invK : ∀ k ∈ Formalism.REAL.Kset (M'.ε τ), ∀ φ, ∃ φ', φ'.totalDegree ≤ φ.totalDegree ∧
    ∀ y y' : M'.sm τ, (y' : M'.H τ) = M'.σ τ k y → A φ' y' = A φ y
  src : ∀ X ∈ lieAt V τ, ∀ φ y u, HasDerivAt (fun t : ℝ => ⟪u, M.rep τ (NormedSpace.exp (t • X)) (A φ y)⟫_ℂ)
    ⟪u, A (srcOp M M' τ aT X φ) y⟫_ℂ 0
  tgt : ∀ Y ∈ lieAt W τ, ∀ φ (y y' : M'.sm τ),
    HasDerivAt (fun t : ℝ => M'.rep τ (NormedSpace.exp (t • Y)) y) (y' : M'.H τ) 0 →
      A (tgtOp M M' τ aS Y φ) y + A φ y' = 0

structure LocW (τ : D.what₂.Tau) (aS aT : ℚ) (A : LPol W.rank V.rank →ₗ[ℂ] M'.sm τ →ₗ[ℂ] M.H τ) : Prop where
  kS : ∀ P y, Formalism.MainNotions.S.IsKFin (M.ε τ) (M.σ τ) (A P y)
  kT : ∀ P u, ∃ b : M'.H τ, Formalism.MainNotions.S.IsKFin (M'.ε τ) (M'.σ τ) b ∧ ∀ y : M'.sm τ, ⟪u, A P y⟫_ℂ = ⟪b, (y : M'.H τ)⟫_ℂ
  src : ∀ X ∈ lieAt V τ, ∀ P y u, HasDerivAt (fun t : ℝ => ⟪u, M.rep τ (NormedSpace.exp (t • X)) (A P y)⟫_ℂ)
    ⟪u, A (locS (M.ε τ) (M'.ε τ) ((M.fr τ * X * (M.fr τ)⁻¹).map (starRingEnd ℂ)) P - ((aT : ℂ) * X.trace) • P) y⟫_ℂ 0
  tgt : ∀ Y ∈ lieAt W τ, ∀ P (y y' : M'.sm τ),
    HasDerivAt (fun t : ℝ => M'.rep τ (NormedSpace.exp (t • Y)) y) (y' : M'.H τ) 0 →
      A (locT (M.ε τ) (M'.ε τ) (M'.fr τ * Y * (M'.fr τ)⁻¹) P + ((aS : ℂ) * Y.trace) • P) y + A P y' = 0

theorem eq_mul_prod_of_partial {ι : Type} [Fintype ι] [DecidableEq ι] {A : ι → Type} (l : ∀ i, A i → ℂ)
    (F : (∀ i, A i) → ℂ) (h : ∀ i a, ∃ c : ℂ, ∀ x, F (Function.update a i x) = c * l i x) :
    ∃ c : ℂ, ∀ a, F a = c * ∏ i, l i (a i) := by

  have key : ∀ (a : ∀ i, A i) (i : ι) (x : A i),
      F (Function.update a i x) * l i (a i) = F a * l i x := by
    intro a i x
    obtain ⟨c, hc⟩ := h i a
    have h1 := hc (a i)
    rw [Function.update_eq_self] at h1
    rw [hc x, h1]
    ring
  by_cases hF : ∀ a, F a = 0
  · exact ⟨0, fun a => by simp [hF a]⟩
  push_neg at hF
  obtain ⟨a₀, ha₀⟩ := hF
  have hl : ∀ i, l i (a₀ i) ≠ 0 := by
    intro i hi
    obtain ⟨c, hc⟩ := h i a₀
    have h1 := hc (a₀ i)
    rw [Function.update_eq_self, hi, mul_zero] at h1
    exact ha₀ h1

  have main : ∀ s : Finset ι, ∀ a : ∀ i, A i, (∀ j, j ∉ s → a j = a₀ j) →
      F a * ∏ j ∈ s, l j (a₀ j) = F a₀ * ∏ j ∈ s, l j (a j) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro a ha
      rw [show a = a₀ from funext fun j => ha j (by simp)]
    | @insert i s hi ih =>
      intro a ha
      have hoff : ∀ j, j ∉ s → Function.update a i (a₀ i) j = a₀ j := by
        intro j hj
        by_cases hji : j = i
        · subst hji
          simp
        · rw [Function.update_of_ne hji]
          exact ha j (by simp [hji, hj])
      have e1 := ih _ hoff
      have e2 := key (Function.update a i (a₀ i)) i (a i)
      simp only [Function.update_idem, Function.update_eq_self, Function.update_self] at e2
      have hprod : ∏ j ∈ s, l j (Function.update a i (a₀ i) j) = ∏ j ∈ s, l j (a j) :=
        Finset.prod_congr rfl fun j hj => by
          have hji : j ≠ i := fun e => hi (e ▸ hj)
          rw [Function.update_of_ne hji]
      rw [hprod] at e1
      rw [Finset.prod_insert hi, Finset.prod_insert hi]
      calc F a * (l i (a₀ i) * ∏ j ∈ s, l j (a₀ j))
          = (F a * l i (a₀ i)) * ∏ j ∈ s, l j (a₀ j) := by ring
        _ = (F (Function.update a i (a₀ i)) * l i (a i)) * ∏ j ∈ s, l j (a₀ j) := by rw [e2]
        _ = l i (a i) * (F (Function.update a i (a₀ i)) * ∏ j ∈ s, l j (a₀ j)) := by ring
        _ = l i (a i) * (F a₀ * ∏ j ∈ s, l j (a j)) := by rw [e1]
        _ = F a₀ * (l i (a i) * ∏ j ∈ s, l j (a j)) := by ring
  have hP : ∏ j, l j (a₀ j) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hl j
  refine ⟨F a₀ / ∏ j, l j (a₀ j), fun a => ?_⟩
  rw [div_mul_eq_mul_div, eq_div_iff hP]
  exact main Finset.univ a fun j hj => absurd (Finset.mem_univ j) hj

end GlobalTheory.Chain.RealLine

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EquivariantOfGeneratorOneParameterGroupStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equivariant_of_generator_oneParameterGroup : ∀ (σ Z H : Type) [Finite σ] [AddCommGroup H] [Module ℂ H] (pt : MvPolynomial σ ℂ →ₗ[ℂ] (Z → ℂ)) (R : ℝ → Module.End ℂ (Z → ℂ)) (L : Module.End ℂ (MvPolynomial σ ℂ)) (U : ℝ → Module.End ℂ H) (B : MvPolynomial σ ℂ →ₗ[ℂ] H) (Λ : Set (H →ₗ[ℂ] ℂ)), Function.Injective pt → R 0 = 1 → (∀ s t, R (s + t) = R s * R t) → (∀ t φ, ∃ ψ, ψ.totalDegree ≤ φ.totalDegree ∧ R t (pt φ) = pt ψ) → (∀ φ z, HasDerivAt (fun t : ℝ => R t (pt φ) z) (pt (L φ) z) 0) → U 0 = 1 → (∀ s t, U (s + t) = U s * U t) → (∀ x, (∀ l ∈ Λ, l x = 0) → x = 0) → (∀ l ∈ Λ, ∀ t, l ∘ₗ U t ∈ Λ) → (∀ l ∈ Λ, ∀ φ, HasDerivAt (fun t : ℝ => l (U t (B φ))) (l (B (L φ))) 0) → ∀ φ φ', pt φ' = R 1 (pt φ) → B φ' = U 1 (B φ) := by
  first | exact @GlobalTheory.OneParamEquivariance.equivariant_of_generator | exact GlobalTheory.OneParamEquivariance.equivariant_of_generator | (intros; apply GlobalTheory.OneParamEquivariance.equivariant_of_generator <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralInverseAtSplitPlacesOfUnitsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_inverse_at_splitPlaces_of_units : ∀ {D : D7} (Z : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Z → ∀ (a : EAf D) (ha : a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), (∀ PP ∈ Z, IsUnit (Formalism.L2.DIV.resS D.host.F PP ⟨a, ha⟩)) → ∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, a * w * toEAf D e = toEAf D e := by
  first | exact @GlobalTheory.LocalInvIdem.exists_inv | exact GlobalTheory.LocalInvIdem.exists_inv | (intros; apply GlobalTheory.LocalInvIdem.exists_inv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeightBruhatFundamentalDomainCentralizerStatement
section
open MeasureTheory Set GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weight_bruhat_fundamental_domain_centralizer : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (Γ : Subgroup H) [DiscreteTopology Γ] (γ : H), IsMulCommutative (cent γ) → ∀ (μ : Measure H) [μ.IsHaarMeasure] (dt : Measure (cent γ)) [dt.IsHaarMeasure] (𝓣 : Set (cent γ)), IsFundamentalDomain (Γ.subgroupOf (cent γ)) 𝓣 dt → ∃ α : H → ℝ≥0∞, Measurable α ∧ (∀ y, ∑' h : Γ.subgroupOf (cent γ), α (((h : cent γ) : H) * y) = 1) ∧ ∀ ψ : H → ℝ≥0∞, Measurable ψ → LeftInv (cent γ) ψ → ∫⁻ y, α y * ψ y ∂μ = dt 𝓣 * ∫⁻ q, descend (cent γ) ψ q ∂(quotMeas (cent γ) dt μ) := by
  first | exact @GlobalTheory.WeightUnfold.exists_weight | exact GlobalTheory.WeightUnfold.exists_weight | (intros; apply GlobalTheory.WeightUnfold.exists_weight <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacquetWordMultiplicityAdditiveJordanHolderStatement
section
open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquetWordMultiplicity_additive_jordanHolder : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (h : HasFiniteLength π), IsSmooth π → ∀ w : List ℂˣ, wordMult π w = (cls π h).sum fun c a => (a.toNat : ℕ∞) * wordMult c.rep.ρ w := by
  first | exact @GlobalTheory.SmGL.Exponents.Additive.wordMult_additive | exact GlobalTheory.SmGL.Exponents.Additive.wordMult_additive | (intros; apply GlobalTheory.SmGL.Exponents.Additive.wordMult_additive <;> assumption)
end

