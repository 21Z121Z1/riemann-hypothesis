import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0013
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMultilinearSlotwiseExtensionOfEquivariant
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.LatticeCosetUniformizer
import Formalism.LocalToGlobal.IndefiniteReal.GramCEqTranspose
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0012

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsUnitDetAddMulOfFromBlocksLocalRingStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isUnit_det_add_mul_of_fromBlocks_localRing : ∀ {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (A B C D : Matrix (Fin n) (Fin n) O),
    IsUnit (Matrix.fromBlocks A B C D).det → ∃ X : Matrix (Fin n) (Fin n) O, IsUnit (A + X * C).det := by
  first | exact @GlobalTheory.BlockInvertibleLocal.exists_isUnit_det_add_mul | exact GlobalTheory.BlockInvertibleLocal.exists_isUnit_det_add_mul | (intros; apply GlobalTheory.BlockInvertibleLocal.exists_isUnit_det_add_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMaximalOperatorStableOfFinsetGenerating
section
open scoped TensorProduct

namespace GlobalTheory.TensHead

theorem exists_maximal_stab_of_finset {V : Type} [AddCommGroup V] [Module ℂ V]
    (G : Set (Module.End ℂ V)) (R : Submodule ℂ V) (F : Finset V)
    (hF : ∀ N : Submodule ℂ V, R ≤ N → Stab G N → (↑F : Set V) ⊆ ↑N → N = ⊤) :
    ∀ N : Submodule ℂ V, R ≤ N → Stab G N → N ≠ ⊤ →
      ∃ N' : Submodule ℂ V, N ≤ N' ∧ Stab G N' ∧ N' ≠ ⊤ ∧
        ∀ U : Submodule ℂ V, Stab G U → N' ≤ U → U = N' ∨ U = ⊤ := by
  intro N hRN hN hNtop
  let s : Set (Submodule ℂ V) := {U | R ≤ U ∧ Stab G U ∧ ¬ (↑F : Set V) ⊆ ↑U}
  have hcomp := (CompleteLattice.isCompactElement_iff_le_of_directed_sSup_le _ _).1
    (Submodule.finset_span_isCompactElement (R := ℂ) F)
  have hNs : N ∈ s := ⟨hRN, hN, fun h => hNtop (hF N hRN hN h)⟩
  obtain ⟨M, hNM, hM⟩ := zorn_le_nonempty₀ s (by
    intro c hcs hc y hy
    have hne : c.Nonempty := ⟨y, hy⟩
    have hdir : DirectedOn (· ≤ ·) c := hc.directedOn
    refine ⟨sSup c, ⟨le_trans (hcs hy).1 (le_sSup hy), ?_, ?_⟩, fun z hz => le_sSup hz⟩
    · intro g hg x hx
      obtain ⟨U, hU, hxU⟩ := (Submodule.mem_sSup_of_directed hne hdir).1 hx
      exact (Submodule.mem_sSup_of_directed hne hdir).2 ⟨U, hU, (hcs hU).2.1 g hg x hxU⟩
    · intro hFc
      have hspan : Submodule.span ℂ (↑F : Set V) ≤ sSup c := Submodule.span_le.2 hFc
      obtain ⟨U, hU, hle⟩ := hcomp c hne hdir hspan
      exact (hcs hU).2.2 (Submodule.span_le.1 hle)) N hNs
  refine ⟨M, hNM, hM.prop.2.1, fun h => hM.prop.2.2 (by rw [h]; exact fun _ _ => trivial), ?_⟩
  intro U hU hMU
  by_cases hFU : (↑F : Set V) ⊆ ↑U
  · exact Or.inr (hF U (le_trans hM.prop.1 hMU) hU hFU)
  · exact Or.inl (le_antisymm (hM.2 ⟨le_trans hM.prop.1 hMU, hU, hFU⟩ hMU) hMU)

end GlobalTheory.TensHead
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMultilinearSlotwiseExtensionOfEquivariantStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_multilinear_positionwise_extension_of_equivariant : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {H : ι → Type} [∀ τ, AddCommGroup (H τ)] [∀ τ, Module ℂ (H τ)]
    {E : Type} [AddCommGroup E] [Module ℂ E] (A B : ∀ τ, Submodule ℂ (H τ)), (∀ τ, A τ ≤ B τ) →
    ∀ (Rk Rg : ∀ τ, Set ((H τ → H τ) × (E →ₗ[ℂ] E))),
    (∀ τ, ∀ r ∈ Rk τ, ∀ x ∈ A τ, r.1 x ∈ A τ) → (∀ τ, ∀ r ∈ Rg τ, ∀ x ∈ B τ, r.1 x ∈ B τ) →
    ∀ (C : ∀ τ, Submodule ℂ (H τ →ₗ[ℂ] E)),
    (∀ τ, ∀ L ∈ C τ, ∀ L' : H τ →ₗ[ℂ] E, (∀ x ∈ B τ, L' x = L x) → L' ∈ C τ) →
    (∀ τ (L : H τ →ₗ[ℂ] E), (∀ r ∈ Rk τ, ∀ x ∈ A τ, L (r.1 x) = r.2 (L x)) →
      ∃ L' ∈ C τ, (∀ r ∈ Rg τ, ∀ x ∈ B τ, L' (r.1 x) = r.2 (L' x)) ∧ ∀ x ∈ A τ, L' x = L x) →
    (∀ τ, ∀ L ∈ C τ, (∀ x ∈ A τ, L x = 0) → ∀ x ∈ B τ, L x = 0) →
    (∀ τ τ', τ ≠ τ' → ∀ r ∈ Rk τ ∪ Rg τ, ∀ L ∈ C τ', r.2 ∘ₗ L ∈ C τ') →
    (∀ τ τ', τ ≠ τ' → ∀ r ∈ Rk τ ∪ Rg τ, ∀ r' ∈ Rg τ', r.2 ∘ₗ r'.2 = r'.2 ∘ₗ r.2) →
    (∀ τ τ', τ ≠ τ' → ∀ F : H τ →ₗ[ℂ] H τ' →ₗ[ℂ] E, (∀ w ∈ B τ, F w ∈ C τ') → (∀ a ∈ A τ', F.flip a ∈ C τ) →
      ∀ b ∈ B τ', F.flip b ∈ C τ) →
    ∀ T₀ : MultilinearMap ℂ H E,
    (∀ τ (u : ∀ τ, H τ), (∀ τ', τ' ≠ τ → u τ' ∈ A τ') → ∀ r ∈ Rk τ, ∀ x ∈ A τ,
      T₀ (Function.update u τ (r.1 x)) = r.2 (T₀ (Function.update u τ x))) →
    ∃ T : MultilinearMap ℂ H E, (∀ u, (∀ τ, u τ ∈ A τ) → T u = T₀ u) ∧
      ∀ τ (u : ∀ τ, H τ), (∀ τ', τ' ≠ τ → u τ' ∈ B τ') →
        T.toLinearMap u τ ∈ C τ ∧
          ∀ r ∈ Rg τ, ∀ x ∈ B τ, T (Function.update u τ (r.1 x)) = r.2 (T (Function.update u τ x)) := by
  first | exact @GlobalTheory.FactorwiseExtension.exists_multilinear_positionwise_extension | exact GlobalTheory.FactorwiseExtension.exists_multilinear_positionwise_extension | (intros; apply GlobalTheory.FactorwiseExtension.exists_multilinear_positionwise_extension <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOfMemDoubleCosetK
section
namespace GlobalTheory.MinusculeCosetsProof

open Matrix IsLocalRing GlobalTheory.IndefiniteRowSideFullHecke.LatticeCosetUniformizer

section General

variable {O F : Type} [CommRing O] [Field F] [Algebra O F] {n : ℕ}

def intLattice (F : Type) [Field F] [Algebra O F] (A : Matrix (Fin n) (Fin n) O) :
    Submodule O (Fin n → F) :=
  LinearMap.range ((inclVec O F n).comp A.mulVecLin)

theorem mem_intLattice (A : Matrix (Fin n) (Fin n) O) (x : Fin n → F) :
    x ∈ intLattice F A ↔ ∃ v, inclVec O F n (A *ᵥ v) = x := Iff.rfl

theorem inclVec_apply (v : Fin n → O) (i : Fin n) : inclVec O F n v i = algebraMap O F (v i) := rfl

theorem inclVec_mulVec (A : Matrix (Fin n) (Fin n) O) (v : Fin n → O) :
    inclVec O F n (A *ᵥ v) = A.map (algebraMap O F) *ᵥ inclVec O F n v := by
  funext i
  simp [inclVec_apply, Matrix.mulVec, dotProduct, map_sum]

theorem mem_scaleBy (a : O) (L : Submodule O (Fin n → F)) (x : Fin n → F) :
    x ∈ scaleBy O a L ↔ ∃ y ∈ L, a • y = x := Iff.rfl

theorem le_of_scaleBy_le {a : O} (ha : algebraMap O F a ≠ 0) {L L' : Submodule O (Fin n → F)}
    (h : scaleBy O a L ≤ scaleBy O a L') : L ≤ L' := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := (mem_scaleBy a L' _).1 (h ((mem_scaleBy a L _).2 ⟨x, hx, rfl⟩))
  have : y = x := by
    funext i
    have := congrFun hxy i
    simp only [Pi.smul_apply, Algebra.smul_def] at this
    exact mul_left_cancel₀ ha this
  exact this ▸ hy

theorem scaleBy_latticeOf {a : O} {t : GL (Fin n) F} {D : Matrix (Fin n) (Fin n) O}
    (hD : a • (t : Matrix (Fin n) (Fin n) F) = D.map (algebraMap O F)) (k : GL (Fin n) O) :
    scaleBy O a (latticeOf O (Matrix.GeneralLinearGroup.map (algebraMap O F) k * t)) =
      intLattice F ((k : Matrix (Fin n) (Fin n) O) * D) := by
  have key : ∀ v : Fin n → O,
      a • (((Matrix.GeneralLinearGroup.map (algebraMap O F) k * t : GL (Fin n) F) :
        Matrix (Fin n) (Fin n) F) *ᵥ (fun i => algebraMap O F (v i))) =
      inclVec O F n (((k : Matrix (Fin n) (Fin n) O) * D) *ᵥ v) := by
    intro v
    rw [inclVec_mulVec, Matrix.map_mul, ← hD, Matrix.mul_smul, Matrix.smul_mulVec]
    rfl
  ext x
  rw [mem_scaleBy, mem_intLattice]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨v, rfl⟩ := (mem_latticeOf O _ _).1 hy
    exact ⟨v, (key v).symm⟩
  · rintro ⟨v, rfl⟩
    exact ⟨_, (mem_latticeOf O _ _).2 ⟨v, rfl⟩, key v⟩

theorem exists_of_mem_doubleCosetK {t g : GL (Fin n) F} (hg : g ∈ doubleCosetK O t) :
    ∃ k : GL (Fin n) O,
      latticeOf O g = latticeOf O (Matrix.GeneralLinearGroup.map (algebraMap O F) k * t) := by
  obtain ⟨_, ⟨k, rfl⟩, k₂, hk₂, rfl⟩ := hg
  exact ⟨k, latticeOf_mul O _ _ hk₂⟩

theorem intLattice_le_std (A : Matrix (Fin n) (Fin n) O) : intLattice F A ≤ stdLattice O F n := by
  rintro _ ⟨v, rfl⟩
  exact ⟨A *ᵥ v, rfl⟩

theorem scaleBy_std_le_intLattice {ϖ : O} {D D' : Matrix (Fin n) (Fin n) O}
    (h : D * D' = ϖ • (1 : Matrix (Fin n) (Fin n) O)) (k : GL (Fin n) O) :
    scaleBy O ϖ (stdLattice O F n) ≤ intLattice F ((k : Matrix (Fin n) (Fin n) O) * D) := by
  intro x hx
  obtain ⟨_, ⟨v, rfl⟩, rfl⟩ := (mem_scaleBy _ _ _).1 hx
  refine ⟨(D' * ((k⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O)) *ᵥ v, ?_⟩
  rw [← map_smul]
  change inclVec O F n _ = _
  congr 1
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.mul_assoc, ← Matrix.mul_assoc D, h,
    Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Units.mul_inv, Matrix.smul_mulVec,
    Matrix.one_mulVec]

theorem exists_int_of_latticeOf_le {g g' : GL (Fin n) F} (h : latticeOf O g' ≤ latticeOf O g) :
    ∃ A : Matrix (Fin n) (Fin n) O,
      ((g⁻¹ * g' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = A.map (algebraMap O F) := by
  have : ∀ j : Fin n, ∃ v : Fin n → O,
      (g : Matrix (Fin n) (Fin n) F) *ᵥ (fun i => algebraMap O F (v i)) =
        (g' : Matrix (Fin n) (Fin n) F) *ᵥ
          (fun i => algebraMap O F ((Pi.single j 1 : Fin n → O) i)) := fun j =>
    (mem_latticeOf O _ _).1 (h ((mem_latticeOf O _ _).2 ⟨_, rfl⟩))
  choose v hv using this
  refine ⟨Matrix.of fun i j => v j i, ?_⟩
  have h2 : (g : Matrix (Fin n) (Fin n) F) *
      (Matrix.of fun i j => v j i).map (algebraMap O F) = g' := by
    ext i j
    have := congrFun (hv j) i
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, Pi.single_apply, apply_ite] using this
  rw [Units.val_mul, ← h2, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]

theorem mk_eq_of_latticeOf_eq (hinj : Function.Injective (algebraMap O F)) {g g' : GL (Fin n) F}
    (h : latticeOf O g = latticeOf O g') :
    (QuotientGroup.mk g : GL (Fin n) F ⧸ integralGL O F n) = QuotientGroup.mk g' := by
  rw [QuotientGroup.eq]
  obtain ⟨A, hA⟩ := exists_int_of_latticeOf_le h.ge
  obtain ⟨B, hB⟩ := exists_int_of_latticeOf_le h.le
  have hAB : A * B = 1 := by
    apply Matrix.map_injective hinj
    simp only [Matrix.map_mul]
    rw [← hA, ← hB, ← Units.val_mul]
    simp
  have hBA : B * A = 1 := by
    apply Matrix.map_injective hinj
    simp only [Matrix.map_mul]
    rw [← hA, ← hB, ← Units.val_mul]
    simp
  refine ⟨⟨A, B, hAB, hBA⟩, ?_⟩
  ext1
  exact hA.symm

variable [IsLocalRing O]

theorem inclVec_injective (hinj : Function.Injective (algebraMap O F)) :
    Function.Injective (inclVec O F n) := by
  intro v w h
  funext i
  exact hinj (congrFun h i)

theorem residue_mulVec (A : Matrix (Fin n) (Fin n) O) (v : Fin n → O) :
    (fun i => residue O ((A *ᵥ v) i)) = A.map (residue O) *ᵥ fun i => residue O (v i) := by
  funext i
  simp [Matrix.mulVec, dotProduct, map_sum]

theorem reduction_intLattice (hinj : Function.Injective (algebraMap O F))
    (A : Matrix (Fin n) (Fin n) O) :
    reduction O (intLattice F A) = LinearMap.range (A.map (residue O)).mulVecLin := by
  ext w
  constructor
  · rintro ⟨v, ⟨u, hu⟩, rfl⟩
    have : A *ᵥ u = v := inclVec_injective hinj hu
    subst this
    exact ⟨_, (residue_mulVec A u).symm⟩
  · rintro ⟨u, rfl⟩
    choose v hv using fun i => residue_surjective (u i)
    refine ⟨A *ᵥ v, ⟨v, rfl⟩, ?_⟩
    rw [residue_mulVec, Matrix.mulVecLin_apply]
    congr 1
    exact funext hv

theorem le_of_reduction_le {ϖ : O} (hm : ∀ x ∈ maximalIdeal O, ϖ ∣ x)
    {L L' : Submodule O (Fin n → F)} (h1 : L ≤ stdLattice O F n)
    (h2 : scaleBy O ϖ (stdLattice O F n) ≤ L') (h : reduction O L ≤ reduction O L') : L ≤ L' := by
  intro x hx
  obtain ⟨v, rfl⟩ := h1 hx
  obtain ⟨v', hv', e⟩ := h (show (fun i => residue O (v i)) ∈ reduction O L from ⟨v, hx, rfl⟩)
  have : ∀ i, ∃ c, v i - v' i = ϖ * c := fun i => hm _ (by
    rw [← residue_eq_zero_iff, map_sub, sub_eq_zero]
    exact (congrFun e i).symm)
  choose c hc using this
  have hv : v = v' + ϖ • c := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ← hc i]
    ring
  rw [hv, map_add, map_smul]
  exact L'.add_mem hv' (h2 ((mem_scaleBy _ _ _).2 ⟨_, ⟨c, rfl⟩, rfl⟩))

theorem isUnit_det_map (k : GL (Fin n) O) :
    IsUnit ((k : Matrix (Fin n) (Fin n) O).map (residue O)).det := by
  have := (Matrix.GeneralLinearGroup.map (residue O) k).isUnit
  exact (Matrix.isUnit_iff_isUnit_det _).1 this

theorem exists_lift (M : Matrix (Fin n) (Fin n) (ResidueField O)) (hM : IsUnit M.det) :
    ∃ k : GL (Fin n) O, (k : Matrix (Fin n) (Fin n) O).map (residue O) = M := by
  choose A hA using fun i j => residue_surjective (M i j)
  have hAM : (Matrix.of A).map (residue O) = M := by
    ext i j
    exact hA i j
  have : IsUnit (Matrix.of A).det := by
    rw [← residue_ne_zero_iff_isUnit, RingHom.map_det, RingHom.mapMatrix_apply, hAM]
    exact hM.ne_zero
  obtain ⟨k, hk⟩ := (Matrix.isUnit_iff_isUnit_det _).2 this
  exact ⟨k, hk ▸ hAM⟩

theorem exists_range_eq {K : Type} [Field K] (D : Matrix (Fin n) (Fin n) K)
    (U : Submodule K (Fin n → K)) (hU : Module.finrank K U = D.rank) :
    ∃ M : Matrix (Fin n) (Fin n) K, IsUnit M.det ∧ LinearMap.range (M * D).mulVecLin = U := by
  have f : LinearMap.range D.mulVecLin ≃ₗ[K] U := LinearEquiv.ofFinrankEq _ _ hU.symm
  obtain ⟨e, he⟩ := Submodule.exists_linearEquiv_restrict_eq f
  refine ⟨LinearMap.toMatrix' (e : (Fin n → K) →ₗ[K] (Fin n → K)), ?_, ?_⟩
  · rw [LinearMap.det_toMatrix']
    exact e.isUnit_det'
  · rw [Matrix.mulVecLin_mul, ← Matrix.toLin'_apply' (LinearMap.toMatrix' _),
      Matrix.toLin'_toMatrix', LinearMap.range_comp]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have := he ⟨y, hy⟩
      simp only [LinearEquiv.coe_coe]
      rw [← this]
      exact (f ⟨y, hy⟩).2
    · intro hx
      refine ⟨(f.symm ⟨x, hx⟩ : _), (f.symm ⟨x, hx⟩).2, ?_⟩
      simp only [LinearEquiv.coe_coe]
      rw [← he]
      simp

theorem core (hinj : Function.Injective (algebraMap O F)) {ϖ : O}
    (hm : ∀ x ∈ maximalIdeal O, ϖ ∣ x) {a : O} (ha : algebraMap O F a ≠ 0)
    {t : GL (Fin n) F} {D D' : Matrix (Fin n) (Fin n) O}
    (hD : a • (t : Matrix (Fin n) (Fin n) F) = D.map (algebraMap O F))
    (h : D * D' = ϖ • (1 : Matrix (Fin n) (Fin n) O)) :
    (∀ g ∈ doubleCosetK O t, scaleBy O ϖ (stdLattice O F n) ≤ scaleBy O a (latticeOf O g) ∧
      scaleBy O a (latticeOf O g) ≤ stdLattice O F n) ∧
    Set.BijOn (fun c => reduction O (scaleBy O a (latticeOfCoset O c))) (cosetsIn O t)
      {U : Submodule (ResidueField O) (Fin n → ResidueField O) |
        Module.finrank (ResidueField O) U = (D.map (residue O)).rank} := by
  have h1 : ∀ g ∈ doubleCosetK O t,
      scaleBy O ϖ (stdLattice O F n) ≤ scaleBy O a (latticeOf O g) ∧
      scaleBy O a (latticeOf O g) ≤ stdLattice O F n := by
    intro g hg
    obtain ⟨k, hk⟩ := exists_of_mem_doubleCosetK hg
    rw [hk, scaleBy_latticeOf hD]
    exact ⟨scaleBy_std_le_intLattice h k, intLattice_le_std _⟩
  refine ⟨h1, ?_, ?_, ?_⟩
  · rintro _ ⟨g, hg, rfl⟩
    obtain ⟨k, hk⟩ := exists_of_mem_doubleCosetK hg
    simp only [Set.mem_setOf_eq, latticeOfCoset_mk]
    rw [hk, scaleBy_latticeOf hD, reduction_intLattice hinj, Matrix.map_mul]
    exact Matrix.rank_mul_eq_right_of_isUnit_det _ _ (isUnit_det_map k)
  · rintro _ ⟨g, hg, rfl⟩ _ ⟨g', hg', rfl⟩ e
    simp only [latticeOfCoset_mk] at e
    apply mk_eq_of_latticeOf_eq hinj
    exact le_antisymm
      (le_of_scaleBy_le ha (le_of_reduction_le hm (h1 g hg).2 (h1 g' hg').1 e.le))
      (le_of_scaleBy_le ha (le_of_reduction_le hm (h1 g' hg').2 (h1 g hg).1 e.ge))
  · intro U hU
    obtain ⟨M, hM, hMU⟩ := exists_range_eq _ U hU
    obtain ⟨k, rfl⟩ := exists_lift M hM
    refine ⟨QuotientGroup.mk (Matrix.GeneralLinearGroup.map (algebraMap O F) k * t),
      ⟨_, ⟨_, ⟨k, rfl⟩, 1, one_mem _, (mul_one _).symm⟩, rfl⟩, ?_⟩
    simp only [latticeOfCoset_mk]
    rw [scaleBy_latticeOf hD, reduction_intLattice hinj, Matrix.map_mul, hMU]

end General

end GlobalTheory.MinusculeCosetsProof
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSmulMemSupLattice
section
open NumberField IsDedekindDomain Formalism.IndefR.Arith

namespace GlobalTheory.DenominatorExistenceTwistedOperators

theorem abs_eq_one {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K)
    (hx : x ∉ v.asIdeal) : FinitePlace.mk v (x : K) = 1 := by
  rw [FinitePlace.mk_apply]
  have h1 := FinitePlace.norm_le_one K v x
  have h2 := (FinitePlace.norm_lt_one_iff_mem K v x).not.mpr hx
  exact le_antisymm h1 (not_lt.mp h2)

theorem exists_prime_to_part {R : Type} [CommRing R] [IsDedekindDomain R] (p : HeightOneSpectrum R) (d : R)
    (hd : d ≠ 0) : ∃ s ∉ p.asIdeal, ∀ q : HeightOneSpectrum R, q ≠ p → ∃ t ∉ q.asIdeal, ∃ u, t * s = u * d := by
  have hI : Ideal.span {d} ≠ 0 := by
    simpa [Ideal.span_singleton_eq_bot] using hd
  obtain ⟨n, J, hJ, hfac⟩ := WfDvdMonoid.max_power_factor hI p.irreducible
  rw [Ideal.dvd_iff_le] at hJ
  obtain ⟨s, hsJ, hsp⟩ := SetLike.not_le_iff_exists.mp hJ
  refine ⟨s, hsp, fun q hq => ?_⟩
  have hnle : ¬ p.asIdeal ^ n ≤ q.asIdeal := by
    intro h
    have := q.isPrime
    have h1 : p.asIdeal ≤ q.asIdeal := Ideal.IsPrime.le_of_pow_le h
    exact hq (HeightOneSpectrum.ext (p.isMaximal.eq_of_le q.isPrime.ne_top h1).symm)
  obtain ⟨t, ht, htq⟩ := SetLike.not_le_iff_exists.mp hnle
  refine ⟨t, htq, ?_⟩
  have : t * s ∈ Ideal.span {d} := by
    rw [hfac]; exact Ideal.mul_mem_mul ht hsJ
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp this
  exact ⟨u, hu.symm⟩

theorem exists_denominator {R K M : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup M] [Module K M] [Module R M] [IsScalarTower R K M] (N : Submodule R M) (x : M)
    (hx : x ∈ Submodule.span K (N : Set M)) : ∃ d : R, d ≠ 0 ∧ d • x ∈ N := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hx⟩ := hx
    obtain ⟨b, hb, hy⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine N.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact N.smul_mem _ hx
    · rw [mul_smul]; exact N.smul_mem _ hy
  | smul c x _ hx =>
    obtain ⟨a, ha, hx⟩ := hx
    obtain ⟨u, w, hw, rfl⟩ := IsFractionRing.div_surjective (A := R) c
    have hw0 : w ≠ 0 := nonZeroDivisors.ne_zero hw
    have hwK : algebraMap R K w ≠ 0 := by simpa using hw0
    refine ⟨a * w, mul_ne_zero ha hw0, ?_⟩
    have : (a * w) • (algebraMap R K u / algebraMap R K w) • x = u • a • x := by
      rw [← algebraMap_smul K (a * w), ← algebraMap_smul K u, ← algebraMap_smul K a, smul_smul, smul_smul]
      congr 1
      rw [map_mul]
      field_simp
    rw [this]
    exact N.smul_mem _ hx

theorem exists_smul_mem_supLattice (LL Ks WL G : Type) [Field LL] [NumberField LL] [Field Ks] [NumberField Ks]
    [Algebra Ks LL] [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
    [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL] (W : (LL →+* ℂ) → Type)
    [(σ : LL →+* ℂ) → NormedAddCommGroup (W σ)] [(σ : LL →+* ℂ) → InnerProductSpace ℂ (W σ)] [Group G]
    (Φ : FormsL LL Ks WL W G) (hspan : Submodule.span Ks (Φ.MK : Set WL) = Φ.WK)
    (la : HeightOneSpectrum (𝓞 Ks)) (f : Φ.WK) (hf : ∀ y : Φ.Pt la, Φ.nrm la y f ≤ 1) :
    ∃ s ∉ la.asIdeal, s • (f : WL) ∈ Φ.MK := by
  obtain ⟨d, hd, hdf⟩ := exists_denominator (K := Ks) Φ.MK (f : WL) (by rw [hspan]; exact f.2)
  obtain ⟨s, hs, hq⟩ := exists_prime_to_part la d hd
  refine ⟨s, hs, ?_⟩
  have hsm : ∀ (a : 𝓞 Ks) (g : WL), a • g = (a : Ks) • g := fun a g => (algebraMap_smul Ks a g).symm
  have hm : s • (f : WL) ∈ Φ.WK := by rw [hsm]; exact Φ.WK.smul_mem _ f.2
  refine ⟨hm, fun q y => ?_⟩
  by_cases h : q = la
  · subst h
    have h1 : (⟨s • (f : WL), hm⟩ : Φ.WK) = (s : Ks) • f := Subtype.ext (hsm s f)
    rw [h1, Φ.nrm_smul, abs_eq_one q s hs, one_mul]
    exact hf y
  · obtain ⟨t, ht, u, htu⟩ := hq q h
    have hmem : t • s • (f : WL) ∈ Φ.MK := by
      rw [smul_smul, htu, mul_smul]; exact Φ.MK.smul_mem _ hdf
    obtain ⟨hw, hb⟩ := hmem
    have h1 : (⟨t • s • (f : WL), hw⟩ : Φ.WK) = (t : Ks) • ⟨s • (f : WL), hm⟩ := Subtype.ext (hsm t _)
    have h2 := hb q y
    rwa [h1, Φ.nrm_smul, abs_eq_one q t ht, one_mul] at h2

end GlobalTheory.DenominatorExistenceTwistedOperators
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExpandPiOfExpandEachStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_sum_prod_of_expansion_in_each_coordinate : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type} (K : ∀ i, Set (X i)) (m : ι → ℕ)
    (k : ∀ i, Fin (m i) → X i) (hk : ∀ i j, k i j ∈ K i) (c : ∀ i, Fin (m i) → X i → ℂ)
    (f : (∀ i, X i) → ℂ)
    (hf : ∀ i (g : ∀ i, X i), (∀ i, g i ∈ K i) → f g = ∑ j, f (Function.update g i (k i j)) * c i j (g i))
    (g : ∀ i, X i) (hg : ∀ i, g i ∈ K i), f g = ∑ J : (∀ i, Fin (m i)), f (fun i => k i (J i)) * ∏ i, c i (J i) (g i) := by
  first | exact @GlobalTheory.expand_pi_of_expand_each | exact GlobalTheory.expand_pi_of_expand_each | (intros; apply GlobalTheory.expand_pi_of_expand_each <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteAndNcardMinpolyCoeffHeightLeStatement
section
open NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_and_ncard_minpoly_coeff_height_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∃ (C : ℝ) (k : ℕ), ∀ B : ℝ, 1 ≤ B → {x : E | ∀ j, Height.mulHeight₁ ((minpoly F x).coeff j) ≤ B}.Finite ∧ (({x : E | ∀ j, Height.mulHeight₁ ((minpoly F x).coeff j) ≤ B}.ncard : ℕ) : ℝ) ≤ C * B ^ k := by
  first | exact @GlobalTheory.MinpolyHeightCount.finite_and_ncard_minpoly_height_le | exact GlobalTheory.MinpolyHeightCount.finite_and_ncard_minpoly_height_le | (intros; apply GlobalTheory.MinpolyHeightCount.finite_and_ncard_minpoly_height_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinsetFunctionsRecoveredFromValuesStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_eq_sum_smul_of_mem_submodule : ∀ {X : Type} (V : Submodule ℂ (X → ℂ)) (F : Finset (X → ℂ)), (∀ u ∈ F, u ∈ V) →
    ∃ (s : Finset X) (E : X → X → ℂ), (∀ x, E x ∈ V) ∧ ∀ u ∈ F, u = ∑ x ∈ s, u x • E x := by
  first | exact @GlobalTheory.finset_functions_recovered_from_values | exact GlobalTheory.finset_functions_recovered_from_values | (intros; apply GlobalTheory.finset_functions_recovered_from_values <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierUniquenessOfOpenSubgroupStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_integral_char_eq_zero_of_periodic_open : ∀ {H A : Type} [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [μ.IsAddHaarMeasure] [AddCommGroup A] (χ : A → H → ℂ), (∀ a s t, χ a (s + t) = χ a s * χ a t) → (∀ a, χ a 0 = 1) → (∀ t, χ 0 t = 1) → (∀ a b t, χ (a + b) t = χ a t * χ b t) → ∀ L : AddSubgroup H, IsOpen (L : Set H) → (∀ x, x ∉ L → ∃ a, (∀ l ∈ L, χ a l = 1) ∧ χ a x ≠ 1) → ∀ (φ : H → ℂ) (Kc : Set H), IsCompact Kc → (∀ t, t ∉ Kc → φ t = 0) → (∀ t, ∀ l ∈ L, φ (t + l) = φ t) → (∀ a, (∀ l ∈ L, χ a l = 1) → ∫ t, χ a t * φ t ∂μ = 0) → φ = 0 := by
  first | exact @GlobalTheory.fourier_uniqueness_of_openSubgroup | exact GlobalTheory.fourier_uniqueness_of_openSubgroup | (intros; apply GlobalTheory.fourier_uniqueness_of_openSubgroup <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FubiniRightConvolutionBoundedContinuousStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_fundamentalDomain_convolution_comm_of_bounded : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {H : Subgroup G} (μ : Measure G) (𝓕 : Set G), μ 𝓕 < ⊤ → ∀ (m : Measure H) [SFinite m] (α : H → ℂ), Integrable α m → ∀ (ψ φ : G → ℂ), Continuous ψ → Continuous φ → ∀ (A B : ℝ), (∀ g, ‖ψ g‖ ≤ A) → (∀ g, ‖φ g‖ ≤ B) → IntegrableOn (fun x => ψ x * ∫ h, α h * φ (x * (h : G)) ∂m) 𝓕 μ ∧ Integrable (fun h : H => α h * ∫ x in 𝓕, ψ x * φ (x * (h : G)) ∂μ) m ∧ ∫ x in 𝓕, ψ x * (∫ h, α h * φ (x * (h : G)) ∂m) ∂μ = ∫ h, α h * (∫ x in 𝓕, ψ x * φ (x * (h : G)) ∂μ) ∂m := by
  first | exact @GlobalTheory.fubini_right_convolution_bounded_continuous | exact GlobalTheory.fubini_right_convolution_bounded_continuous | (intros; apply GlobalTheory.fubini_right_convolution_bounded_continuous <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GradedSeriesContinuationDominatedStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_and_summable_on_ball_of_hasSum_on_interval : ∀ {ι : Type} (deg : ι → ℕ), (∀ k, {i | deg i = k}.Finite) → ∀ (a : ι → ℂ) (b : ι → ℝ) (C δ ρ : ℝ) (P P' : ℂ → ℂ), 0 < δ → (∀ i, 0 ≤ b i) → (∀ i, ‖a i‖ ≤ C * b i) → DifferentiableOn ℂ P (Metric.ball 0 ρ) → DifferentiableOn ℂ P' (Metric.ball 0 ρ) → (∀ x : ℝ, 0 < x → x < δ → HasSum (fun i => a i * (x : ℂ) ^ deg i) (P x) ∧ HasSum (fun i => (b i : ℂ) * (x : ℂ) ^ deg i) (P' x)) → ∀ X : ℂ, ‖X‖ < ρ → HasSum (fun i => a i * X ^ deg i) (P X) ∧ Summable (fun i => b i * ‖X‖ ^ deg i) := by
  first | exact @GlobalTheory.gradedSeries_continuation_dominated | exact GlobalTheory.gradedSeries_continuation_dominated | (intros; apply GlobalTheory.gradedSeries_continuation_dominated <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarMapMulRightEqOfFiniteFundamentalDomain
section
open MeasureTheory Function
open scoped Pointwise

namespace GlobalTheory

theorem haar_map_mul_right_eq_of_fundamentalDomain (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H]
    (Γ N : Subgroup H) (hΓ : Countable Γ) (hNc : IsClosed (N : Set H)) (κ : Measure N) (𝓝 : Set N)
    (hκ : κ.IsHaarMeasure) (h𝓝 : IsFundamentalDomain (Γ.subgroupOf N) 𝓝 κ) (hfin : κ 𝓝 ≠ ⊤) (n₀ : N) :
    κ.map (· * n₀) = κ := by
  haveI : LocallyCompactSpace N := hNc.locallyCompactSpace
  haveI : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology (N : Set H)
  haveI : Countable (Γ.subgroupOf N) := by
    refine Function.Injective.countable (f := fun x : Γ.subgroupOf N => (⟨((x : N) : H), x.2⟩ : Γ)) ?_
    intro a b h
    have h' : ((a : N) : H) = ((b : N) : H) := congrArg (fun y : Γ => (y : H)) h
    exact Subtype.ext (Subtype.ext h')
  haveI : (κ.map (· * n₀)).IsHaarMeasure := Measure.isHaarMeasure_map_mul_right κ n₀
  have hc := Measure.isMulLeftInvariant_eq_smul (κ.map (· * n₀)) κ
  set c := Measure.haarScalarFactor (κ.map (· * n₀)) κ
  have h𝓝' : IsFundamentalDomain (Γ.subgroupOf N) ((· * n₀) ⁻¹' 𝓝) κ := by
    refine h𝓝.preimage_of_equiv (quasiMeasurePreserving_mul_right κ n₀) (e := id) bijective_id ?_
    intro g x
    simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc]
  have hm : κ ((· * n₀) ⁻¹' 𝓝) = κ 𝓝 := h𝓝'.measure_eq h𝓝
  have h0 : κ 𝓝 ≠ 0 := h𝓝.measure_ne_zero (NeZero.ne κ)
  have hmap : (κ.map (· * n₀)) 𝓝 = κ ((· * n₀) ⁻¹' 𝓝) :=
    MeasurableEquiv.map_apply (MeasurableEquiv.mulRight n₀) 𝓝
  have h1 : (c : ENNReal) * κ 𝓝 = 1 * κ 𝓝 := by
    calc (c : ENNReal) * κ 𝓝 = (c • κ) 𝓝 := by simp [Measure.smul_apply]
      _ = (κ.map (· * n₀)) 𝓝 := by rw [hc]
      _ = 1 * κ 𝓝 := by rw [one_mul]; exact hmap.trans hm
  have hc1 : c = 1 := by
    have := (ENNReal.mul_left_inj h0 hfin).1 h1
    exact_mod_cast this
  rw [hc, hc1, one_smul]

end GlobalTheory
end

