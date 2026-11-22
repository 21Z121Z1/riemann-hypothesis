import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0012
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0024
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0029
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0027
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0003
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0028
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PlaceEqOneOfNotMem

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenPtSpecializesOfSpecializes
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar TopologicalSpace

theorem isOpen_of_isClosed_of_generizing {α : Type*} [TopologicalSpace α] [NoetherianSpace α] [QuasiSober α]
    (S : Set α) (hc : IsClosed S) (hs : ∀ x y : α, x ⤳ y → y ∈ S → x ∈ S) : IsOpen S := by
  have hfin : (irreducibleComponents α).Finite := NoetherianSpace.finite_irreducibleComponents
  have hT : IsClosed (⋃₀ {C ∈ irreducibleComponents α | Disjoint C S}) := by
    rw [Set.sUnion_eq_biUnion]
    exact (hfin.subset fun C (h : C ∈ {C ∈ irreducibleComponents α | Disjoint C S}) => h.1).isClosed_biUnion
      fun C h => isClosed_of_mem_irreducibleComponents C h.1
  have e : Sᶜ = ⋃₀ {C ∈ irreducibleComponents α | Disjoint C S} := by
    ext x
    constructor
    · intro hx
      refine ⟨irreducibleComponent x, ⟨irreducibleComponent_mem_irreducibleComponents x, ?_⟩,
        mem_irreducibleComponent⟩
      rw [Set.disjoint_left]
      intro s hsC hsS
      have hC := isIrreducible_irreducibleComponent (x := x)
      have hcl : IsClosed (irreducibleComponent x) := isClosed_irreducibleComponent
      obtain ⟨c, hcg⟩ := QuasiSober.sober hC hcl
      have hcs : c ∈ S := hs c s (hcg.specializes hsC) hsS
      exact hx (hc.closure_subset_iff.2 (Set.singleton_subset_iff.2 hcs) (by
        rw [hcg.def]; exact mem_irreducibleComponent))
    · rintro ⟨C, ⟨-, hd⟩, hx⟩ hxS
      exact Set.disjoint_left.1 hd hx hxS
  rw [← isClosed_compl_iff, e]
  exact hT

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

theorem genPt_specializes_of_specializes (ξ : Spec (CommRingCat.of Ω) ⟶ X) (h : IsCptGen ξ) {p y : X}
    (hp : genPt ξ ⤳ p) (hy : y ⤳ p) : genPt ξ ⤳ y := by
  haveI := CptInh.dom ξ h ⟨p, hp⟩
  haveI : IsDomain (X.presheaf.stalk p) := this
  obtain ⟨a, ha⟩ : genPt ξ ∈ Set.range (X.fromSpecStalk p) := by
    rwa [Scheme.range_fromSpecStalk]
  obtain ⟨b, hb⟩ : y ∈ Set.range (X.fromSpecStalk p) := by
    rwa [Scheme.range_fromSpecStalk]
  let o : Spec (CommRingCat.of (X.presheaf.stalk p)) :=
    (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (X.presheaf.stalk p))
  have hoc : ∀ c : Spec (CommRingCat.of (X.presheaf.stalk p)), o ⤳ c := fun c =>
    (PrimeSpectrum.le_iff_specializes (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (X.presheaf.stalk p)) c).1 bot_le
  have h1 : X.fromSpecStalk p o ⤳ genPt ξ := by
    rw [← ha]; exact (hoc a).map (X.fromSpecStalk p).continuous
  have h2 : X.fromSpecStalk p o ⤳ y := by
    rw [← hb]; exact (hoc b).map (X.fromSpecStalk p).continuous
  rwa [CptInh.nogen ξ h _ h1] at h2

theorem isOpen_closure_genPt (ξ : Spec (CommRingCat.of Ω) ⟶ X) [IsLocallyNoetherian X] (h : IsCptGen ξ) :
    IsOpen (closure {genPt ξ}) := by
  rw [isOpen_iff_forall_mem_open]
  intro p hp
  obtain ⟨W, hpW⟩ : ∃ W : X.affineOpens, p ∈ W.1 := by
    obtain ⟨W, hW, hpW, -⟩ := exists_isAffineOpen_mem_and_subset (x := p) (U := ⊤) trivial
    exact ⟨⟨W, hW⟩, hpW⟩
  haveI : IsNoetherianRing Γ(X, W.1) := IsLocallyNoetherian.component_noetherian W
  haveI : NoetherianSpace (W.1 : X.Opens) := noetherianSpace_of_isAffineOpen W.1 W.2
  haveI : QuasiSober (W.1 : X.Opens) := inferInstanceAs (QuasiSober (W.1 : X.Opens).toScheme)
  have ho : IsOpen (Subtype.val ⁻¹' (closure {genPt ξ}) : Set (W.1 : X.Opens)) :=
    isOpen_of_isClosed_of_generizing _ (isClosed_closure.preimage continuous_subtype_val)
      fun x y hxy hy => by
        have hy' : genPt ξ ⤳ y.1 := specializes_iff_mem_closure.2 hy
        exact specializes_iff_mem_closure.1
          (genPt_specializes_of_specializes ξ h hy' (hxy.map continuous_subtype_val))
  refine ⟨Subtype.val '' (Subtype.val ⁻¹' (closure {genPt ξ}) : Set (W.1 : X.Opens)), ?_,
    W.1.isOpen.isOpenMap_subtype_val _ ho, ⟨⟨p, hpW⟩, hp, rfl⟩⟩
  rintro _ ⟨x, hx, rfl⟩
  exact hx

theorem cpt_open_integral : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    [IsLocallyNoetherian X], IsCptGen ξ → ∃ U : X.Opens, (∀ q : X, q ∈ U ↔ genPt ξ ⤳ q) ∧
      IsClosed (U : Set X) ∧ IsIntegral U.toScheme := by
  intro X Ω _ ξ _ h
  let U : X.Opens := ⟨closure {genPt ξ}, isOpen_closure_genPt ξ h⟩
  have hU : ∀ q : X, q ∈ U ↔ genPt ξ ⤳ q := fun q => specializes_iff_mem_closure.symm
  refine ⟨U, hU, isClosed_closure, ?_⟩
  haveI : IrreducibleSpace U.toScheme :=
    Subtype.irreducibleSpace (isIrreducible_singleton (x := genPt ξ)).closure
  haveI : ∀ x : U.toScheme, _root_.IsReduced (U.toScheme.presheaf.stalk x) := fun x => by
    haveI := CptInh.dom ξ h ⟨U.ι x, (hU _).1 x.2⟩
    have e := (asIso (U.ι.stalkMap x)).commRingCatIsoToRingEquiv
    exact isReduced_of_injective e.symm.toRingHom e.symm.injective
  haveI : IsReduced U.toScheme := isReduced_of_isReduced_stalk _
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFlagFieldChange
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.GenericColumns

theorem det_eq_one {K : Type*} [Field K] {n : ℕ} (u : Matrix (Fin n) (Fin n) K)
    (h1 : ∀ k, u k k = 1) (h0 : ∀ l k, l < k → u l k = 0) : u.det = 1 := by
  rw [Matrix.det_of_lowerTriangular u (fun i j hij => h0 _ _ hij)]
  simp [h1]

theorem linearIndependent_cols {K M : Type*} [Field K] [AddCommGroup M] [Module K M] {n : ℕ}
    (u : Matrix (Fin n) (Fin n) K) (h1 : ∀ k, u k k = 1) (h0 : ∀ l k, l < k → u l k = 0)
    (v : Fin n → M) (hv : LinearIndependent K v) :
    LinearIndependent K fun k => ∑ l, u l k • v l := by
  rw [Fintype.linearIndependent_iff] at hv ⊢
  intro g hg
  have hz : ∀ l, ∑ k, u l k * g k = 0 := by
    apply hv (fun l => ∑ k, u l k * g k)
    rw [← hg]
    simp only [Finset.smul_sum, Finset.sum_smul, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by rw [mul_comm]
  have hm : u.mulVec g = 0 := funext hz
  have hg0 := Matrix.eq_zero_of_mulVec_eq_zero (by rw [det_eq_one u h1 h0]; exact one_ne_zero) hm
  intro i
  exact congrFun hg0 i

theorem span_cols {K M : Type*} [Field K] [AddCommGroup M] [Module K M] {n : ℕ}
    (u : Matrix (Fin n) (Fin n) K) (h1 : ∀ k, u k k = 1) (h0 : ∀ l k, l < k → u l k = 0)
    (v : Fin n → M) :
    Submodule.span K (Set.range fun k => ∑ l, u l k • v l) = Submodule.span K (Set.range v) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨m, rfl⟩
    have hu : u * u⁻¹ = 1 := Matrix.mul_nonsing_inv u (by rw [det_eq_one u h1 h0]; exact isUnit_one)
    have hvm : v m = ∑ k, u⁻¹ k m • ∑ l, u l k • v l := by
      simp only [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      have hl : ∀ l, ∑ k, (u⁻¹ k m * u l k) • v l = (if l = m then (1 : K) else 0) • v l := by
        intro l
        rw [← Finset.sum_smul]
        congr 1
        have := congrFun (congrFun hu l) m
        rw [Matrix.mul_apply, Matrix.one_apply] at this
        rw [← this]
        exact Finset.sum_congr rfl fun k _ => mul_comm _ _
      simp [hl]
    show v m ∈ _
    rw [hvm]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem genU_diag (Ω : Type) [Field Ω] {S : Type} (r : S → ℕ) (s : S) (k : Fin (r s)) :
    genU Ω r s k k = 1 := by
  simp [genU]

theorem genU_zero (Ω : Type) [Field Ω] {S : Type} (r : S → ℕ) (s : S) (l k : Fin (r s)) (h : l < k) :
    genU Ω r s l k = 0 := by
  have h1 : ¬ k < l := not_lt.2 h.le
  have h2 : l ≠ k := h.ne
  simp [genU, h1, h2]

theorem genU_gen (Ω : Type) [Field Ω] {S : Type} (r : S → ℕ) (q : GenIx r) :
    genU Ω r q.1 q.2.1.1 q.2.1.2 =
      algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X q) := by
  obtain ⟨s, ⟨⟨l, k⟩, h⟩⟩ := q
  exact dif_pos h

theorem algebraicIndependent_gen (Ω : Type) [Field Ω] {S : Type} (r : S → ℕ) :
    AlgebraicIndependent Ω (fun q : GenIx r =>
      algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X q)) :=
  (MvPolynomial.algebraicIndependent_X (GenIx r) Ω).map'
    (f := IsScalarTower.toAlgHom Ω (MvPolynomial (GenIx r) Ω) (GenField Ω r))
    (IsFractionRing.injective _ _)

theorem algebraicIndependent_comp {Ω₀ Ω K I : Type} [Field Ω₀] [Field Ω] [Field K] [Algebra Ω K]
    (fn : Ω₀ →+* Ω) {x : I → K} (hx : AlgebraicIndependent Ω x) :
    letI := ((algebraMap Ω K).comp fn).toAlgebra
    AlgebraicIndependent Ω₀ x := by
  letI a1 : Algebra Ω₀ Ω := fn.toAlgebra
  letI a2 : Algebra Ω₀ K := ((algebraMap Ω K).comp fn).toAlgebra
  haveI : IsScalarTower Ω₀ Ω K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact hx.restrictScalars (R := Ω₀) (K := Ω) fn.injective

theorem adjoin_entries {Ω₀ Ω : Type} [Field Ω₀] [Field Ω] (fn : Ω₀ →+* Ω) {S : Type} (r : S → ℕ) :
    letI := ((algebraMap Ω (GenField Ω r)).comp fn).toAlgebra
    IntermediateField.adjoin Ω₀
        (Set.range fun q : Σ s, Fin (r s) × Fin (r s) => genU Ω r q.1 q.2.1 q.2.2) =
      IntermediateField.adjoin Ω₀ (Set.range fun q : GenIx r =>
        algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X q)) := by
  letI := ((algebraMap Ω (GenField Ω r)).comp fn).toAlgebra
  apply le_antisymm
  · refine IntermediateField.adjoin_le_iff.2 ?_
    rintro _ ⟨⟨s, l, k⟩, rfl⟩
    show genU Ω r s l k ∈ _
    by_cases h : k < l
    · have := genU_gen Ω r ⟨s, ⟨(l, k), h⟩⟩
      exact this ▸ IntermediateField.subset_adjoin _ _ ⟨_, rfl⟩
    · by_cases e : l = k
      · subst e
        rw [genU_diag]
        exact one_mem _
      · rw [genU_zero Ω r s l k (lt_of_le_of_ne (not_lt.1 h) e)]
        exact zero_mem _
  · refine IntermediateField.adjoin_le_iff.2 ?_
    rintro _ ⟨q, rfl⟩
    show algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X q) ∈ _
    rw [← genU_gen]
    exact IntermediateField.subset_adjoin _ _ ⟨⟨q.1, q.2.1.1, q.2.1.2⟩, rfl⟩

theorem isGenericFlag_columns : ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (fn : Ω₀ →+* Ω) (S : Type) (r : S → ℕ) (d : ℕ), 0 < d → (letI := ((algebraMap Ω (GenField Ω r)).comp fn).toAlgebra; Module.finrank (IntermediateField.adjoin Ω₀ (Set.range fun q : GenIx r => algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X q))) (GenField Ω r) = d) → ∀ (E₀ E' : Type) [AddCommGroup E₀] [Module Ω₀ E₀] [AddCommGroup E'] [Module (GenField Ω r) E'] (j : E₀ →+ E') (V₀ : S → Submodule Ω₀ E₀) (c : ∀ s, Fin (r s) → E₀), (∀ s, LinearIndependent Ω₀ (c s) ∧ Submodule.span Ω₀ (Set.range (c s)) = V₀ s) → (∀ (a : Ω₀) e, j (a • e) = algebraMap Ω (GenField Ω r) (fn a) • j e) → (∀ s, LinearIndependent (GenField Ω r) fun k => j (c s k)) → (∀ s, Submodule.span (GenField Ω r) (Set.range fun k => ∑ l, genU Ω r s l k • j (c s l)) = Submodule.span (GenField Ω r) (Set.range fun k => j (c s k))) ∧ (letI := ((algebraMap Ω (GenField Ω r)).comp fn).toAlgebra; IsGenericFlag (Ω' := GenField Ω r) j V₀ (fun s k => ∑ l, genU Ω r s l k • j (c s l)) d) := by
  intro Ω₀ Ω _ _ fn S r d hd hdeg E₀ E' _ _ _ _ j V₀ c hc hj hli
  refine ⟨fun s => span_cols _ (genU_diag Ω r s) (genU_zero Ω r s) _, ?_⟩
  letI := ((algebraMap Ω (GenField Ω r)).comp fn).toAlgebra
  refine ⟨c, genU Ω r, hc, hj, hli,
    fun s => linearIndependent_cols _ (genU_diag Ω r s) (genU_zero Ω r s) _ (hli s),
    genU_diag Ω r, genU_zero Ω r, fun _ _ => rfl, ?_, hd, ?_⟩
  · have h := algebraicIndependent_comp fn (algebraicIndependent_gen Ω r)
    have he : (fun q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1} =>
        genU Ω r q.1 q.2.1.1 q.2.1.2) = fun q : GenIx r =>
        algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X q) :=
      funext (genU_gen Ω r)
    rw [he]
    exact h
  · rw [adjoin_entries fn r]
    exact hdeg

end GlobalTheory.CompanionTheory.Ar.FlagBun.GenericColumns
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFlagOverGenericField
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun

open AlgebraicGeometry CategoryTheory

variable {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {S : Type} {r : S → ℕ}

theorem genU_diag (s : S) (k : Fin (r s)) : genU Ω r s k k = 1 := by
  simp [genU]

theorem genU_above (s : S) (l k : Fin (r s)) (h : l < k) : genU Ω r s l k = 0 := by
  have h1 : ¬ k < l := not_lt.mpr h.le
  simp [genU, h1, h.ne]

theorem genU_below (s : S) (l k : Fin (r s)) (h : k < l) :
    genU Ω r s l k = algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r)
      (MvPolynomial.X ⟨s, ⟨(l, k), h⟩⟩) := by
  simp only [genU, dif_pos h]

theorem genU_det (s : S) : (genU Ω r s).det = 1 := by
  have hlow : (genU Ω r s).IsLowerTriangular := by
    intro i j hij
    exact genU_above s i j (by simpa using hij)
  rw [Matrix.det_of_isLowerTriangular _ hlow]
  exact Finset.prod_eq_one fun i _ => genU_diag s i

theorem genField_adjoin_eq_top :
    IntermediateField.adjoin Ω
      (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => genU Ω r q.1 q.2.1 q.2.2) = ⊤ := by
  set K := IntermediateField.adjoin Ω
    (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => genU Ω r q.1 q.2.1 q.2.2) with hK
  have hX : ∀ i : GenIx r,
      algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X i) ∈ K := by
    intro i
    obtain ⟨s, ⟨⟨l, k⟩, h⟩⟩ := i
    apply IntermediateField.subset_adjoin
    exact ⟨⟨s, (l, k)⟩, genU_below s l k h⟩
  have hP : ∀ p : MvPolynomial (GenIx r) Ω,
      algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) p ∈ K := by
    intro p
    refine MvPolynomial.induction_on
      (motive := fun p => algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) p ∈ K) p ?_ ?_ ?_
    · intro a
      have h1 := IsScalarTower.algebraMap_apply Ω (MvPolynomial (GenIx r) Ω) (GenField Ω r) a
      rw [MvPolynomial.algebraMap_eq] at h1
      rw [← h1]
      exact IntermediateField.algebraMap_mem K a
    · intro p q hp hq
      rw [map_add]
      exact add_mem hp hq
    · intro p n hp
      rw [map_mul]
      exact mul_mem hp (hX n)
  refine eq_top_iff.mpr fun z _ => ?_
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (MvPolynomial (GenIx r) Ω) z
  exact div_mem (hP a) (hP b)

theorem linearIndependent_one_tmul {ι : Type} {v : ι → E} (hv : LinearIndependent Ω v) :
    LinearIndependent (GenField Ω r)
      fun k => TensorProduct.mk Ω (GenField Ω r) E 1 (v k) := by
  simpa only [TensorProduct.mk_apply] using
    Module.Flat.linearIndependent_one_tmul (S := GenField Ω r) hv

theorem genB_linearIndependent (c : ∀ s, Fin (r s) → E) (s : S)
    (h : LinearIndependent (GenField Ω r)
      fun k => TensorProduct.mk Ω (GenField Ω r) E 1 (c s k)) :
    LinearIndependent (GenField Ω r) (genB (Ω := Ω) c s) := by
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro g hg
  have hz : ∀ l, ∑ k, genU Ω r s l k * g k = 0 := by
    refine h (fun l => ∑ k, genU Ω r s l k * g k) ?_
    rw [← hg]
    simp only [genB, Finset.smul_sum, Finset.sum_smul, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by rw [mul_comm]
  have hv : Matrix.mulVec (genU Ω r s) g = 0 := by
    ext l
    exact hz l
  have hU : IsUnit (genU Ω r s).det := by
    rw [genU_det]
    exact isUnit_one
  have hg0 : g = 0 := by
    calc g = Matrix.mulVec ((genU Ω r s)⁻¹ * genU Ω r s) g := by
          rw [Matrix.nonsing_inv_mul _ hU, Matrix.one_mulVec]
      _ = Matrix.mulVec (genU Ω r s)⁻¹ (Matrix.mulVec (genU Ω r s) g) := by rw [Matrix.mulVec_mulVec]
      _ = 0 := by rw [hv, Matrix.mulVec_zero]
  intro k
  simp [hg0]

theorem genB_isGenericFlag : ∀ (Ω : Type) [Field Ω] (E : Type) [AddCommGroup E] [Module Ω E] (S : Type)
    (r : S → ℕ) (V : S → Submodule Ω E) (c : ∀ s, Fin (r s) → E),
    (∀ s, LinearIndependent Ω (c s) ∧ Submodule.span Ω (Set.range (c s)) = V s) →
    IsGenericFlag (Ω' := GenField Ω r) (TensorProduct.mk Ω (GenField Ω r) E 1).toAddMonoidHom V (genB c) 1 := by
  intro Ω hΩ E hE hEm S r V c hc
  unfold IsGenericFlag
  have hli : ∀ σ, LinearIndependent (GenField Ω r)
      fun k => TensorProduct.mk Ω (GenField Ω r) E 1 (c σ k) :=
    fun σ => linearIndependent_one_tmul (r := r) (hc σ).1
  refine ⟨c, genU Ω r, hc, ?_, fun σ => hli σ, fun σ => genB_linearIndependent c σ (hli σ),
    fun σ k => genU_diag σ k, fun σ l k h => genU_above σ l k h, fun σ i => rfl, ?_, Nat.one_pos, ?_⟩
  · intro a e
    simp only [LinearMap.toAddMonoidHom_coe, TensorProduct.mk_apply]
    rw [TensorProduct.tmul_smul, algebraMap_smul]
  · have hai : AlgebraicIndependent Ω (fun q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1} =>
        algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X q)) :=
      (MvPolynomial.algebraicIndependent_X (GenIx r) Ω).map'
        (f := IsScalarTower.toAlgHom Ω (MvPolynomial (GenIx r) Ω) (GenField Ω r))
        (IsFractionRing.injective (MvPolynomial (GenIx r) Ω) (GenField Ω r))
    have hfam : (fun q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1} =>
        genU Ω r q.1 q.2.1.1 q.2.1.2) =
        fun q => algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X q) :=
      funext fun q => genU_below q.1 q.2.1.1 q.2.1.2 q.2.2
    rw [hfam]
    exact hai
  · rw [genField_adjoin_eq_top]
    exact IntermediateField.finrank_top

end GlobalTheory.CompanionTheory.Ar.FlagBun
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HeightOnePrimeDvrStalk
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieStalk

namespace GlobalTheory.CompanionTheory.Ar.LieStalk.HeightOne

theorem isDVR_of_ringKrullDim_eq_one (B : Type*) [CommRing B] [IsDomain B] [IsLocalRing B] [IsNoetherianRing B]
    [IsIntegrallyClosed B] (h : ringKrullDim B = 1) : IsDiscreteValuationRing B := by
  have hf : ¬ IsField B := fun hB => by
    rw [ringKrullDim_eq_zero_of_isField hB] at h
    exact zero_ne_one h
  have hle : Ring.KrullDimLE 1 B := Ring.krullDimLE_iff.2 (by rw [h]; rfl)
  have hmax := Ring.krullDimLE_one_iff_of_noZeroDivisors.1 hle
  have hT := (IsDiscreteValuationRing.TFAE B hf).out 0 3
  refine hT.2 ⟨inferInstance, ExistsUnique.intro (IsLocalRing.maximalIdeal B) ⟨?_, inferInstance⟩ ?_⟩
  · exact fun h0 => hf (IsLocalRing.isField_iff_maximalIdeal_eq.2 h0)
  · rintro Q ⟨h0, hQ⟩
    have := hmax Q h0 hQ
    exact IsLocalRing.eq_maximalIdeal this

theorem comap_maximalIdeal_stalkSpecializes {X : Scheme.{0}} {x y : X} (h : x ⤳ y)
    (P : PrimeSpectrum (X.presheaf.stalk y)) (hP : X.fromSpecStalk y P = x) :
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).comap (X.presheaf.stalkSpecializes h).hom = P.asIdeal := by
  have e := Scheme.SpecMap_stalkSpecializes_fromSpecStalk h
  have e3 : (Spec.map (X.presheaf.stalkSpecializes h) ≫ X.fromSpecStalk y)
      (IsLocalRing.closedPoint (X.presheaf.stalk x) : Spec (X.presheaf.stalk x)) = x := by
    rw [e]
    exact Scheme.fromSpecStalk_closedPoint
  have e2 : X.fromSpecStalk y (Spec.map (X.presheaf.stalkSpecializes h)
      (IsLocalRing.closedPoint (X.presheaf.stalk x) : Spec (X.presheaf.stalk x))) = X.fromSpecStalk y P :=
    (Scheme.Hom.comp_apply _ _ _).symm.trans (e3.trans hP.symm)
  have inj : Function.Injective (X.fromSpecStalk y) := (X.fromSpecStalk y).isEmbedding.injective
  exact congrArg PrimeSpectrum.asIdeal (inj e2)

theorem exists_mul_stalkSpecializes {X : Scheme.{0}} {x y : X} (h : x ⤳ y)
    (P : Ideal (X.presheaf.stalk y))
    (hP : (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).comap (X.presheaf.stalkSpecializes h).hom = P)
    (b : X.presheaf.stalk x) :
    ∃ a, a ∉ P ∧ ∃ c, (X.presheaf.stalkSpecializes h).hom a * b = (X.presheaf.stalkSpecializes h).hom c := by
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial
  have hxU : x ∈ U := h.mem_open U.isOpen hyU
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hxU⟩ : U)
  have loc := hU.isLocalization_stalk ⟨x, hxU⟩
  obtain ⟨⟨r, t⟩, ht⟩ := IsLocalization.surj (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl b
  have hg : ∀ r : Γ(X, U), (X.presheaf.stalkSpecializes h).hom ((X.presheaf.germ U y hyU).hom r) =
      algebraMap Γ(X, U) (X.presheaf.stalk x) r := fun r =>
    ConcreteCategory.congr_hom (TopCat.Presheaf.germ_stalkSpecializes X.presheaf hyU h) r
  have hu : IsUnit (algebraMap Γ(X, U) (X.presheaf.stalk x) (t : Γ(X, U))) := IsLocalization.map_units _ t
  refine ⟨(X.presheaf.germ U y hyU).hom t, fun hm => ?_, (X.presheaf.germ U y hyU).hom r, ?_⟩
  · rw [← hP, Ideal.mem_comap, hg] at hm
    exact (IsLocalRing.mem_maximalIdeal _).1 hm hu
  · rw [hg, hg, mul_comm]
    exact ht

end GlobalTheory.CompanionTheory.Ar.LieStalk.HeightOne

namespace GlobalTheory.CompanionTheory.Ar.LieStalk.HeightOne

theorem exists_generisation_of_height_eq_one : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X), IsCptGen ξ → IsLocallyNoetherian X → IsNormalScheme X → ∀ (p : Cpt ξ) (P : PrimeSpectrum (regAt ξ p)), P.asIdeal.height = 1 → ∃ (q : Cpt ξ) (hs : q.1 ⤳ p.1), (∃ _ : IsDomain (X.presheaf.stalk q.1), IsDiscreteValuationRing (X.presheaf.stalk q.1)) ∧ (∀ s : regAt ξ p, s ∉ P.asIdeal → (s : Ω)⁻¹ ∈ regAt ξ q) ∧ ∀ a ∈ regAt ξ q, ∃ s : regAt ξ p, s ∉ P.asIdeal ∧ (s : Ω) * a ∈ regAt ξ p := by
  intro X Ω _ ξ hgen hN hnorm p P hP
  let P' : PrimeSpectrum (X.presheaf.stalk p.1) := ⟨Ideal.comap (regIso hgen p) P.asIdeal, inferInstance⟩
  have hP' : P'.asIdeal.height = 1 := ((regIso hgen p).height_comap P.asIdeal).trans hP
  have hmem : ∀ a, a ∈ P'.asIdeal ↔ regIso hgen p a ∈ P.asIdeal := fun a => Iff.rfl
  have hs : X.fromSpecStalk p.1 P' ⤳ p.1 := by
    have h : X.fromSpecStalk p.1 P' ∈ Set.range (X.fromSpecStalk p.1) := ⟨P', rfl⟩
    rwa [Scheme.range_fromSpecStalk] at h
  have hgq : genPt ξ ⤳ X.fromSpecStalk p.1 P' := by
    have e1 : genPt ξ = X.fromSpecStalk p.1 (spMap (genMap ξ p)
        (IsLocalRing.closedPoint Ω : Sp Ω)) :=
      (congrArg (fun g : Sp Ω ⟶ X => g (IsLocalRing.closedPoint Ω : Sp Ω))
        (spMap_genMap_fromSpecStalk p)).symm.trans (Scheme.Hom.comp_apply _ _ _)
    refine (specializes_of_eq e1).trans (Specializes.map ?_ (X.fromSpecStalk p.1).continuous)
    refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
    intro a ha
    have h0 : genMap ξ p a ∈ IsLocalRing.maximalIdeal Ω := ha
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at h0
    have : a = 0 := hgen.inj p (h0.trans (map_zero _).symm)
    rw [this]
    exact Ideal.zero_mem _
  let q : Cpt ξ := ⟨X.fromSpecStalk p.1 P', hgq⟩
  have hs' : q.1 ⤳ p.1 := hs
  obtain ⟨hdom, hic⟩ := hnorm q.1
  haveI := hN
  let f : X.presheaf.stalk p.1 →+* X.presheaf.stalk q.1 := (X.presheaf.stalkSpecializes hs').hom
  have hcomap : (IsLocalRing.maximalIdeal (X.presheaf.stalk q.1)).comap f = P'.asIdeal :=
    comap_maximalIdeal_stalkSpecializes hs' P' rfl
  have hgf : ∀ a, genMap ξ q (f a) = genMap ξ p a := genMap_specializes hs'
  have hfinj : Function.Injective f := fun a b hab =>
    hgen.inj p (by rw [← hgf, ← hgf, hab])
  have hunit : ∀ a, a ∉ P'.asIdeal → IsUnit (f a) := fun a ha => by
    by_contra hu
    exact ha (hcomap ▸ (IsLocalRing.mem_maximalIdeal _).2 hu)
  have hfrac : ∀ b, ∃ a, a ∉ P'.asIdeal ∧ ∃ c, f a * b = f c :=
    exists_mul_stalkSpecializes hs' P'.asIdeal hcomap
  have hdim : ringKrullDim (X.presheaf.stalk q.1) = 1 := by
    letI : Algebra (X.presheaf.stalk p.1) (X.presheaf.stalk q.1) := f.toAlgebra
    haveI : IsLocalization.AtPrime (X.presheaf.stalk q.1) P'.asIdeal :=
      { map_units := fun s => hunit s.1 s.2
        surj := fun b => by
          obtain ⟨a, ha, c, hc⟩ := hfrac b
          exact ⟨⟨c, ⟨a, ha⟩⟩, by rw [mul_comm]; exact hc⟩
        exists_of_eq := fun {a b} h => ⟨1, by rw [hfinj h]⟩ }
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height P'.asIdeal (X.presheaf.stalk q.1), hP']
    rfl
  refine ⟨q, hs', ⟨hdom, isDVR_of_ringKrullDim_eq_one _ hdim⟩, fun s hsP => ?_, ?_⟩
  · have ha : (regIso hgen p).symm s ∉ P'.asIdeal := by
      rw [hmem, RingEquiv.apply_symm_apply]
      exact hsP
    obtain ⟨u, hu⟩ := (hunit _ ha).exists_right_inv
    refine ⟨u, ?_⟩
    refine eq_inv_of_mul_eq_one_right ?_
    have h1 := congrArg (genMap ξ q) hu
    rw [map_mul, map_one, hgf, genMap_regIso_symm] at h1
    exact h1
  · rintro _ ⟨b, rfl⟩
    obtain ⟨a, ha, c, hc⟩ := hfrac b
    refine ⟨regIso hgen p a, fun h => ha ((hmem a).2 h), ⟨c, ?_⟩⟩
    have h1 := congrArg (genMap ξ q) hc
    rw [map_mul, hgf, hgf] at h1
    exact h1.symm

end GlobalTheory.CompanionTheory.Ar.LieStalk.HeightOne
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackEquivalenceStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_model_pullback_equivalence : ∀ (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → ∀ (R : Type) [CommRing R] (x' : Sp R ⟶ S') (E : Type) [AddCommGroup E] [Module R E], (∀ M : LieModel G (x' ≫ f) E, ∃ M' : LieModel G' x' E, ∀ e, (M'.pt e).left ≫ φ = (M.pt e).left) ∧ ∀ M' : LieModel G' x' E, ∃ M : LieModel G (x' ≫ f) E, ∀ e, (M'.pt e).left ≫ φ = (M.pt e).left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LiePull.lieModel_pullback | exact GlobalTheory.CompanionTheory.Ar.LiePull.lieModel_pullback | (intros; apply GlobalTheory.CompanionTheory.Ar.LiePull.lieModel_pullback <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalIndexAtSinglePlaceStatement
section
open NumberField Matrix IsDedekindDomain GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_index_at_single_place : ∀ (L : Type) [Field L] [NumberField L] (W : Type) [AddCommGroup W] [Module (𝓞 L) W] (v : FinitePlace L) (A B : Submodule (𝓞 L) W), B ≤ A → B.toAddSubgroup.relIndex A.toAddSubgroup ≠ 0 → (∀ w : FinitePlace L, w ≠ v → locAt w A = locAt w B) → (locAt v B).toAddSubgroup.relIndex (locAt v A).toAddSubgroup = B.toAddSubgroup.relIndex A.toAddSubgroup := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.LocIndex.relIndex_locAt | exact GlobalTheory.CompanionTheory.Ar.Cusp.LocIndex.relIndex_locAt | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.LocIndex.relIndex_locAt <;> assumption)
end

