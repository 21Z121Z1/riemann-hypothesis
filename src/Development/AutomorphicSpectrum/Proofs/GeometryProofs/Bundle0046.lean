import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0041
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteOpenHopfOrder
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0019
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0026
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0039
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0037
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0008
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsProductRefinement
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0002
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EtaleLocalizationAtPrimeTensorOfLowHeight

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AlgebraicIndependentOfAdjoin
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell

theorem algebraicIndependent_of_mem_adjoin_range :
    ∀ {Ω K : Type} [Field Ω] [Field K] [Algebra Ω K] {ι : Type} [Finite ι] (u v : ι → K),
      AlgebraicIndependent Ω u → (∀ a, u a ∈ IntermediateField.adjoin Ω (Set.range v)) →
      AlgebraicIndependent Ω v := by
  intro Ω K _ _ _ ι _ u v hu hmem
  set L := IntermediateField.adjoin Ω (Set.range v) with hL
  let v' : ι → L := fun a => ⟨v a, IntermediateField.subset_adjoin Ω _ ⟨a, rfl⟩⟩
  let u' : ι → L := fun a => ⟨u a, hmem a⟩
  have hu' : AlgebraicIndependent Ω u' := AlgebraicIndependent.of_comp (x := u') L.val hu
  have htop : IntermediateField.adjoin Ω (Set.range v') = ⊤ := by
    apply IntermediateField.map_injective L.val
    have hcomp : (⇑L.val ∘ v') = v := rfl
    rw [IntermediateField.adjoin_map, ← Set.range_comp, hcomp, ← AlgHom.fieldRange_eq_map,
      IntermediateField.fieldRange_val]
    try rfl
  haveI : Algebra.IsAlgebraic (Algebra.adjoin Ω (Set.range v')) L := by
    rw [← IntermediateField.isAlgebraic_adjoin_iff_top]
    refine ⟨fun x => ?_⟩
    have hx : x ∈ IntermediateField.adjoin Ω (Set.range v') := by
      rw [htop]
      exact IntermediateField.mem_top
    exact isAlgebraic_algebraMap (⟨x, hx⟩ : IntermediateField.adjoin Ω (Set.range v'))
  haveI : FaithfulSMul Ω L :=
    (faithfulSMul_iff_algebraMap_injective Ω L).mpr (algebraMap Ω L).injective
  obtain ⟨t, hts, htb⟩ := exists_isTranscendenceBasis_subset (R := Ω) (Set.range v')
  have hle : Cardinal.mk ι ≤ Cardinal.mk t :=
    hu'.cardinalMk_le_trdeg.trans htb.cardinalMk_eq_trdeg.symm.le
  haveI : Finite t := ((Set.finite_range v').subset hts).to_subtype
  have hcard : Nat.card ι ≤ Nat.card t := by
    letI := Fintype.ofFinite ι
    letI := Fintype.ofFinite t
    rw [Cardinal.mk_fintype, Cardinal.mk_fintype] at hle
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact_mod_cast hle
  have heq : t = Set.range v' :=
    Set.eq_of_subset_of_ncard_le hts
      (by
        rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
        exact (Finite.card_range_le v').trans hcard)
      (Set.finite_range v')
  subst heq
  have hinj : Function.Injective v' := by
    have hbij := (Set.rangeFactorization_surjective (f := v')).bijective_of_nat_card_le hcard
    intro a b hab
    exact hbij.1 (Subtype.ext hab)
  have hv' : AlgebraicIndependent Ω v' := (algebraicIndependent_subtype_range hinj).mp htb.1
  exact hv'.map' (f := L.val) Subtype.val_injective

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArMonoAddSingle
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open MvPolynomial NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Top

namespace RootMono

theorem card_fiber {α : Type*} [DecidableEq α] (l : List α) (c : α) :
    Fintype.card {i : Fin l.length // l.get i = c} = l.count c := by
  rw [Fintype.card_subtype, Finset.card_filter]
  induction l with
  | nil => simp
  | cons a l ih =>
    have h := Fin.sum_univ_succ (n := l.length)
      (fun i : Fin (l.length + 1) => if (a :: l).get i = c then 1 else 0)
    simp only [List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero, Fin.val_succ,
      List.getElem_cons_succ] at h ih
    simp only [List.get_eq_getElem, List.length_cons]
    rw [h, ih, List.count_cons]
    by_cases hac : a = c
    · simp [hac, add_comm]
    · simp [hac, add_comm]

theorem exists_perm_fin {α : Type*} [DecidableEq α] {l₁ l₂ : List α} (h : l₁.Perm l₂) {n : ℕ} (hn : l₁.length = n) :
    ∃ σ : Equiv.Perm (Fin n), ∀ (i : Fin n) (h₁ : (i : ℕ) < l₁.length) (h₂ : (σ i : ℕ) < l₂.length),
      l₂[(σ i : ℕ)] = l₁[(i : ℕ)] := by
  subst hn
  have hc : ∀ c, Fintype.card {i : Fin l₁.length // l₁.get i = c} =
      Fintype.card {i : Fin l₂.length // l₂.get i = c} := fun c => by
    rw [card_fiber, card_fiber, h.count_eq]
  let e : Fin l₁.length ≃ Fin l₂.length := Equiv.ofFiberEquiv fun c => Fintype.equivOfCardEq (hc c)
  have he : ∀ i, l₂.get (e i) = l₁.get i := Equiv.ofFiberEquiv_map _
  refine ⟨e.trans (finCongr h.length_eq.symm), fun i h₁ h₂ => ?_⟩
  simpa using he i

theorem length_toList {J : Type} (m : J →₀ ℕ) : (Finsupp.toMultiset m).toList.length = m.degree := by
  rw [Multiset.length_toList, Finsupp.card_toMultiset]
  simp only [Finsupp.sum, id]
  rfl

end RootMono

open RootMono in

theorem arMono_add_single (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M : RootModel Ψ N) (II : IntersectionSystem)
    (t : ℝ) (m : Ψ × Fin N →₀ ℕ) (r : Ψ × Fin N) (hII : IsIntersectionSystem II) (hm : m.degree = dimFl Ψ N) :
    M.arMono II t ((m + Finsupp.single r 1).mapDomain some) =
      II M.K M.ι M.P (dimFl Ψ N + 1)
        (Fin.snoc (monoLines (M.line t) (m.mapDomain some) (dimFl Ψ N)) (M.x t r)) / (M.δ : ℝ) := by
  classical
  have hn : (m + Finsupp.single r 1).mapDomain some = m.mapDomain some + Finsupp.single (some r) 1 := by
    rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single]
  have hdm : (m.mapDomain some).degree = dimFl Ψ N := by
    rw [Finsupp.degree_mapDomain, hm]
  have hdeg : ((m + Finsupp.single r 1).mapDomain some).degree = dimFl Ψ N + 1 := by
    rw [hn, map_add, hdm, Finsupp.degree_single]
  have hnone : ((m + Finsupp.single r 1).mapDomain some) none = 0 :=
    Finsupp.mapDomain_notin_range _ _ (by simp)
  have hperm : (Finsupp.toMultiset ((m + Finsupp.single r 1).mapDomain some)).toList.Perm
      ((Finsupp.toMultiset (m.mapDomain some)).toList ++ [some r]) := by
    rw [← Multiset.coe_eq_coe, ← Multiset.coe_add, Multiset.coe_toList, Multiset.coe_toList, hn, map_add]
    simp
  have hlen₁ : (Finsupp.toMultiset ((m + Finsupp.single r 1).mapDomain some)).toList.length = dimFl Ψ N + 1 := by
    rw [length_toList, hdeg]
  have hlen₀ : (Finsupp.toMultiset (m.mapDomain some)).toList.length = dimFl Ψ N := by
    rw [length_toList, hdm]
  have hsm : ∀ o, IsSmoothHerm (M.line t o) := by
    intro o
    cases o with
    | none => exact M.A_smooth
    | some b => exact M.x_smooth t b
  set L : Fin (dimFl Ψ N + 1) → HermLine M.ι :=
    Fin.snoc (monoLines (M.line t) (m.mapDomain some) (dimFl Ψ N)) (M.x t r) with hL
  have hval : ∀ (j : Fin (dimFl Ψ N + 1))
      (hj : (j : ℕ) < ((Finsupp.toMultiset (m.mapDomain some)).toList ++ [some r]).length),
      L j = M.line t (((Finsupp.toMultiset (m.mapDomain some)).toList ++ [some r])[(j : ℕ)]) := by
    intro j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · intro hj
      have : ((Finsupp.toMultiset (m.mapDomain some)).toList ++ [some r])[((Fin.last (dimFl Ψ N) : Fin _) : ℕ)] = some r := by
        simp [List.getElem_append, hlen₀]
      rw [this, hL, Fin.snoc_last]
      rfl
    · intro hj
      have hk : (k : ℕ) < (Finsupp.toMultiset (m.mapDomain some)).toList.length := by
        rw [hlen₀]; exact k.2
      have : ((Finsupp.toMultiset (m.mapDomain some)).toList ++ [some r])[((Fin.castSucc k : Fin _) : ℕ)] =
          (Finsupp.toMultiset (m.mapDomain some)).toList[(k : ℕ)] := by
        exact List.getElem_append_left hk
      rw [this, hL, Fin.snoc_castSucc]
      simp only [monoLines, dif_pos hk]
      rfl
  have hLs : ∀ j, IsSmoothHerm (L j) := by
    intro j
    have hj : (j : ℕ) < ((Finsupp.toMultiset (m.mapDomain some)).toList ++ [some r]).length := by
      simp [hlen₀, j.2]
    rw [hval j hj]
    exact hsm _
  obtain ⟨σ, hσ⟩ := exists_perm_fin hperm hlen₁
  have hfun : monoLines (M.line t) ((m + Finsupp.single r 1).mapDomain some) (dimFl Ψ N + 1) = L ∘ σ := by
    funext i
    have h₁ : (i : ℕ) < (Finsupp.toMultiset ((m + Finsupp.single r 1).mapDomain some)).toList.length := by
      rw [hlen₁]; exact i.2
    have h₂ : (σ i : ℕ) < ((Finsupp.toMultiset (m.mapDomain some)).toList ++ [some r]).length := by
      simp [hlen₀, (σ i).2]
    simp only [monoLines, dif_pos h₁, Function.comp, hval (σ i) h₂, hσ i h₁ h₂]
    rfl
  unfold RootModel.arMono
  rw [if_pos hdeg, hnone, pow_zero, mul_one, hfun]
  congr 1
  exact (hII M.K M.ι).1 M.P (dimFl Ψ N + 1) L σ M.arith hLs

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BlockJoinInclusionsCompat
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace GlobalTheory.CompanionTheory.Ar.Cmp.JoinBlock

theorem mConeMap_rename {K : Type} {ι : K → Type} {K' : Type} {ι' : K' → Type}
    (κ : K → K') (v : (Σ k, ι k) → Σ k, ι' k) {Ω : Type} [Field Ω] (y : (Σ k, ι' k) → Ω)
    (hv : ∀ p, (v p).1 = κ p.1) (f : MvPolynomial (Σ k, ι k) ℤ) :
    mConeMap y (rename v f) = rename κ (mConeMap (y ∘ v) f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [mConeMap]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, rename_X]
    congr 1
    simp [mConeMap, hv]

theorem imageZ_coord {K : Type} {ι : K → Type} {K' : Type} {ι' : K' → Type}
    (κ : K → K') (v : (Σ k, ι k) → Σ k, ι' k) {Ω : Type} [Field Ω] (y : (Σ k, ι' k) → Ω)
    (hκ : Function.Injective κ) (hv : ∀ p, (v p).1 = κ p.1) :
    imageZ v (mCoordIdeal y) = mCoordIdeal (y ∘ v) := by
  ext f
  simp only [imageZ, mCoordIdeal, Ideal.mem_comap, RingHom.mem_ker]
  change mConeMap y (rename v f) = 0 ↔ _
  rw [mConeMap_rename κ v y hv f]
  exact map_eq_zero_iff _ (rename_injective κ hκ)

theorem pullDeg_comp {K K' K'' : Type} (κ : K → K') (κ' : K' → K'')
    (hκ : Function.Injective κ) (hκ' : Function.Injective κ') (a : K → ℤ) :
    pullDeg (κ' ∘ κ) a = pullDeg κ' (pullDeg κ a) := by
  funext k''
  simp only [pullDeg]
  by_cases h' : ∃ k', κ' k' = k''
  · obtain ⟨k', rfl⟩ := h'
    rw [hκ'.extend_apply]
    by_cases h : ∃ k, κ k = k'
    · obtain ⟨k, rfl⟩ := h
      rw [hκ.extend_apply]
      exact (hκ'.comp hκ).extend_apply a 0 k
    · have h2 : ¬∃ k, (κ' ∘ κ) k = κ' k' := fun ⟨k, hk⟩ => h ⟨k, hκ' hk⟩
      rw [Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h2]
      rfl
  · have h2 : ¬∃ k, (κ' ∘ κ) k = k'' := fun ⟨k, hk⟩ => h' ⟨κ k, hk⟩
    rw [Function.extend_apply' _ _ _ h', Function.extend_apply' _ _ _ h2]

end GlobalTheory.CompanionTheory.Ar.Cmp.JoinBlock

namespace GlobalTheory.CompanionTheory.Ar.Cmp

open GlobalTheory.CompanionTheory.Ar.Cmp.JoinBlock in

theorem join_block_maps : (∀ (K₁ : Type) [Fintype K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)] (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)] (Ω : Type) (y₁ : (Σ k, ι₁ k) → Ω) (y₂ : (Σ k, ι₂ k) → Ω), IsBlockMap Sum.inl (joinInl ι₁ ι₂) ∧ IsBlockMap Sum.inr (joinInr ι₁ ι₂) ∧ joinVec y₁ y₂ ∘ joinInl ι₁ ι₂ = y₁ ∧ joinVec y₁ y₂ ∘ joinInr ι₁ ι₂ = y₂) ∧ (∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (κ : K → K') (v : (Σ k, ι k) → Σ k, ι' k) (Ω : Type) [Field Ω] (y : (Σ k, ι' k) → Ω), IsBlockMap κ v → imageZ v (mCoordIdeal y) = mCoordIdeal (y ∘ v)) ∧ (∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (K'' : Type) [Fintype K''] (ι'' : K'' → Type) [∀ k, Fintype (ι'' k)] (κ : K → K') (v : (Σ k, ι k) → Σ k, ι' k) (κ' : K' → K'') (v' : (Σ k, ι' k) → Σ k, ι'' k), IsBlockMap κ v → IsBlockMap κ' v' → IsBlockMap (κ' ∘ κ) (v' ∘ v) ∧ ∀ a, pullDeg (κ' ∘ κ) a = pullDeg κ' (pullDeg κ a)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro K₁ _ ι₁ _ K₂ _ ι₂ _ Ω y₁ y₂
    refine ⟨⟨Sum.inl_injective, ?_, fun _ => rfl, ?_⟩, ⟨Sum.inr_injective, ?_, fun _ => rfl, ?_⟩, ?_, ?_⟩
    · rintro ⟨k, i⟩ ⟨k', i'⟩ h
      cases h
      rfl
    · rintro ⟨k', i⟩ ⟨k, rfl⟩
      exact ⟨⟨k, i⟩, rfl⟩
    · rintro ⟨k, i⟩ ⟨k', i'⟩ h
      cases h
      rfl
    · rintro ⟨k', i⟩ ⟨k, rfl⟩
      exact ⟨⟨k, i⟩, rfl⟩
    · funext ⟨k, i⟩
      rfl
    · funext ⟨k, i⟩
      rfl
  · intro K _ ι _ K' _ ι' _ κ v Ω _ y h
    exact imageZ_coord κ v y h.1 h.2.2.1
  · intro K _ ι _ K' _ ι' _ K'' _ ι'' _ κ v κ' v' h h'
    obtain ⟨hκ, hv, hc, hs⟩ := h
    obtain ⟨hκ', hv', hc', hs'⟩ := h'
    refine ⟨⟨hκ'.comp hκ, hv'.comp hv, fun p => ?_, ?_⟩, pullDeg_comp κ κ' hκ hκ'⟩
    · simp [hc', hc]
    · rintro q ⟨k, hk⟩
      obtain ⟨q', rfl⟩ := hs' q ⟨κ k, hk⟩
      have h1 : q'.1 = κ k := hκ' ((hc' q').symm.trans hk.symm)
      obtain ⟨p, rfl⟩ := hs q' ⟨k, h1.symm⟩
      exact ⟨p, rfl⟩

end GlobalTheory.CompanionTheory.Ar.Cmp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEmbeddingIsoFinite
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge

namespace GlobalTheory.CompanionTheory.Ar.BT.FiniteIso

open GlobalTheory.CompanionTheory.Ar.BT.SubOrder

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T]

theorem isFinOpenSub_top (Γ : QFGroup R T) (hfin : IsFinite Γ.G.hom) : Γ.IsFinOpenSub ⊤ where
  finite := by
    have := hfin
    have hi : IsIso (⊤ : Γ.G.left.Opens).ι := (Scheme.topIso Γ.G.left).isIso_hom
    infer_instance
  one _ := trivial
  mul _ _ _ _ _ _ := trivial
  inv _ _ _ _ := trivial

noncomputable def secMap {X : Scheme.{0}} {A : Type} [CommRing A] (j : X ⟶ Spec (CommRingCat.of A)) : A →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ j.appTop).hom

theorem val_secMap (Γ : QFGroup R T) {A : Subalgebra R (T → R)} {j : Γ.G.left ⟶ Spec (CommRingCat.of A)}
    (hj : Γ.IsEmb A j) (t : T) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ (⊤ : Γ.G.left.Opens)) (a : A) :
    valAt (Γ.pt t).left ⊤ h (secMap j a) = algebraMap R (FractionRing R) ((a : T → R) t) := by
  have e0 : j.appLE ⊤ ⊤ (by simp) = j.appTop := Scheme.Hom.appLE_eq_app _
  have h2 : ⊤ ≤ ((Γ.pt t).left ≫ j) ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of A)).Opens) := by simp
  have h3 : ⊤ ≤ (Spec.map (CommRingCat.ofHom
    ((algebraMap R (FractionRing R)).comp ((Pi.evalRingHom (fun _ : T => R) t).comp A.val.toRingHom)))) ⁻¹ᵁ
      (⊤ : (Spec (CommRingCat.of A)).Opens) := by simp
  have e1 := valHom_appLE (Γ.pt t).left j (V := ⊤) (W := ⊤) (by simp) h h2
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)
  rw [e0, valHom_congr (hj.pt t) _ h2 h3, valHom_spec_top] at e1
  exact e1

theorem isIso_of_secMap_bijective {X : Scheme.{0}} [IsAffine X] {A : Type} [CommRing A]
    (j : X ⟶ Spec (CommRingCat.of A)) (hb : Function.Bijective (secMap j)) : IsIso j := by
  have h1 : IsIso ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ j.appTop) :=
    (ConcreteCategory.isIso_iff_bijective _).2 hb
  have h2 : IsIso j.appTop := IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (CommRingCat.of A)).inv j.appTop
  have e := Scheme.isoSpec_hom_naturality j
  have h3 : IsIso (j ≫ (Spec (CommRingCat.of A)).isoSpec.hom) := by
    rw [← e]; infer_instance
  exact IsIso.of_isIso_comp_right j (Spec (CommRingCat.of A)).isoSpec.hom

end GlobalTheory.CompanionTheory.Ar.BT.FiniteIso

namespace GlobalTheory.CompanionTheory.Ar.BT.FiniteIso

open GlobalTheory.CompanionTheory.Ar.BT.SubOrder

theorem isIso_of_finite : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤))), Γ.IsEmb (Γ.btOrder ⊤) j → IsFinite Γ.G.hom → IsIso j := by
  intro R _ _ _ T _ _ Γ j hj hfin
  have hF := isFinOpenSub_top Γ hfin
  have hU := isAffineOpen_of_fin Γ hF
  have : IsAffine Γ.G.left := by
    have := hfin
    exact isAffine_of_isAffineHom Γ.G.hom
  obtain ⟨H, A', hH, hopf, hA'⟩ := GlobalTheory.T.finite_open_hopf_order R T Γ ⊤ hF
  have htop : ∀ t, ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ (⊤ : Γ.G.left.Opens) := fun t => by simp
  have hHt : ∀ t, t ∈ H := fun t => (hH t).2 (htop t)
  have inj : Function.Injective (algebraMap R (FractionRing R)) := IsFractionRing.injective R _
  letI : Algebra R Γ(Γ.G.left, ⊤) := (secRho Γ hU).toAlgebra
  have hρ : hU.fromSpec ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R Γ(Γ.G.left, ⊤))) :=
    fromSpec_hom Γ hU
  have hfinite := sec_finite hρ hF
  have hval : ∀ (s : Γ(Γ.G.left, ⊤)) (t : T),
      ∃ r : R, algebraMap R (FractionRing R) r = valAt (Γ.pt t).left ⊤ (htop t) s := by
    intro s t
    have h1 : IsIntegral R s := Algebra.IsIntegral.isIntegral s
    exact IsIntegrallyClosed.isIntegral_iff.1 (h1.map (valAlg hρ t (htop t)))
  apply isIso_of_secMap_bijective
  constructor
  · rw [injective_iff_map_eq_zero]
    intro a ha
    apply Subtype.ext
    funext t
    apply inj
    have e := val_secMap Γ hj t (htop t) a
    rw [ha, ← valHom_apply, map_zero] at e
    simpa using e.symm
  · intro s
    choose f hf using hval s
    let f' : H → R := fun h => f h
    have hf' : f' ∈ A' := (hA' f').2 ⟨s, fun t h => (hf t).symm⟩
    have hind : f' ∈ indOrder (MonoidHom.id H) A' := by
      rw [GlobalTheory.T.hopf_order_induction_id R H A' hopf]
      exact hf'
    have hmem : f ∈ Γ.btOrder ⊤ := by
      apply Algebra.subset_adjoin
      intro t g _
      obtain ⟨s', hs'⟩ := (hA' _).1 (hind ⟨t, hHt t⟩)
      exact ⟨⊤, trivial, s', fun u h => hs' ⟨u, hHt u⟩ h⟩
    refine ⟨⟨f, hmem⟩, ?_⟩
    rw [← sub_eq_zero]
    apply GlobalTheory.T.section_eq_zero_of_values R T Γ ⊤
    intro t h
    rw [← valHom_apply, map_sub, valHom_apply, valHom_apply, val_secMap Γ hj, hf, sub_self]

end GlobalTheory.CompanionTheory.Ar.BT.FiniteIso
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEqOfLeStatement
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.btOrder_eq_of_le_of_isFinOpenSub : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U U' : Γ.G.left.Opens), Γ.IsFinOpenSub U → Γ.IsFinOpenSub U' → U' ≤ U → Γ.btOrder U = Γ.btOrder U' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.QFGroup.btOrder_eq_of_le | exact GlobalTheory.CompanionTheory.Ar.BT.QFGroup.btOrder_eq_of_le | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.QFGroup.btOrder_eq_of_le <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartFrameMatrixRegularStatement
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_frame_matrix_regular : ∀ (Ω : Type) [Field Ω] (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) (x : κ → Ω) (S : Type) [Fintype S] (r n m : S → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω E) (cc : ∀ s, Fin (r s) → E) (M : ∀ s, Matrix (Fin (n s)) (Fin (r s)) Ω) (T : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) (c₀ : κ) (J : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1)) (g : Ω), x c₀ ≠ 0 → g ∈ chartSub x c₀ → g ≠ 0 → (∀ s j l, φ s j (cc s l) = x c₀ ^ m s * (M s * T s) j l) → (∀ q, stepMinor (flagB M T q.1) q.2 (J q) ≠ 0) → algebraMap Ω (GenField Ω r) g ∈ chartSub (flagCoord κ x φ cc) ((c₀, J) : FlagIx κ n r) ∧ locSub (chartSub (flagCoord κ x φ cc) ((c₀, J) : FlagIx κ n r)) (algebraMap Ω (GenField Ω r) g) = ratioRing (locSub (chartSub x c₀) g) (flagB M T) J := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.chartRing_eq_ratioRing | exact GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.chartRing_eq_ratioRing | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.chartRing_eq_ratioRing <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartPrimeExistsUniquePointStatement
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_prime_existsUnique_point : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (c : κ), x c ≠ 0 → ∀ P : Ideal (chRing o x c), P.IsPrime → ∃! p : Cpt M.ξ, InChart M.ξ x c p ∧ ∀ u : chRing o x c, u ∈ P ↔ ¬ unitAt M.ξ p (u : Ω) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.chart_prime_point | exact GlobalTheory.CompanionTheory.Ar.chart_prime_point | (intros; apply GlobalTheory.CompanionTheory.Ar.chart_prime_point <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartUnitBasicOpenStatement
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_unit_basic_open : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (c : κ) (p : Cpt M.ξ) (U : M.X.Opens), InChart M.ξ x c p → p.1 ∈ U → ∃ f ∈ chRing o x c, unitAt M.ξ p f ∧ ∀ q : Cpt M.ξ, InChart M.ξ x c q → unitAt M.ξ q f → q.1 ∈ U := by
  first | exact @GlobalTheory.CompanionTheory.Ar.chRing_basicOpen_basis | exact GlobalTheory.CompanionTheory.Ar.chRing_basicOpen_basis | (intros; apply GlobalTheory.CompanionTheory.Ar.chRing_basicOpen_basis <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoherentLatticeClosureStatement
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coherent_lattice_closure : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (E' : Type) [AddCommGroup E'] [Module Ω E'] (L L' : Lat ξ E) (T : Set (Cpt ξ)), (∀ r V, L.IsVBOn T r V → L.IsCohOn T) ∧ (∀ φ : E →ₗ[Ω] E', L.IsCohOn T → (L.map φ).IsCohOn T) ∧ (L.IsCohOn T → L'.IsCohOn T → Lat.IsCohOn (fun p => L p ⊔ L' p : Lat ξ E) T) ∧ (∀ (r : ℕ) (V : Submodule Ω E) (a : Ω), a ≠ 0 → L.IsVBOn T r V → (L.scale a).IsVBOn T r V) ∧ (∀ (r : ℕ) (V : Submodule Ω E), L.IsCohOn T → (∀ p ∈ T, ∃ b : Fin r → E, Submodule.span Ω (Set.range b) = V ∧ L.IsFrameAt b p) → L.IsVBOn T r V) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.coh_vb_images_sums_multiples | exact GlobalTheory.CompanionTheory.Ar.coh_vb_images_sums_multiples | (intros; apply GlobalTheory.CompanionTheory.Ar.coh_vb_images_sums_multiples <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConnectedSpecialFibreConstant
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem unitAt_of_localLifts_of_unitAt : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s] (ϖ : O), Irreducible ϖ → Function.Injective (algebraMap O Ω) → ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → IsCptGen ξ → _root_.IsConnected (zeroSet ξ (algebraMap O Ω ϖ)) → ∀ h : Cpt ξ → Ω, (∀ p : Cpt ξ, ¬ unitAt ξ p (algebraMap O Ω ϖ) → ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → ¬ unitAt ξ q (algebraMap O Ω ϖ) → h p ∈ regAt ξ q ∧ (h p - h q) / algebraMap O Ω ϖ ∈ regAt ξ q) → (∃ p, ¬ unitAt ξ p (algebraMap O Ω ϖ) ∧ unitAt ξ p (h p)) → ∀ p, ¬ unitAt ξ p (algebraMap O Ω ϖ) → unitAt ξ p (h p) :=
  @PositivityTheory.Xgn.function_on_connected_fibre_unit

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsProductRefinementStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coords_product_refinement : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (o : Type) [CommRing o] [Algebra o Ω] (κ κ' : Type) (x : κ → Ω) (s : κ' → Ω), CoordTie o ξ x → (∀ p : Cpt ξ, ∃ i, InChart ξ s i p) → [Finite κ] → [Finite κ'] → ∃ n : ℕ, CoordTie o ξ fun q : (Fin n → κ) × κ × κ' => (∏ a, x (q.1 a)) * x q.2.1 * s q.2.2 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.coordTie_add_block | exact GlobalTheory.CompanionTheory.Ar.coordTie_add_block | (intros; apply GlobalTheory.CompanionTheory.Ar.coordTie_add_block <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominantSmoothMapCoordsStatement
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dominant_smooth_map_coords : ∀ (X X' : Scheme.{0}) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (ξ : Spec (CommRingCat.of Ω₀) ⟶ X)
    (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (f : X' ⟶ X) (i : Ω₀ →+* Ω) (κ κ' : Type) (x : κ → Ω₀) (x' : κ' → Ω),
    (∀ q : X, genPt ξ ⤳ q) → (∀ q : X', genPt ξ' ⤳ q) → CoordTie ℤ ξ x → CoordTie ℤ ξ' x' →
    GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → Smooth f → ∀ (c : κ) (c' : κ'), x c ≠ 0 → x' c' ≠ 0 →
    (∀ j, i (x j / x c) ∈ Algebra.adjoin ℤ (Set.range fun j' => x' j' / x' c')) →
    ∃ φ : Algebra.adjoin ℤ (Set.range fun j => x j / x c) →+* Algebra.adjoin ℤ (Set.range fun j' => x' j' / x' c'),
      (∀ a, ((φ a : Algebra.adjoin ℤ (Set.range fun j' => x' j' / x' c')) : Ω) = i a) ∧ φ.Smooth := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChartSmooth.smooth_chartRing | exact GlobalTheory.CompanionTheory.Ar.ChartSmooth.smooth_chartRing | (intros; apply GlobalTheory.CompanionTheory.Ar.ChartSmooth.smooth_chartRing <;> assumption)
end

