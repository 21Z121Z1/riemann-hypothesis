import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenericCentreSpecializes
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0001
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0022
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0003

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.DegreeZeroCurvePositive
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace PositivityTheory.Xgn.CurvePositivity

theorem change_gen {Ω : Type} [Field Ω] (σ π e f : Ω) (M : ℕ) (hf : f ≠ 0) :
    π / (σ / e) ^ M = π / (σ / f) ^ M * (e / f) ^ M := by
  have hfM : f ^ M ≠ 0 := pow_ne_zero _ hf
  rw [div_pow, div_pow, div_pow, div_div_eq_mul_div, div_div_eq_mul_div]
  by_cases hσ : σ ^ M = 0
  · simp [hσ]
  · field_simp

theorem val_one {K : Type} [Field K] (C : Crv.ACurve K) (hw : ∀ i, 0 < C.w i) (c : K) (hc : c ≠ 0)
    (r t : C.I → K) (M : ℕ) (hr : ∀ i, r i ≠ 0) (hfin : {i | C.v i (r i) ≠ 1}.Finite)
    (hd : ∑ᶠ i, (C.w i : ℤ) * (-WithZero.log (C.v i (r i))) = 0)
    (ht : ∀ i, C.v i (t i) ≤ 1) (hct : ∀ i, c = t i * r i ^ M) (i : C.I) : C.v i (t i) = 1 := by
  have ht0 : ∀ j, t j ≠ 0 := fun j h => hc (by rw [hct j, h, zero_mul])
  have hvt : ∀ j, C.v j (t j) ≠ 0 := fun j => (Valuation.ne_zero_iff _).2 (ht0 j)
  have hvr : ∀ j, C.v j (r j) ≠ 0 := fun j => (Valuation.ne_zero_iff _).2 (hr j)
  have hL : ∀ j, WithZero.log (C.v j c) =
      WithZero.log (C.v j (t j)) + (M : ℤ) * WithZero.log (C.v j (r j)) := by
    intro j
    rw [hct j, map_mul, map_pow, WithZero.log_mul (hvt j) (pow_ne_zero _ (hvr j)), WithZero.log_pow]
    simp
  have hle : ∀ j, WithZero.log (C.v j (t j)) ≤ 0 := by
    intro j
    have := (WithZero.log_le_log (hvt j) one_ne_zero).2 (ht j)
    rwa [WithZero.log_one] at this
  set A : C.I → ℤ := fun j => (C.w j : ℤ) * WithZero.log (C.v j (t j)) with hA
  set B : C.I → ℤ := fun j => (C.w j : ℤ) * WithZero.log (C.v j c) with hB
  set D : C.I → ℤ := fun j => (C.w j : ℤ) * (-WithZero.log (C.v j (r j))) with hD
  have hsB : (Function.support B).Finite := (C.fin c hc).subset (fun j hj => by
    simp only [Function.mem_support, hB] at hj
    intro h1; apply hj; rw [h1, WithZero.log_one, mul_zero])
  have hsD : (Function.support D).Finite := hfin.subset (fun j hj => by
    simp only [Function.mem_support, hD] at hj
    intro h1; apply hj; rw [h1, WithZero.log_one, neg_zero, mul_zero])
  have hABD : A = fun j => B j + (M : ℤ) * D j := by
    funext j; simp only [hA, hB, hD]; rw [hL j]; ring
  have hsMD : (Function.support fun j => (M : ℤ) * D j).Finite :=
    hsD.subset (Function.support_mul_subset_right _ _)
  have hsA : (Function.support A).Finite := by
    rw [hABD]; exact (hsB.union hsMD).subset (Function.support_add _ _)
  have hsum : ∑ᶠ j, A j = 0 := by
    rw [hABD, finsum_add_distrib hsB hsMD, ← mul_finsum]
    simp only [hB, hD]
    rw [C.prod c hc, hd, mul_zero, add_zero]
  have hnn : ∀ j, 0 ≤ -A j := fun j => by
    simp only [hA]; have := hle j; have := hw j; nlinarith
  have hsA' : (Function.support fun j => -A j).Finite :=
    hsA.subset (fun j hj => by simpa [Function.mem_support] using hj)
  have h1 := single_le_finsum i hsA' hnn
  rw [finsum_neg_distrib, hsum, neg_zero] at h1
  have h2 : WithZero.log (C.v i (t i)) = 0 := by
    have h3 : A i = 0 := by have := hnn i; linarith
    simp only [hA] at h3
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact absurd h4 (by have := hw i; omega)
    · exact h4
  rw [← WithZero.exp_log (hvt i), h2, WithZero.exp_zero]

end PositivityTheory.Xgn.CurvePositivity

theorem PositivityTheory.Xgn.degree_zero_curve_positive : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] (s : X ⟶ Spec (CommRingCat.of O)) [IsSeparated s] [LocallyOfFiniteType s] (ϖ : Ω) (L : Lat ξ Ω) (σ π : Ω) (M : ℕ) (Γ : FibreCurve ξ ϖ), IsCptGen ξ → L.IsVB 1 ⊤ → 0 < M → Γ.HasDeg L 0 → (∀ (p : Cpt ξ) (e : Ω), L.IsGenAt p e → π / (σ / e) ^ M ∈ regAt ξ p) → (∀ e, L.IsGenAt ⟨centre Γ.η, Γ.η_spec⟩ e → unitAt ξ ⟨centre Γ.η, Γ.η_spec⟩ (π / (σ / e) ^ M)) → ∀ (i : Γ.C.I) (h : genPt ξ ⤳ centre (Γ.z i)) (e : Ω), L.IsGenAt ⟨centre (Γ.z i), h⟩ e → unitAt ξ ⟨centre (Γ.z i), h⟩ (π / (σ / e) ^ M) := by
  intro X Ω _ ξ O _ s _ _ ϖ L σ π M Γ hξ _ _ hdeg hreg hunit i h e he
  obtain ⟨e0, f, r, he0, hf, hr, hfin, hd⟩ := hdeg
  have hf' : ∀ j, L.IsGenAt ⟨centre (Γ.z j), Γ.z_spec j⟩ (f j) := fun j => (hf j).2
  obtain ⟨c, hc⟩ := ProjectiveLinePlaces.valAt_of_unit Γ.η_spec (hunit e0 he0)
  choose g hg using fun j => hreg _ _ (hf' j)
  let t : ∀ j, (Γ.C.v j).valuationSubring := fun j => (Scheme.stalkClosedPointTo (Γ.z j)).hom (g j)
  have hz : ∀ j, ValAt ξ (Γ.z j) (π / (σ / f j) ^ M) (t j) := fun j => ⟨Γ.z_spec j, g j, hg j, rfl⟩
  have hη : ∀ j, ValAt ξ Γ.η (π / (σ / f j) ^ M) (t j : Γ.κ) := fun j =>
    ProjectiveLinePlaces.valAt_restrict _ (Γ.z_gen j) Γ.η_spec (hz j)
  have hct : ∀ j, (c : Γ.κ) = (t j : Γ.κ) * r j ^ M := fun j => by
    have h2 := CoordModel.valAt_mul (hη j) (ProjectiveLinePlaces.valAt_pow (hr j).2 M)
    rw [← PositivityTheory.Xgn.CurvePositivity.change_gen σ π e0 (f j) M (hf' j).1] at h2
    exact CoordModel.valAt_unique hξ hc h2
  have hv := PositivityTheory.Xgn.CurvePositivity.val_one Γ.C Γ.w_pos c c.ne_zero r (fun j => (t j : Γ.κ)) M
    (fun j => (hr j).1) hfin hd (fun j => (t j).2) hct i
  have ht0 : (t i : Γ.κ) ≠ 0 := fun h0 => by simp [h0] at hv
  have hu : IsUnit (t i) := by
    refine IsUnit.of_mul_eq_one ⟨(t i : Γ.κ)⁻¹, ?_⟩ (Subtype.ext (mul_inv_cancel₀ ht0))
    change Γ.C.v i _ ≤ 1
    rw [map_inv₀, hv, inv_one]
  have hgu : IsUnit (g i) := (Scheme.isLocalHom_stalkClosedPointTo' (Γ.z i)).map_nonunit (g i) hu
  obtain ⟨u, hu1, hu2⟩ := (CptModel.unitAt_iff ξ _ _).1 (ProjectiveLinePlaces.unitAt_div he (hf' i))
  refine (CptModel.unitAt_iff ξ _ _).2 ⟨g i * u ^ M, hgu.mul (hu1.pow M), ?_⟩
  rw [PositivityTheory.Xgn.CurvePositivity.change_gen σ π e (f i) M (hf' i).1, map_mul, map_pow, hu2]
  exact congrArg (· * (e / f i) ^ M) (hg i)
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ExistsCurveInFibreDegree
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace PositivityTheory.Xgn.CurveInFibre

theorem valAt_inv {X : Scheme.{0}} {Ω K : Type} [Field Ω] [Field K] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {η : Spec (CommRingCat.of K) ⟶ X} {a : Ω} {r : K} (h : ValAt ξ η a r) (hr : r ≠ 0) :
    ValAt ξ η a⁻¹ r⁻¹ := by
  obtain ⟨hz, s, rfl, rfl⟩ := h
  have hl := Scheme.isLocalHom_stalkClosedPointTo η
  have hs : IsUnit s := hl.map_nonunit s (IsUnit.mk0 _ hr)
  obtain ⟨u, rfl⟩ := hs
  refine ⟨hz, ↑u⁻¹, ?_, ?_⟩
  · exact map_units_inv _ u
  · exact map_units_inv _ u

theorem finite_not_integral {K O A : Type} [Field K] [CommRing O] [CommRing A] (C : Crv.ACurve K) (g : O →+* A)
    (hg : g.FiniteType) (φ : A →+* K) (hO : ∀ i a, φ (g a) ∈ (C.v i).valuationSubring) :
    {i | ¬ ∀ a, φ a ∈ (C.v i).valuationSubring}.Finite := by
  letI := g.toAlgebra
  obtain ⟨t, ht⟩ := (show Algebra.FiniteType O A from hg).out
  have hfin : ∀ a : A, {i | φ a ∉ (C.v i).valuationSubring}.Finite := by
    intro a
    by_cases h0 : φ a = 0
    · simp [h0]
    · exact (C.fin _ h0).subset fun i hi h1 => hi (le_of_eq h1)
  refine (t.finite_toSet.biUnion fun a _ => hfin a).subset fun i hi => ?_
  by_contra hc
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_not] at hc
  refine hi fun a => ?_
  have ha : a ∈ Algebra.adjoin O (t : Set A) := ht ▸ Algebra.mem_top
  induction ha using Algebra.adjoin_induction with
  | mem y hy => exact hc y hy
  | algebraMap r => exact hO i r
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | mul y z _ _ hy hz => rw [map_mul]; exact mul_mem hy hz

theorem ae_centre {X : Scheme.{0}} {K O : Type} [Field K] [CommRing O] (s : X ⟶ Spec (CommRingCat.of O))
    [IsSeparated s] [LocallyOfFiniteType s] (C : Crv.ACurve K) (η : Spec (CommRingCat.of K) ⟶ X)
    (z : ∀ i, Spec (CommRingCat.of (C.v i).valuationSubring) ⟶ X)
    (hz : ∀ i, Spec.map (CommRingCat.ofHom (C.v i).valuationSubring.subtype) ≫ z i = η)
    (U : X.Opens) (hU : centre η ∈ U) : {i | centre (z i) ∉ U}.Finite := by
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset hU
  have hV : IsAffineOpen V := hV
  have hr : Set.range η ⊆ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]
    rintro _ ⟨p, rfl⟩
    have : p = IsLocalRing.closedPoint K := Subsingleton.elim (α := PrimeSpectrum K) _ _
    rw [this]
    exact hxV
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift hV.fromSpec η hr)
  have hφ' : Spec.map φ ≫ hV.fromSpec = η := by rw [hφ, IsOpenImmersion.lift_fac]
  obtain ⟨g, hg⟩ := Spec.map_surjective (hV.fromSpec ≫ s)
  have hgf : g.hom.FiniteType :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 (hg ▸ inferInstance)
  choose ψ hψ using fun i => Spec.map_surjective (z i ≫ s)
  have hsq : ∀ i, ψ i ≫ CommRingCat.ofHom (C.v i).valuationSubring.subtype = g ≫ φ := fun i => by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, hψ, hg, ← Category.assoc, ← Category.assoc, hz, hφ']
  have hsq' : ∀ i a, φ.hom (g.hom a) = ((ψ i).hom a : K) := fun i a =>
    (congrArg (fun f => f.hom a) (hsq i)).symm
  refine (finite_not_integral C g.hom hgf φ.hom fun i a => ?_).subset fun i hi hc => hi ?_
  · rw [hsq' i a]
    exact ((ψ i).hom a).2
  · let χ : Γ(X, V) ⟶ CommRingCat.of (C.v i).valuationSubring :=
      CommRingCat.ofHom (φ.hom.codRestrict (C.v i).valuationSubring hc)
    haveI : IsDominant (Spec.map (CommRingCat.ofHom (C.v i).valuationSubring.subtype)) :=
      ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (C.v i).valuationSubring.subtype).2 (by
        rw [(RingHom.injective_iff_ker_eq_bot _).1 Subtype.val_injective]
        exact bot_le)⟩
    have e : z i = Spec.map χ ≫ hV.fromSpec := by
      refine ext_of_isDominant_of_isSeparated s ?_
        (Spec.map (CommRingCat.ofHom (C.v i).valuationSubring.subtype)) ?_
      · rw [Category.assoc, ← hg, ← hψ, ← Spec.map_comp]
        congr 1
        ext a
        exact (hsq' i a).symm
      · rw [hz, ← Category.assoc, ← Spec.map_comp, ← hφ']
        rfl
    refine hVU ?_
    change centre (z i) ∈ (V : Set X)
    rw [e, ← hV.range_fromSpec]
    exact ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩

end PositivityTheory.Xgn.CurveInFibre

theorem PositivityTheory.Xgn.exists_curve_in_fibre_degree : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] (s : X ⟶ Spec (CommRingCat.of O)) [IsSeparated s] [LocallyOfFiniteType s] (ϖ : Ω) (Γ : FibreCurve ξ ϖ), IsCptGen ξ → ∃ Y : Crv.CurveIn Γ.C Γ.η, Y.x = Γ.z ∧ ∀ (L : Lat ξ Ω) (n : ℤ), L.IsVB 1 ⊤ → (Γ.HasDeg L n ↔ Y.IsDeg L n) := by
  intro X Ω _ ξ O _ s _ _ ϖ Γ _
  refine ⟨⟨Γ.z, Γ.z_gen, PositivityTheory.Xgn.CurveInFibre.ae_centre s Γ.C Γ.η Γ.z Γ.z_gen⟩, rfl, fun L n _ => ⟨?_, ?_⟩⟩
  · rintro ⟨e, f, r, he, hf, hr, hfin, hd⟩
    refine ⟨Γ.η_spec, Γ.z_spec, e, f, fun i => (r i)⁻¹, he, fun i => (hf i).2, fun i => ⟨inv_ne_zero (hr i).1, ?_⟩,
      ?_, ?_⟩
    · rw [← inv_div]
      exact PositivityTheory.Xgn.CurveInFibre.valAt_inv (hr i).2 (hr i).1
    · simpa using hfin
    · rw [← hd]
      simp
  · rintro ⟨h₀, h, e, f, r, he, hf, hr, hfin, hd⟩
    refine ⟨e, f, fun i => (r i)⁻¹, he, fun i => ⟨h i, hf i⟩, fun i => ⟨inv_ne_zero (hr i).1, ?_⟩, ?_, ?_⟩
    · rw [← inv_div]
      exact PositivityTheory.Xgn.CurveInFibre.valAt_inv (hr i).2 (hr i).1
    · simpa using hfin
    · rw [hd]
      simp
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ImageLatticeBaseChange
section
open GlobalTheory.CompanionTheory.Ar.Num

namespace PositivityTheory.Xgn.ImageLatticeBaseChange

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem mem_dotDual (R : Subalgebra o Ω) {m : ℕ} (L : AddSubgroup (Fin m → Ω)) (w : Fin m → Ω) :
    w ∈ dotDual R L ↔ ∀ v ∈ L, v ⬝ᵥ w ∈ R := by
  simp [dotDual, AddSubgroup.mem_iInf]

theorem mem_stdLat (R : Subalgebra o Ω) {ι : Type} (v : ι → Ω) :
    v ∈ stdLat R ι ↔ ∀ i, v i ∈ R := by
  simp [stdLat, AddSubgroup.mem_pi]

theorem isBaseChange_bcMap (C : Type) [Field C] [Algebra Ω C] (m : ℕ) :
    IsBaseChange C (bcMap Ω C (Fin m)) :=
  IsBaseChange.finitePow (Fin m) (IsBaseChange.linearMap Ω C)

theorem locFree_div (R : Subalgebra o Ω) {m : ℕ} {w : Ω} (hw : w ≠ 0)
    (L : AddSubgroup (Fin m → Ω)) (hL : ∀ v, v ∈ L ↔ ∀ i, w * v i ∈ R) : LocFree R m L := by
  have hb : ∀ a : Fin m → Ω, (∑ q, a q • w⁻¹ • (Pi.single q 1 : Fin m → Ω)) = fun i => a i * w⁻¹ := by
    intro a
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  refine ⟨?_, 1, fun _ => 1, fun _ => 1, fun _ => R.one_mem, fun _ => R.one_mem, by simp,
    fun _ => ⟨fun q => w⁻¹ • (Pi.single q 1 : Fin m → Ω), ?_, ?_, ?_⟩⟩
  · intro a ha e he
    rw [hL] at he ⊢
    intro i
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mul_left_comm]
    exact R.mul_mem ha (he i)
  · have h := (Pi.basisFun Ω (Fin m)).linearIndependent.map'
      (LinearEquiv.smulOfNeZero Ω (Fin m → Ω) w⁻¹ (inv_ne_zero hw)).toLinearMap
      (LinearEquiv.ker _)
    simpa [Function.comp_def] using h
  · rw [Submodule.eq_top_iff']
    intro x
    have hx : x = ∑ q, (w * x q) • (w⁻¹ • (Pi.single q 1 : Fin m → Ω)) := by
      rw [hb (fun q => w * x q)]
      funext i
      field_simp
    rw [hx]
    exact Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)
  · intro e
    constructor
    · rintro ⟨k, hk⟩
      simp only [one_pow, one_smul] at hk
      refine ⟨fun q => w * e q, fun q => ⟨0, by simpa using (hL e).1 hk q⟩, ?_⟩
      rw [hb]
      funext i
      field_simp
    · rintro ⟨a, ha, rfl⟩
      refine ⟨0, ?_⟩
      simp only [pow_zero, one_smul]
      rw [hb, hL]
      intro i
      obtain ⟨k, hk⟩ := ha i
      simp only [one_pow, one_mul] at hk
      field_simp
      exact hk

end PositivityTheory.Xgn.ImageLatticeBaseChange

private theorem dotDual_spanOver_bcMap_eq {o Ω C : Type} [CommRing o] [Field Ω] [Field C] [Algebra o Ω] [Algebra o C]
    [Algebra Ω C] (R : Subalgebra o Ω) (RC : Subalgebra o C) (hR : ∀ a ∈ R, algebraMap Ω C a ∈ RC)
    {m k : ℕ} (A : AddSubgroup (Fin m → Ω)) (a γ : Fin k → Fin m → Ω) (ha : ∀ i, a i ∈ A)
    (hγ : ∀ i, γ i ∈ dotDual R A) (hid : ∀ l j, ∑ i, a i l * γ i j = if l = j then 1 else 0) :
    dotDual RC (spanOver RC (bcMap Ω C (Fin m) '' A)) = spanOver RC (bcMap Ω C (Fin m) '' dotDual R A) := by
  have hb : ∀ (v : Fin m → Ω) j, bcMap Ω C (Fin m) v j = algebraMap Ω C (v j) := fun _ _ => rfl
  have hdot : ∀ u v : Fin m → Ω,
      bcMap Ω C (Fin m) u ⬝ᵥ bcMap Ω C (Fin m) v = algebraMap Ω C (u ⬝ᵥ v) := by
    intro u v
    simp only [dotProduct, hb, map_sum, map_mul]
  apply le_antisymm
  · intro y hy
    rw [PositivityTheory.Xgn.ImageLatticeBaseChange.mem_dotDual] at hy
    have hy' : y = ∑ i, (bcMap Ω C (Fin m) (a i) ⬝ᵥ y) • bcMap Ω C (Fin m) (γ i) := by
      funext j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, dotProduct, hb]
      calc y j = ∑ l, y l * algebraMap Ω C (if l = j then 1 else 0) := by
            simp [apply_ite]
        _ = ∑ i, (∑ l, algebraMap Ω C (a i l) * y l) * algebraMap Ω C (γ i j) := by
            simp_rw [← hid, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
            ring
    rw [hy']
    refine AddSubgroup.sum_mem _ fun i _ => AddSubgroup.subset_closure
      ⟨_, hy _ (AddSubgroup.subset_closure ⟨1, RC.one_mem, _, ⟨a i, ha i, rfl⟩, (one_smul _ _).symm⟩),
        _, ⟨γ i, hγ i, rfl⟩, rfl⟩
  · refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨c, hc, _, ⟨g, hg, rfl⟩, rfl⟩
    have hg' := (PositivityTheory.Xgn.ImageLatticeBaseChange.mem_dotDual R A g).1 hg
    rw [SetLike.mem_coe, PositivityTheory.Xgn.ImageLatticeBaseChange.mem_dotDual]
    intro v hv
    induction hv using AddSubgroup.closure_induction with
    | mem v hv =>
      obtain ⟨d, hd, _, ⟨u, hu, rfl⟩, rfl⟩ := hv
      rw [smul_dotProduct, dotProduct_smul, hdot, smul_eq_mul, smul_eq_mul]
      exact RC.mul_mem hd (RC.mul_mem hc (hR _ (hg' u hu)))
    | zero => simp
    | add u v _ _ hu hv =>
      rw [add_dotProduct]
      exact add_mem hu hv
    | neg u _ hu =>
      rw [neg_dotProduct]
      exact neg_mem hu

private theorem exists_dual_pair_af_of_summand_locFree {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F]
    [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ)
    (χ : F → Ω) (h0 : χ 0 = 0) (h1 : χ 1 = 1) (hS : Summand (D.l1 R p) (linMap n χ).range)
    (hl1 : LocFree R (Fintype.card F ^ n) (D.l1 R p)) :
    ∃ (k : ℕ) (a γ : Fin k → Fin n → Ω), (∀ i, a i ∈ D.af R p χ) ∧ (∀ i, γ i ∈ dotDual R (D.af R p χ)) ∧
      ∀ l j, ∑ i, a i l * γ i j = if l = j then 1 else 0 := by
  classical
  obtain ⟨π, hπ, hπL⟩ := PositivityTheory.Xgn.GoodLatticeBaseChange.af_retract R D p χ h0 h1 hS
  let L1 : Submodule R ((Fin n → F) → Ω) :=
    { carrier := D.l1 R p
      add_mem' := fun ha hb => add_mem ha hb
      zero_mem' := zero_mem _
      smul_mem' := fun c v hv => hl1.1 c c.2 v hv }
  obtain ⟨k, φ, u, hφ, hsum⟩ := GlobalTheory.CompanionTheory.Ar.Num.LocFreeProj.exists_dualBasis (L := L1) hl1
  refine ⟨k * Fintype.card F ^ n, fun i => π (u (finProdFinEquiv.symm i)),
    fun i j => φ (finProdFinEquiv.symm i) (linMap n χ (Pi.single j 1)), ?_, ?_, ?_⟩
  · intro i
    exact hπL _ (u _).2
  · intro i
    rw [PositivityTheory.Xgn.ImageLatticeBaseChange.mem_dotDual]
    intro v hv
    have hv' : v = ∑ j, v j • (Pi.single j 1 : Fin n → Ω) := by
      funext l
      simp [Finset.sum_apply, Pi.single_apply]
    have hval : v ⬝ᵥ (fun j => φ (finProdFinEquiv.symm i) (linMap n χ (Pi.single j 1))) =
        φ (finProdFinEquiv.symm i) (linMap n χ v) := by
      conv_rhs => rw [hv']
      simp only [map_sum, map_smul, smul_eq_mul, dotProduct]
    rw [hval]
    exact hφ _ _ hv
  · intro l j
    have h := congrArg (fun e => π e l) (hsum (linMap n χ (Pi.single j 1)))
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hπ] at h
    rw [show (if l = j then (1 : Ω) else 0) = (Pi.single j 1 : Fin n → Ω) l by simp [Pi.single_apply], ← h]
    exact (finProdFinEquiv.symm.sum_comp
      (fun x => π (u x) l * φ x (linMap n χ (Pi.single j 1)))).trans
      (Finset.sum_congr rfl fun x _ => mul_comm _ _)

private theorem map_snd_spanOver_prodMap_eq {o C : Type} [CommRing o] [Field C] [Algebra o C] (RC : Subalgebra o C)
    {X Y Xc Yc : Type} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Xc] [Module C Xc] [AddCommGroup Yc]
    [Module C Yc] (f : X → Xc) (g : Y → Yc) (S : AddSubgroup (X × Y)) :
    AddSubgroup.map (AddMonoidHom.snd Xc Yc) (spanOver RC (Prod.map f g '' S)) =
      spanOver RC (g '' AddSubgroup.map (AddMonoidHom.snd X Y) S) := by
  unfold spanOver
  rw [AddMonoidHom.map_closure]
  congr 1
  ext v
  constructor
  · rintro ⟨_, ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
    exact ⟨a, ha, g x.2, ⟨x.2, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
  · rintro ⟨a, ha, _, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
    exact ⟨a • Prod.map f g x, ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩

open PositivityTheory.Xgn.ImageLatticeBaseChange PositivityTheory.Xgn.A_graph_restrict_bc in
theorem PositivityTheory.Xgn.image_lattice_base_change : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → D.Good₁ R p χ → (∀ τ, mulLat w (stdLat R _) ≤ D.af R p (χ τ)) → ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ τ, (D.bc RC).imH RC p τ (fun a => algebraMap Ω C (χ τ a)) = spanOver RC (bcMap Ω C _ '' D.imH R p τ (χ τ)) := by
  intro o Ω _ _ _ F _ _ _ n Sg r s D R p w χ hC hB hG hw C _ _ _ _ RC hR τ
  obtain ⟨hp, hwR, ⟨c, hc, hpc⟩, h01, hχ⟩ := hC
  have hw0 : w ≠ 0 := by
    rintro rfl
    apply hp
    rw [hpc, mul_zero]
  obtain ⟨hχ0, hχ1, hχR⟩ := hχ τ
  obtain ⟨k, a, γ, ha, hγ, hid⟩ := exists_dual_pair_af_of_summand_locFree D R p (χ τ) hχ0 hχ1 (hG.lin τ) hG.l1
  have hhh : (D.bc RC).hh RC p (fun x => algebraMap Ω C (χ τ x)) =
      spanOver RC (bcMap Ω C (Fin n) '' D.hh R p (χ τ)) := by
    unfold LieLatticeData.hh
    rw [PositivityTheory.Xgn.GoodLatticeBaseChange.af_bc R RC D p hR (χ τ) hχ0 hχ1 (hG.lin τ)]
    exact dotDual_spanOver_bcMap_eq R RC hR (D.af R p (χ τ)) a γ ha hγ hid
  have hstab : ∀ a ∈ R, ∀ v ∈ D.Del τ, a • v ∈ D.Del τ := fun a ha => (hB.stable τ a ha).2.1
  have hfst : ∀ v, v ∈ AddSubgroup.map (AddMonoidHom.fst _ _) (D.Del τ) ↔ ∀ i, w * v i ∈ R := by
    intro v
    rw [AddSubgroup.mem_map]
    constructor
    · rintro ⟨⟨b, c'⟩, hbc, rfl⟩
      have := ((hB.del τ).1 b).1 ⟨c', hbc⟩
      rw [PositivityTheory.Xgn.ImageLatticeBaseChange.mem_stdLat] at this
      exact this
    · intro hv
      obtain ⟨c', hc'⟩ := ((hB.del τ).1 v).2 ((PositivityTheory.Xgn.ImageLatticeBaseChange.mem_stdLat R _).2 hv)
      exact ⟨(v, c'), hc', rfl⟩
  have hLF := PositivityTheory.Xgn.ImageLatticeBaseChange.locFree_div R hw0 _ hfst
  have hHle : D.hh R p (χ τ) ≤ AddSubgroup.map (AddMonoidHom.fst _ _) (D.Del τ) := by
    intro v hv
    rw [hfst]
    intro i
    have hv' := (PositivityTheory.Xgn.ImageLatticeBaseChange.mem_dotDual R _ v).1 hv
    have hmem : w • (Pi.single i 1 : Fin n → Ω) ∈ D.af R p (χ τ) :=
      hw τ ⟨Pi.single i 1, (PositivityTheory.Xgn.ImageLatticeBaseChange.mem_stdLat R _).2 (fun j => by
        by_cases h : j = i <;> simp [h, Pi.single_apply, R.one_mem, R.zero_mem]), rfl⟩
    have := hv' _ hmem
    simpa [smul_dotProduct, single_dotProduct] using this
  have hHst : ∀ a ∈ R, ∀ v ∈ D.hh R p (χ τ), a • v ∈ D.hh R p (χ τ) := by
    intro a ha v hv
    unfold LieLatticeData.hh at hv ⊢
    rw [PositivityTheory.Xgn.ImageLatticeBaseChange.mem_dotDual] at hv ⊢
    intro u hu
    rw [dotProduct_smul, smul_eq_mul]
    exact R.mul_mem ha (hv u hu)
  have hg := (PositivityTheory.Xgn.t_graph_restrict_bc R RC hR (bcMap Ω C (Fin n)) (bcMap Ω C (Fin (s τ)))
    (PositivityTheory.Xgn.ImageLatticeBaseChange.isBaseChange_bcMap C n) (PositivityTheory.Xgn.ImageLatticeBaseChange.isBaseChange_bcMap C (s τ))
    (D.Del τ) (D.hh R p (χ τ)) n hstab hLF hHle hHst).1
  unfold LieLatticeData.imH
  rw [hhh]
  change AddSubgroup.map _ (spanOver RC (Prod.map (bcMap Ω C (Fin n)) (bcMap Ω C (Fin (s τ))) '' ↑(D.Del τ)) ⊓ _) = _
  rw [hg]
  exact map_snd_spanOver_prodMap_eq RC _ _ _
end

