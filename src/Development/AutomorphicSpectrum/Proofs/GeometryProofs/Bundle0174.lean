import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0007
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0023
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeDominantCompat
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0055
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0088
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PlaceEqOneOfNotMem
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0096
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StandardRankOneLatticeOfLocal
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0170
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0003
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.ThetaMove
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackSmooth
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LiePull

section Lat

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] [IsCommMonObj G] {Ω : Type} [Field Ω]
  {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]

theorem lat_eq_span (M : LieModel G ξ E) (p : Cpt ξ)
    (hx : Spec.map (CommRingCat.ofHom (genMap ξ p)) ≫ X.fromSpecStalk p.1 = ξ) {r : ℕ}
    (b : Fin r → ExtE hx M) (hsp : Submodule.span (X.presheaf.stalk p.1) (Set.range b) = ⊤) :
    M.lat p = Submodule.span (regAt ξ p) (Set.range fun k => val (b k)) := by
  have car := (lieLat_carrier X G Ω ξ E M p).1
  apply le_antisymm
  · intro e he
    obtain ⟨v, hv⟩ := (car e).1 he
    let y : ExtE hx M := ⟨e, v, hv⟩
    have hy : y ∈ Submodule.span (X.presheaf.stalk p.1) (Set.range b) := by
      rw [hsp]; trivial
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hy
    have he' : e = ∑ k, genMap ξ p (c k) • val (b k) := by
      have h1 : val y = e := rfl
      rw [← h1, ← hc, map_sum]
      rfl
    rw [he']
    refine Submodule.sum_mem _ fun k _ => ?_
    exact Submodule.smul_mem _ (⟨genMap ξ p (c k), c k, rfl⟩ : regAt ξ p) (Submodule.subset_span ⟨k, rfl⟩)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    exact (car _).2 (val_spec (b k))

theorem ext_basis {A : Type} [CommRing A] [IsLocalRing A] {g : A →+* Ω} {x : Spec (CommRingCat.of A) ⟶ X}
    (hs : Smooth G.hom) (hg : Function.Injective g) (hx : Spec.map (CommRingCat.ofHom g) ≫ x = ξ)
    (M : LieModel G ξ E) : ∃ n : ℕ, Nonempty (Module.Basis (Fin n) A (ExtE hx M)) :=
  GlobalTheory.T.lie_model_free_over_local_ring X G hs A x (ExtE hx M) (extModel hg hx M)

end Lat

theorem frame : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω') ⟶ X'), IsCptGen ξ → IsCptGen ξ' → ∀ (f : X' ⟶ X) (i : Ω →+* Ω') (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i) (G : Over X) [GrpObj G] [IsCommMonObj G] (G' : Over X') [GrpObj G'] [IsCommMonObj G'] (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → Smooth G.hom → ∀ (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (E' : Type) [AddCommGroup E'] [Module Ω' E'] (M' : LieModel G' ξ' E') (j : E →+ E'), (∀ v, (M'.pt (j v)).left ≫ φ = spMap (dualMap i) ≫ (M.pt v).left) → ∀ q' : Cpt ξ', ∃ (r : ℕ) (B : Module.Basis (Fin r) Ω E) (B' : Module.Basis (Fin r) Ω' E') (v : Fin r → (epsAt (X.fromSpecStalk (f q'.1)) ⟶ G)) (v' : Fin r → (epsAt (X'.fromSpecStalk q'.1) ⟶ G')), (∀ k, B' k = j (B k)) ∧ M.lat ⟨f q'.1, hd.specializes q'⟩ = Submodule.span (regAt ξ ⟨f q'.1, hd.specializes q'⟩) (Set.range B) ∧ M'.lat q' = Submodule.span (regAt ξ' q') (Set.range B') ∧ (∀ k, M.Extends ⟨f q'.1, hd.specializes q'⟩ (B k) (v k)) ∧ (∀ k, M'.Extends q' (B' k) (v' k)) ∧ ∀ k, (v' k).left ≫ φ = spMap (dualMap (f.stalkMap q'.1).hom) ≫ (v k).left := by
  intro X X' Ω Ω' _ _ ξ ξ' hξ hξ' f i hd G _ _ G' _ _ φ hG hs E _ _ M E' _ _ M' j hj q'
  have hp : genPt ξ ⤳ f q'.1 := hd.specializes q'
  have hx := LieCarrier.genMap_fromSpecStalk (ξ := ξ) ⟨f q'.1, hp⟩
  have hx' := LieCarrier.genMap_fromSpecStalk (ξ := ξ') q'
  have hρ : Spec.map (CommRingCat.ofHom (f.stalkMap q'.1).hom) ≫ X.fromSpecStalk (f q'.1) =
      X'.fromSpecStalk q'.1 ≫ f := Scheme.SpecMap_stalkMap_fromSpecStalk f
  have hρ' : (genMap ξ' q').comp (f.stalkMap q'.1).hom = i.comp (genMap ξ ⟨f q'.1, hp⟩) :=
    RingHom.ext (RegAtDom.genMap_stalkMap hd q'.1 q'.2 hp)
  have hg := hξ.inj ⟨f q'.1, hp⟩
  have hg' := hξ'.inj q'
  obtain ⟨r, ⟨b⟩⟩ := ext_basis (A := X.presheaf.stalk (f q'.1)) hs hg hx M
  obtain ⟨hli, hsp⟩ := bc hs (genMap ξ ⟨f q'.1, hp⟩) (X.fromSpecStalk (f q'.1)) ξ hx (extModel hg hx M) M b
    (fun k => val (b k)) (fun k => (vec_spec (b k)).2)
  let B : Module.Basis (Fin r) Ω E := Module.Basis.mk hli hsp.ge
  have hB : ∀ k, B k = val (b k) := fun k => by simp [B]
  obtain ⟨hli', hsp'⟩ := bc hs i ξ (ξ' ≫ f) hd.symm M (LieMove.pushModel hG M') B (fun k => j (B k)) (fun k => hj _)
  let B' : Module.Basis (Fin r) Ω' E' := Module.Basis.mk hli' hsp'.ge
  have hB' : ∀ k, B' k = j (B k) := fun k => by simp [B']
  have up : ∀ k, ∃ u : epsAt (X'.fromSpecStalk q'.1) ⟶ G',
      Ext (genMap ξ' q') (X'.fromSpecStalk q'.1) M' (j (val (b k))) u ∧
      u.left ≫ φ = spMap (dualMap (f.stalkMap q'.1).hom) ≫ (vec (b k)).left :=
    fun k => ext_up hG hj hρ hρ' hx' (vec_spec (b k))
  choose u hu huφ using up
  let b' : Fin r → ExtE hx' M' := fun k => ⟨j (val (b k)), u k, hu k⟩
  obtain ⟨-, hsp''⟩ := bc hs (f.stalkMap q'.1).hom (X.fromSpecStalk (f q'.1)) (X'.fromSpecStalk q'.1 ≫ f) hρ
    (extModel hg hx M) (LieMove.pushModel hG (extModel hg' hx' M')) b b'
    (fun k => by
      have e₁ : vec (b' k) = u k := (vec_spec (b' k)).unique hg' (hu k)
      show (vec (b' k)).left ≫ φ = _
      rw [e₁]
      exact huφ k)
  refine ⟨r, B, B', fun k => vec (b k), u, hB', ?_, ?_, ?_, ?_, huφ⟩
  · rw [lat_eq_span M _ hx b b.span_eq]
    congr 2
    exact funext fun k => (hB k).symm
  · rw [lat_eq_span M' q' hx' b' hsp'']
    congr 2
    exact funext fun k => by rw [hB', hB]; rfl
  · intro k
    rw [hB]
    exact vec_spec (b k)
  · intro k
    rw [hB', hB]
    exact hu k

end GlobalTheory.CompanionTheory.Ar.LiePull
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalIndexFrameLogDet
section
open NumberField Matrix IsDedekindDomain GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame

namespace GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame

variable {L : Type} [Field L] [NumberField L] {n : ℕ}

theorem place_eq_zpow_ordE (v : FinitePlace L) {x : L} (hx : x ≠ 0) :
    v x = ((Ideal.absNorm v.maximalIdeal.asIdeal : ℕ) : ℝ) ^ (-Formalism.L2.Ker.ordE v.maximalIdeal x) := by
  have hw : IsDedekindDomain.HeightOneSpectrum.valuation L v.maximalIdeal x ≠ 0 := by
    rwa [ne_eq, Valuation.zero_iff]
  rw [← NumberField.FinitePlace.norm_embedding_eq, NumberField.FinitePlace.norm_embedding,
    NumberField.HeightOneSpectrum.adicAbv_def]
  unfold Formalism.L2.Ker.ordE
  rw [neg_neg]
  obtain ⟨k, hk⟩ : ∃ k : ℤ, IsDedekindDomain.HeightOneSpectrum.valuation L v.maximalIdeal x = WithZero.exp k :=
    ⟨_, (WithZero.exp_log hw).symm⟩
  rw [hk, WithZero.log_exp, WithZeroMulInt.toNNReal_neg_apply _ (WithZero.exp_ne_zero)]
  simp [WithZero.exp]

theorem relIndex_map_of_integral (v : FinitePlace L) (S : Matrix (Fin n) (Fin n) L)
    (hS : ∀ i j, v (S i j) ≤ 1) (hdet : S.det ≠ 0) (f : (Fin n → L) →+ (Fin n → L))
    (hf : ∀ x, f x = S *ᵥ x) (Λ : AddSubgroup (Fin n → L)) (hΛ : ∀ x, x ∈ Λ ↔ ∀ i, v (x i) ≤ 1) :
    Λ.map f ≤ Λ ∧ (((Λ.map f).relIndex Λ : ℕ) : ℝ) = (v S.det)⁻¹ := by
  have hint : ∀ a : L, v a ≤ 1 ↔ Formalism.L2.Col.IntAt v.maximalIdeal a := fun a => by
    rw [place_le_one_iff, GlobalTheory.CharValCompare.intAt_iff]
  have hle : Λ.map f ≤ Λ := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := AddSubgroup.mem_map.mp hz
    rw [hΛ] at hy ⊢
    intro i
    rw [hf]
    show v (∑ j, S i j * y j) ≤ 1
    exact place_sum_le_one v _ _ (fun j _ => place_mul_le_one v (hS i j) (hy j))
  refine ⟨hle, ?_⟩
  have key := GlobalTheory.IdxDet.relIndex_mulVec L (Fin n) v.maximalIdeal S Λ (Λ.map f) hdet
    (fun x => by rw [hΛ]; exact forall_congr' fun i => hint (x i))
    (fun x => by
      rw [AddSubgroup.mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy, hf y⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy, hf y⟩)
    hle
  rw [place_eq_zpow_ordE v hdet, _root_.zpow_neg, inv_inv]
  have key' := congrArg (fun q : ℚ => (q : ℝ)) key
  push_cast at key'
  exact key'

theorem gIdx_locAt_frame (L : Type) [Field L] [NumberField L] (n : ℕ) (v : FinitePlace L)
    (T : Matrix (Fin n) (Fin n) L) (hdet : T.det ≠ 0) :
    gIdx (locAt v (frame T)).toAddSubgroup
      (locAt v (frame (1 : Matrix (Fin n) (Fin n) L))).toAddSubgroup = Real.log (v T.det) := by
  set Λ := (locAt v (frame (1 : Matrix (Fin n) (Fin n) L))).toAddSubgroup with hΛdef
  have hΛ : ∀ x, x ∈ Λ ↔ ∀ i, v (x i) ≤ 1 := fun x => mem_locAt_frame_one
  obtain ⟨M, hM⟩ : ∃ M : (Fin n → L) →+ (Fin n → L), ∀ x, M x = T *ᵥ x :=
    ⟨(Matrix.mulVecLin T).toAddMonoidHom, fun x => rfl⟩
  have hTΛ : (locAt v (frame T)).toAddSubgroup = Λ.map M := by
    ext x
    rw [Submodule.mem_toAddSubgroup, mem_locAt_frame, AddSubgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, (hΛ y).2 hy, hM y⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, (hΛ y).1 hy, hM y⟩
  have hMinj : Function.Injective M := by
    intro x y hxy
    rw [hM, hM] at hxy
    have h := congrArg (fun z => T⁻¹ *ᵥ z) hxy
    simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul T (isUnit_iff_ne_zero.mpr hdet)] using h
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (NumberField.RingOfIntegers L))
    (Finset.univ : Finset (Fin n × Fin n)) (fun p => T p.1 p.2)
  set c : L := algebraMap (NumberField.RingOfIntegers L) L b with hcdef
  have hc0 : c ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  have hcv : v c ≤ 1 := place_int_le_one v b
  have hcT : ∀ i j, v ((c • T) i j) ≤ 1 := by
    intro i j
    obtain ⟨r, hr⟩ := hb (i, j) (Finset.mem_univ _)
    rw [Matrix.smul_apply]
    have : c • T i j = algebraMap (NumberField.RingOfIntegers L) L r := by
      rw [hr, smul_eq_mul, Algebra.smul_def]
      all_goals rfl
    rw [this]
    exact place_int_le_one v r
  have hcI : ∀ i j, v ((c • (1 : Matrix (Fin n) (Fin n) L)) i j) ≤ 1 := by
    intro i j
    rw [Matrix.smul_apply, Matrix.one_apply]
    split_ifs
    · simpa using hcv
    · simpa using place_int_le_one v 0
  obtain ⟨a, ha⟩ : ∃ a : (Fin n → L) →+ (Fin n → L), ∀ x, a x = c • x :=
    ⟨DistribSMul.toAddMonoidHom _ c, fun x => rfl⟩
  have hdetI : (c • (1 : Matrix (Fin n) (Fin n) L)).det = c ^ n := by
    rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one]
  have hdetT : (c • T).det = c ^ n * T.det := by
    rw [Matrix.det_smul, Fintype.card_fin]
  have hcn : c ^ n ≠ 0 := pow_ne_zero _ hc0
  have h1 := relIndex_map_of_integral v (c • (1 : Matrix (Fin n) (Fin n) L)) hcI
    (by rw [hdetI]; exact hcn) a (fun x => by rw [ha]; ext i; simp [Matrix.mulVec, dotProduct, Matrix.one_apply]) Λ hΛ
  have h2 := relIndex_map_of_integral v (c • T) hcT (by rw [hdetT]; exact mul_ne_zero hcn hdet) (a.comp M)
    (fun x => by
      rw [AddMonoidHom.comp_apply, ha, hM]
      ext i
      simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]) Λ hΛ
  have hpos : ∀ y : L, y ≠ 0 → 0 < v y := fun y hy => NumberField.FinitePlace.pos_iff.mpr hy
  have hr1 : (Λ.map a).relIndex Λ ≠ 0 := by
    intro h0
    have := h1.2
    rw [h0, Nat.cast_zero, hdetI] at this
    exact (inv_pos.mpr (hpos _ hcn)).ne' this.symm
  have hr2 : (Λ.map (a.comp M)).relIndex Λ ≠ 0 := by
    intro h0
    have := h2.2
    rw [h0, Nat.cast_zero, hdetT] at this
    exact (inv_pos.mpr (hpos _ (mul_ne_zero hcn hdet))).ne' this.symm
  rw [hTΛ, gIdx_frac Λ M a hMinj (fun x => by rw [ha, hM, hM, ha, Matrix.mulVec_smul]) h1.1 hr1 h2.1 hr2,
    h1.2, h2.2, hdetI, hdetT, Real.log_inv, Real.log_inv]
  have hm : v (c ^ n * T.det) = v (c ^ n) * v T.det := by
    rw [NumberField.FinitePlace.coe_apply, NumberField.FinitePlace.coe_apply,
      NumberField.FinitePlace.coe_apply, map_mul]
  rw [hm, Real.log_mul (hpos _ hcn).ne' (hpos _ hdet).ne']
  ring

end GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentVectorExtendsDvrStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_vector_extends_dvr : ∀ (O K : Type) [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K] [IsFractionRing O K] (S : Scheme.{0}) (x : Sp O ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (E : Type) [AddCommGroup E] [Module O E] (M : LieModel G x E) (v : epsAt (spMap (algebraMap O K) ≫ x) ⟶ G), IsTanAt G _ v → (∀ (P : Ideal O) [P.IsMaximal] (c : Localization.AtPrime P →+* K), c.comp (algebraMap O _) = algebraMap O K → ∃ w : epsAt (spMap (algebraMap O (Localization.AtPrime P)) ≫ x) ⟶ G, IsTanAt G _ w ∧ v.left = spMap (dualMap c) ≫ w.left) → ∃ e, M.Lifts (algebraMap O K) (𝟙 G.left) e v := by
  first | exact @GlobalTheory.CompanionTheory.Ar.lieModel_lifts_of_local | exact GlobalTheory.CompanionTheory.Ar.lieModel_lifts_of_local | (intros; apply GlobalTheory.CompanionTheory.Ar.lieModel_lifts_of_local <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.WeilPairingBaseChangeUnitStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_pairing_base_change_unit : ∀ {X : Scheme.{0}} (G : Over X) [GrpObj G] [IsCommMonObj G] (L : LB G.left), L.IsLB → ∀ (k M : Type) [Field k] [Field M] (j : k →+* M) (q : Sp k ⟶ X) (q' : Sp M ⟶ X), q' = spMap j ≫ q → ∀ (n : ℤ) (x y : Over.mk q ⟶ G) (x' y' : Over.mk q' ⟶ G), x'.left = spMap j ≫ x.left → y'.left = spMap j ≫ y.left → ∀ (c : kˣ) (c' : Mˣ), Out.WeilIs G L n x y (unitOn c) → Out.WeilIs G L n x' y' (unitOn c') → c' = Units.map j.toMonoidHom c := by
  first | exact @GlobalTheory.CompanionTheory.Ar.weilIs_fieldExt | exact GlobalTheory.CompanionTheory.Ar.weilIs_fieldExt | (intros; apply GlobalTheory.CompanionTheory.Ar.weilIs_fieldExt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.WeilPairingPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HtTorPull

theorem spMap_comp_fields {A B C : Type} [Field A] [Field B] [Field C] (i : A →+* B) (τ : B →+* C) :
    spMap (τ.comp i) = spMap τ ≫ spMap i := by
  simp only [spMap]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem cancel_spMap {K K' : Type} [Field K] [Field K'] (τ : K →+* K') {Z : Scheme.{0}}
    (a b : Spec (CommRingCat.of K) ⟶ Z) (h : spMap τ ≫ a = spMap τ ≫ b) : a = b := by
  have hd : IsSchemeTheoreticallyDominant (spMap τ) :=
    LieEx.std_of_inj (CommRingCat.ofHom τ) τ.injective
  have hs : Function.Surjective (spMap τ) := by
    intro p
    obtain ⟨x⟩ : Nonempty (Spec (CommRingCat.of K')) := inferInstance
    exact ⟨x, Subsingleton.elim (α := PrimeSpectrum K) _ _⟩
  exact LieEx.epi_of_surj (spMap τ) hs a b h

theorem secVal_eq_of_eq {B : Type} [CommRing B] {Z : Scheme.{0}} {x x' : Spec (CommRingCat.of B) ⟶ Z} (e : x = x')
    (W : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ W) (h' : ⊤ ≤ x' ⁻¹ᵁ W) (s : Γ(Z, W)) : secVal x W h s = secVal x' W h' s := by
  subst e
  rfl

theorem torsion_clause : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω'), GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → ∀ (G : Over X) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (n : ℕ) (e : (Over.mk ξ ⟶ G) → (Over.mk ξ ⟶ G) → Ωˣ), GenWeil G L ξ n e → FullTorsion G ξ n → ∀ (G' : Over X') [GrpObj G'] [IsCommMonObj G'] (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → FullTorsion G' ξ' n → ∀ (L' : LB G'.left) (e' : (Over.mk ξ' ⟶ G') → (Over.mk ξ' ⟶ G') → Ω'ˣ), GenWeil G' L' ξ' n e' → ∀ (y : Over.mk ξ ⟶ G) (y' : Over.mk ξ' ⟶ G'), y ^ n = 1 → y' ^ n = 1 → (∀ (g : Over.mk ξ ⟶ G) (g' : Over.mk ξ' ⟶ G'), g ^ n = 1 → g' ^ n = 1 → g'.left ≫ φ = spMap i ≫ g.left → (e' y' g' : Ω') = i (e y g)) → (∀ (g : Over.mk ξ ⟶ G), g ^ n = 1 → ∃ g' : Over.mk ξ' ⟶ G', g' ^ n = 1 ∧ g'.left ≫ φ = spMap i ≫ g.left) → (∀ (g' : Over.mk ξ' ⟶ G'), g' ^ n = 1 → ∃ g : Over.mk ξ ⟶ G, g ^ n = 1 ∧ g'.left ≫ φ = spMap i ≫ g.left) → ∀ (W : G.left.Opens) (s : Γ(G.left, W)),
  (∀ (k : Type) [Field k] [IsAlgClosed k] (τ : Ω →+* k) (xk g : Over.mk (spMap τ ≫ ξ) ⟶ G) (c : kˣ) (h : ⊤ ≤ g.left ⁻¹ᵁ W), xk.left = spMap τ ≫ y.left → g ^ n = 1 → Out.WeilIs G L n xk g (unitOn c) → secVal (B := k) g.left W h s = c) →
  (∀ (k : Type) [Field k] [IsAlgClosed k] (τ : Ω' →+* k) (xk g : Over.mk (spMap τ ≫ ξ') ⟶ G') (c : kˣ) (h : ⊤ ≤ g.left ⁻¹ᵁ (φ ⁻¹ᵁ W)), xk.left = spMap τ ≫ y'.left → g ^ n = 1 → Out.WeilIs G' L' n xk g (unitOn c) → secVal (B := k) g.left (φ ⁻¹ᵁ W) h (φ.app W s) = c) := by
  intro X X' Ω Ω' _ _ ξ ξ' f i hD G _ _ L n e hGW hFT G' _ _ φ hP hFT' L' e' hGW' y y' hy hy' hcomp hlift hdown W s hW
    k _ _ τ xk g c h hxk hgn hWeil
  obtain ⟨x', hx⟩ := hFT' k τ g hgn
  let U : Over.mk (spMap τ ≫ ξ') ⟶ Over.mk ξ' := Over.homMk (spMap τ) rfl
  have hgU : g = U ≫ x' := Over.OverMorphism.ext hx
  have hx'n : x' ^ n = 1 := by
    have e1 : preHom (G := G') U (x' ^ n) = preHom (G := G') U 1 := by
      rw [map_pow, map_one]
      show (U ≫ x') ^ n = 1
      rw [← hgU]
      exact hgn
    apply Over.OverMorphism.ext
    apply cancel_spMap τ
    exact congrArg (fun z => z.left) e1
  obtain ⟨g₀, hg₀, hxg⟩ := hdown x' hx'n
  have hc' : (c : k) = τ (e' y' x') := (hGW'.weil y' x' hy' hx'n k τ xk g c hxk hx).1 hWeil
  have hc : (c : k) = (τ.comp i) (e y g₀) := by
    rw [hc', hcomp g₀ x' hg₀ hx'n hxg]
    rfl
  let U₀ : Over.mk (spMap (τ.comp i) ≫ ξ) ⟶ Over.mk ξ := Over.homMk (spMap (τ.comp i)) rfl
  have hW1 : Out.WeilIs G L n (U₀ ≫ y) (U₀ ≫ g₀) (unitOn c) :=
    (hGW.weil y g₀ hy hg₀ k (τ.comp i) (U₀ ≫ y) (U₀ ≫ g₀) c rfl rfl).2 hc
  have hg₁ : (U₀ ≫ g₀) ^ n = 1 := by
    have e1 : preHom (G := G) U₀ (g₀ ^ n) = (U₀ ≫ g₀) ^ n := map_pow _ _ _
    rw [← e1, hg₀, map_one]
  have hl : g.left ≫ φ = (U₀ ≫ g₀).left := by
    show g.left ≫ φ = spMap (τ.comp i) ≫ g₀.left
    rw [hx, Category.assoc, hxg, spMap_comp_fields, Category.assoc]
  have h' : ⊤ ≤ (g.left ≫ φ) ⁻¹ᵁ W := h
  have h₁ : ⊤ ≤ (U₀ ≫ g₀).left ⁻¹ᵁ W := hl ▸ h'
  rw [HtPull.seccomp k _ _ g.left φ W h h' s, secVal_eq_of_eq hl W h' h₁ s]
  exact hW k (τ.comp i) (U₀ ≫ y) (U₀ ≫ g₀) c h₁ rfl hg₁ hW1

end GlobalTheory.CompanionTheory.Ar.HtTorPull
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.WeilPairingTransportRelation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.TorsionChars

theorem exists_units_map_eq {Ω Ω' : Type} [Field Ω] [Field Ω'] (i : Ω →+* Ω') (n : ℕ) [NeZero n]
    (v : Ω'ˣ) (hv : v ^ Nat.card (rootsOfUnity n Ω) = 1) :
    ∃ u : Ωˣ, Units.map (i : Ω →* Ω') u = v := by
  classical
  set m := Nat.card (rootsOfUnity n Ω) with hm
  haveI : NeZero m := ⟨Nat.card_pos.ne'⟩
  have hinj : Function.Injective (Units.map (i : Ω →* Ω')) :=
    Units.map_injective i.injective
  let f : rootsOfUnity n Ω → rootsOfUnity m Ω' := fun u =>
    ⟨Units.map (i : Ω →* Ω') u.1, by
      have h1 : (u : Ωˣ) ^ m = 1 := by
        have := congrArg Subtype.val (pow_card_eq_one' (x := u))
        rw [Subgroup.coe_pow, Subgroup.coe_one] at this
        exact this
      rw [mem_rootsOfUnity, ← map_pow, h1, map_one]⟩
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (hinj (congrArg Subtype.val hab))
  have hbij := hf.bijective_of_nat_card_le (card_rootsOfUnity Ω' m)
  obtain ⟨u, hu⟩ := hbij.2 ⟨v, by rw [mem_rootsOfUnity]; exact hv⟩
  exact ⟨u.1, congrArg Subtype.val hu⟩

theorem pow_right_of_mul {G M : Type} [CommGroup G] [CommGroup M] (n : ℕ) (χ : G → M)
    (hχ : ∀ g g', g ^ n = 1 → g' ^ n = 1 → χ (g * g') = χ g * χ g')
    (g : G) (hg : g ^ n = 1) (k : ℕ) : χ (g ^ k) = χ g ^ k := by
  have h1 : χ 1 = 1 := by
    have := hχ 1 1 (one_pow n) (one_pow n)
    simpa using this
  induction k with
  | zero => simpa using h1
  | succ k ih =>
    have hk : (g ^ k) ^ n = 1 := by rw [← pow_mul, mul_comm, pow_mul, hg, one_pow]
    rw [pow_succ, hχ _ _ hk hg, ih, pow_succ]

theorem chars_descend : ∀ (Ω Ω' : Type) [Field Ω] [Field Ω'] (i : Ω →+* Ω') (C A : Type) [CommGroup C] [CommGroup A] (rel : A → C → Prop) (n : ℕ), 1 ≤ n →
  (∀ c : C, c ^ n = 1 → ∃ a : A, a ^ n = 1 ∧ rel a c) →
  (∀ a : A, a ^ n = 1 → ∃ c : C, c ^ n = 1 ∧ rel a c) →
  (∀ a a' c c', rel a c → rel a' c' → rel (a * a') (c * c')) →
  (∀ a a' c, rel a c → rel a' c → a = a') →
  (∀ a c c', rel a c → rel a c' → c = c') →
  ∀ (e : C → C → Ωˣ) (e' : A → A → Ω'ˣ),
  (∀ x g g', x ^ n = 1 → g ^ n = 1 → g' ^ n = 1 → e x (g * g') = e x g * e x g') →
  (∀ χ : C → Ωˣ, (∀ g g', g ^ n = 1 → g' ^ n = 1 → χ (g * g') = χ g * χ g') → ∃ x, x ^ n = 1 ∧ ∀ g, g ^ n = 1 → χ g = e x g) →
  (∀ g, g ^ n = 1 → (∀ x, x ^ n = 1 → e x g = 1) → g = 1) →
  (∀ x g g', x ^ n = 1 → g ^ n = 1 → g' ^ n = 1 → e' x (g * g') = e' x g * e' x g') →
  (∀ χ : A → Ω'ˣ, (∀ g g', g ^ n = 1 → g' ^ n = 1 → χ (g * g') = χ g * χ g') → ∃ x, x ^ n = 1 ∧ ∀ g, g ^ n = 1 → χ g = e' x g) →
  (∀ y' : A, y' ^ n = 1 → ∃ y : C, y ^ n = 1 ∧ ∀ g g', g ^ n = 1 → g' ^ n = 1 → rel g' g → (e' y' g' : Ω') = i (e y g)) ∧
  (∀ y : C, y ^ n = 1 → ∃ y' : A, y' ^ n = 1 ∧ ∀ g g', g ^ n = 1 → g' ^ n = 1 → rel g' g → (e' y' g' : Ω') = i (e y g)) := by
  classical
  intro Ω Ω' _ _ i C A _ _ rel n hn hCA hAC hmul hinjA hinjC e e' emul eperf enondeg e'mul e'perf
  haveI : NeZero n := ⟨by omega⟩
  have hinj : Function.Injective (Units.map (i : Ω →* Ω')) :=
    Units.map_injective i.injective
  have hrel11 : rel 1 1 := by
    obtain ⟨a₀, -, h₀⟩ := hCA 1 (one_pow n)
    have h := hmul _ _ _ _ h₀ h₀
    rw [_root_.mul_one] at h
    have : a₀ * a₀ = a₀ := hinjA _ _ _ h h₀
    have h1 : a₀ = 1 := by simpa using this
    rwa [h1] at h₀
  have hrelpow : ∀ a c, rel a c → ∀ k : ℕ, rel (a ^ k) (c ^ k) := by
    intro a c h k
    induction k with
    | zero => simpa using hrel11
    | succ k ih => rw [pow_succ, pow_succ]; exact hmul _ _ _ _ ih h
  refine ⟨?_, ?_⟩
  · intro y' hy'
    set m := Nat.card (rootsOfUnity n Ω) with hm
    have hCm : ∀ g : C, g ^ n = 1 → g ^ m = 1 := by
      intro g hg
      refine enondeg _ (by rw [← pow_mul, mul_comm, pow_mul, hg, one_pow]) ?_
      intro x hx
      rw [pow_right_of_mul n (e x) (fun g g' => emul x g g' hx) g hg m]
      have hmem : e x g ∈ rootsOfUnity n Ω := by
        rw [mem_rootsOfUnity, ← pow_right_of_mul n (e x) (fun g g' => emul x g g' hx) g hg n, hg]
        have := emul x 1 1 hx (one_pow n) (one_pow n)
        simpa using this
      have := congrArg Subtype.val (pow_card_eq_one' (x := (⟨e x g, hmem⟩ : rootsOfUnity n Ω)))
      rw [Subgroup.coe_pow, Subgroup.coe_one] at this
      exact this
    have hAm : ∀ a : A, a ^ n = 1 → a ^ m = 1 := by
      intro a ha
      obtain ⟨c, hc, hac⟩ := hAC a ha
      have h := hrelpow a c hac m
      rw [hCm c hc] at h
      exact hinjA _ _ _ h hrel11
    have hval : ∀ a : A, a ^ n = 1 → ∃ u : Ωˣ, Units.map (i : Ω →* Ω') u = e' y' a := by
      intro a ha
      apply exists_units_map_eq i n
      rw [← pow_right_of_mul n (e' y') (fun g g' => e'mul y' g g' hy') a ha m, hAm a ha]
      have := e'mul y' 1 1 hy' (one_pow n) (one_pow n)
      simpa using this
    have hpart : ∀ c : C, c ^ n = 1 → ∃ u : Ωˣ, ∃ a : A, a ^ n = 1 ∧ rel a c ∧
        Units.map (i : Ω →* Ω') u = e' y' a := by
      intro c hc
      obtain ⟨a, ha, hac⟩ := hCA c hc
      obtain ⟨u, hu⟩ := hval a ha
      exact ⟨u, a, ha, hac, hu⟩
    let χ : C → Ωˣ := fun c => if h : c ^ n = 1 then (hpart c h).choose else 1
    have hχ : ∀ c : C, c ^ n = 1 → ∀ a : A, a ^ n = 1 → rel a c →
        Units.map (i : Ω →* Ω') (χ c) = e' y' a := by
      intro c hc a ha hac
      obtain ⟨a₁, -, hrel, hu⟩ := (hpart c hc).choose_spec
      have : χ c = (hpart c hc).choose := dif_pos hc
      rw [this, hu, hinjA _ _ _ hrel hac]
    obtain ⟨y, hy, hye⟩ := eperf χ (by
      intro g g' hg hg'
      obtain ⟨a, ha, hag⟩ := hCA g hg
      obtain ⟨a', ha', hag'⟩ := hCA g' hg'
      have hgg : (g * g') ^ n = 1 := by rw [mul_pow, hg, hg', _root_.one_mul]
      have haa : (a * a') ^ n = 1 := by rw [mul_pow, ha, ha', _root_.one_mul]
      apply hinj
      rw [map_mul, hχ _ hgg _ haa (hmul _ _ _ _ hag hag'), hχ _ hg _ ha hag, hχ _ hg' _ ha' hag',
        e'mul y' _ _ hy' ha ha'])
    refine ⟨y, hy, ?_⟩
    intro g g' hg hg' hrel
    rw [← hχ g hg g' hg' hrel, hye g hg]
    rfl
  · intro y hy
    have hpart : ∀ a : A, a ^ n = 1 → ∃ c : C, c ^ n = 1 ∧ rel a c := hAC
    let χ : A → Ω'ˣ := fun a =>
      if h : a ^ n = 1 then Units.map (i : Ω →* Ω') (e y (hpart a h).choose) else 1
    have hχ : ∀ a : A, a ^ n = 1 → ∀ c : C, rel a c →
        χ a = Units.map (i : Ω →* Ω') (e y c) := by
      intro a ha c hac
      have : χ a = Units.map (i : Ω →* Ω') (e y (hpart a ha).choose) := dif_pos ha
      rw [this, hinjC _ _ _ (hpart a ha).choose_spec.2 hac]
    obtain ⟨y', hy', hye⟩ := e'perf χ (by
      intro g g' hg hg'
      obtain ⟨c, hc, hgc⟩ := hAC g hg
      obtain ⟨c', hc', hgc'⟩ := hAC g' hg'
      have hgg : (g * g') ^ n = 1 := by rw [mul_pow, hg, hg', _root_.one_mul]
      rw [hχ _ hgg _ (hmul _ _ _ _ hgc hgc'), hχ _ hg _ hgc, hχ _ hg' _ hgc',
        emul y _ _ hy hc hc', map_mul])
    refine ⟨y', hy', ?_⟩
    intro g g' hg hg' hrel
    rw [← hye g' hg', hχ g' hg' g hrel]
    rfl

end GlobalTheory.CompanionTheory.Ar.TorsionChars
end

