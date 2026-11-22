import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.MorphismsDescendToLargeSubfield
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem morphisms_descend_to_large_subfield :
    ∀ (K : Type) [Field K] (K₀ : Subfield K) (X₀ X : Scheme.{0}) (p₀ : X₀ ⟶ Sp K₀) (p : X ⟶ Sp K) (φ : X ⟶ X₀) (Z : Scheme.{0}) (q : Z ⟶ Sp K₀) [QuasiCompact p₀] [QuasiSeparated p₀] [LocallyOfFinitePresentation q] (I : Type) [Finite I] (f : I → (X ⟶ Z)), IsPullback φ p p₀ (spMap K₀.subtype) → (∀ j, f j ≫ q = φ ≫ p₀) → ∃ s : Finset K, ∀ (K₁ : Subfield K) (h : K₀ ≤ K₁), (s : Set K) ⊆ K₁ → ∀ (X₁ : Scheme.{0}) (p₁ : X₁ ⟶ Sp K₁) (φ₁ : X₁ ⟶ X₀) (ψ : X ⟶ X₁), IsPullback φ₁ p₁ p₀ (spMap (Subfield.inclusion h)) → ψ ≫ φ₁ = φ → ψ ≫ p₁ = p ≫ spMap K₁.subtype → ∃ f₁ : I → (X₁ ⟶ Z), ∀ j, ψ ≫ f₁ j = f j ∧ f₁ j ≫ q = φ₁ ≫ p₀ := by
  intro K _ K₀ X₀ X p₀ p φ Z q _ _ _ I _ f hX hf
  have hX' : IsPullback φ p p₀ (spMap (algebraMap K₀ K)) := hX
  obtain ⟨R, g, ⟨s, rfl⟩, -, hg⟩ := Spread.exists_fg_forall_comp_eq (A := K) p₀ q
    (fun j ↦ hX'.isoPullback.inv ≫ f j)
    (fun j ↦ by rw [Category.assoc, hf, IsPullback.isoPullback_inv_fst_assoc]) ⊥ Subalgebra.fg_bot
  refine ⟨s, fun K₁ h hs X₁ p₁ φ₁ ψ h₁ hψ₁ hψ₂ ↦ ?_⟩
  have hle : ∀ x ∈ Algebra.adjoin K₀ (s : Set K), x ∈ K₁ := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact hs hx
    | algebraMap r => exact h r.2
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy
  let e : Algebra.adjoin K₀ (s : Set K) →+* K₁ :=
    (Algebra.adjoin K₀ (s : Set K)).val.toRingHom.codRestrict K₁ fun x ↦ hle x x.2
  have he₁ : spMap e ≫ spMap (algebraMap K₀ (Algebra.adjoin K₀ (s : Set K))) =
      spMap (Subfield.inclusion h) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have he₂ : spMap K₁.subtype ≫ spMap e =
      spMap (Algebra.adjoin K₀ (s : Set K)).val.toRingHom := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  let u : X₁ ⟶ pullback p₀ (spMap (algebraMap K₀ (Algebra.adjoin K₀ (s : Set K)))) :=
    pullback.lift φ₁ (p₁ ≫ spMap e) (by rw [Category.assoc, he₁, h₁.w])
  have hu : ψ ≫ u = hX'.isoPullback.hom ≫ Spread.bcMap p₀ (Algebra.adjoin K₀ (s : Set K)).val := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, Spread.bcMap_fst, IsPullback.isoPullback_hom_fst,
        pullback.lift_fst, hψ₁]
    · rw [Category.assoc, Category.assoc, Spread.bcMap_snd, IsPullback.isoPullback_hom_snd_assoc,
        pullback.lift_snd, ← Category.assoc, hψ₂, Category.assoc, he₂]
  refine ⟨fun j ↦ u ≫ g j, fun j ↦ ⟨?_, ?_⟩⟩
  · rw [← Category.assoc, hu, Category.assoc, (hg j).2, Iso.hom_inv_id_assoc]
  · rw [Category.assoc, (hg j).1, pullback.lift_fst_assoc]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.MorphismsGenericSpreadOut
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.GenericSpread

theorem exists_away_of_fg {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (S : Subalgebra R K) (hS : S.FG) :
    ∃ (f : R) (_ : f ≠ 0) (g : S →ₐ[R] Localization.Away f) (l : Localization.Away f →ₐ[R] K),
      ∀ x, l (g x) = x := by
  classical
  obtain ⟨t, rfl⟩ := hS
  choose p hp using fun x : K => IsLocalization.surj (nonZeroDivisors R) x
  set f : R := ∏ x ∈ t, ((p x).2 : R) with hf_def
  have hf0 : f ≠ 0 := Finset.prod_ne_zero_iff.mpr fun x _ => nonZeroDivisors.ne_zero (p x).2.2
  have hfK : IsUnit (algebraMap R K f) :=
    ((map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hf0).isUnit
  have hpow : ∀ y : Submonoid.powers f, IsUnit (algebraMap R K y) := by
    rintro ⟨_, n, rfl⟩
    simpa using hfK.pow n
  let l : Localization.Away f →ₐ[R] K :=
    ⟨IsLocalization.lift (M := Submonoid.powers f) (S := Localization.Away f) hpow,
      fun r => IsLocalization.lift_eq hpow r⟩
  have hl : Function.Injective l := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) z
    have h1 := congrArg l (IsLocalization.mk'_spec (Localization.Away f) a s)
    rw [map_mul, hz, zero_mul, AlgHom.commutes] at h1
    have ha : a = 0 := (IsFractionRing.injective R K) (by rw [← h1, map_zero])
    subst ha
    exact IsLocalization.mk'_zero s
  have hle : Algebra.adjoin R (↑t : Set K) ≤ l.range := by
    rw [Algebra.adjoin_le_iff]
    intro x hx
    rw [SetLike.mem_coe, AlgHom.mem_range]
    have hdvd : ((p x).2 : R) ∣ f := Finset.dvd_prod_of_mem _ (Finset.mem_coe.mp hx)
    have hu : IsUnit (algebraMap R (Localization.Away f) ((p x).2 : R)) :=
      isUnit_of_dvd_unit (map_dvd _ hdvd) (IsLocalization.Away.algebraMap_isUnit f)
    refine ⟨algebraMap R _ (p x).1 * ↑hu.unit⁻¹, ?_⟩
    have hne : algebraMap R K ((p x).2 : R) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr (nonZeroDivisors.ne_zero (p x).2.2)
    apply mul_right_cancel₀ hne
    calc l (algebraMap R _ (p x).1 * ↑hu.unit⁻¹) * algebraMap R K ((p x).2 : R)
        = l (algebraMap R _ (p x).1 * ↑hu.unit⁻¹ * algebraMap R _ ((p x).2 : R)) := by
          rw [map_mul l _ (algebraMap R _ _), AlgHom.commutes]
      _ = l (algebraMap R _ (p x).1) := by rw [_root_.mul_assoc, IsUnit.val_inv_mul, _root_.mul_one]
      _ = algebraMap R K (p x).1 := AlgHom.commutes l _
      _ = x * algebraMap R K ((p x).2 : R) := (hp x).symm
  refine ⟨f, hf0, (AlgEquiv.ofInjective l hl).symm.toAlgHom.comp (Subalgebra.inclusion hle), l,
    fun x => ?_⟩
  show l ((AlgEquiv.ofInjective l hl).symm (Subalgebra.inclusion hle x)) = x
  rw [← AlgEquiv.ofInjective_apply l hl, AlgEquiv.apply_symm_apply]
  rfl

end GlobalTheory.GenericSpread

namespace GlobalTheory

theorem morphisms_generic_spread_out :
    ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (B Z : Scheme.{0}) (pB : B ⟶ Sp R) (pZ : Z ⟶ Sp R) (I : Type) [Finite I] (u : I → (pullback pB (spMap (algebraMap R K)) ⟶ Z)), QuasiCompact pB → QuasiSeparated pB → LocallyOfFinitePresentation pZ → (∀ i, u i ≫ pZ = pullback.fst _ _ ≫ pB) → ∃ (f : R) (_ : f ≠ 0) (u' : I → (pullback pB (spMap (algebraMap R (Localization.Away f))) ⟶ Z)), ∀ i, u' i ≫ pZ = pullback.fst _ _ ≫ pB ∧ ∀ j : pullback pB (spMap (algebraMap R K)) ⟶ pullback pB (spMap (algebraMap R (Localization.Away f))), j ≫ pullback.fst _ _ = pullback.fst _ _ → j ≫ u' i = u i := by
  intro R K _ _ _ _ _ _ B Z pB pZ I _ u hqc hqs hlfp hu
  have := hqc
  have := hqs
  have := hlfp
  obtain ⟨S, ψ, hSfg, -, hψ⟩ :=
    GlobalTheory.Spread.exists_fg_forall_comp_eq pB pZ u hu ⊥ Subalgebra.fg_bot
  obtain ⟨f, hf0, g, l, hgl⟩ := GlobalTheory.GenericSpread.exists_away_of_fg S hSfg
  have hmono : Mono (spMap (algebraMap R (Localization.Away f))) := inferInstance
  refine ⟨f, hf0, fun i => GlobalTheory.Spread.bcMap pB g ≫ ψ i, fun i => ⟨?_, fun j hj => ?_⟩⟩
  · rw [Category.assoc, (hψ i).1, ← Category.assoc, GlobalTheory.Spread.bcMap_fst]
  · have hj2 : j ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap l.toRingHom := by
      apply (cancel_mono (spMap (algebraMap R (Localization.Away f)))).mp
      rw [Category.assoc, Category.assoc, GlobalTheory.Spread.spMap_algHom_comp, ← pullback.condition,
        ← pullback.condition, ← Category.assoc, hj]
    have hjb : j = GlobalTheory.Spread.bcMap pB l := GlobalTheory.Spread.eq_bcMap pB l hj hj2
    rw [hjb, ← Category.assoc, GlobalTheory.Spread.bcMap_comp_of_eq pB g l S.val hgl]
    exact (hψ i).2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PelObjectClassPrimAndIsoClosed
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.PelPrim

def chartPullSection {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (ψ : X ⟶ Y) (e : ψ ≫ φ = 𝟙 X) :
    ChartPull L (L.pull φ) ψ :=
  have le : ∀ i, L.U i ≤ ψ ⁻¹ᵁ (L.pull φ).U (fun _ => i) := fun i y hy => mem_pull.2 (by
    have : (ψ ≫ φ) y ∈ L.U i := by rw [e]; exact hy
    exact this)
  { idx := fun i _ => i
    le := le
    g := fun y i j hi hj =>
      ((gm_pull_g L φ ψ y (fun _ => i) (fun _ => j) (le i hi) (le j hj)).trans (by rw [e])).symm }

theorem lbIso_inv {X Y : Scheme.{0}} {L : LB X} {M : LB Y} {φ : Y ⟶ X} {ψ : X ⟶ Y} (e : ψ ≫ φ = 𝟙 X)
    (h : LBIso M (L.pull φ)) : LBIso L (M.pull ψ) :=
  (LBIso.chartPull (chartPullPull M ψ ψ rfl) (chartPullSection L φ ψ e) h).symm

theorem lbIso_comp {X X' X'' : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} {F : X' ⟶ X} {F' : X'' ⟶ X'}
    (hL : L.IsLB) (hL' : L'.IsLB) (hL'' : L''.IsLB) (h : LBIso L' (L.pull F)) (h' : LBIso L'' (L'.pull F')) :
    LBIso L'' (L.pull (F' ≫ F)) := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨w', hw'⟩ := h'
  obtain ⟨w'', T⟩ := exists_comp hL' w w' ((isGen_iff w).1 hw) ((isGen_iff w').1 hw') hL hL''
  exact ⟨w'', (isGen_iff w'').2 (T.pgen_comp hL' ((isGen_iff w).1 hw) ((isGen_iff w').1 hw'))⟩

theorem lbIso_linComb {X Y : Scheme.{0}} {L M : LB X} (h : LBIso L M) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (ε : K → ℤ) : LBIso (LB.LinComb L φ ε) (LB.LinComb M φ ε) := by
  obtain ⟨w, hw⟩ := h
  exact ⟨_, DVR.linCombIso_isGen w hw φ ε⟩

section Cube
variable {S : Scheme.{0}} {G A : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A]

theorem psum_comp (ψ : A ⟶ G) [IsMonHom ψ] {T T' : Over S} {n : ℕ} (x' : Fin n → (T' ⟶ A)) (x : Fin n → (T ⟶ G))
    (U : T' ⟶ T) (hx : ∀ i, x' i ≫ ψ = U ≫ x i) (I : Finset (Fin n)) :
    (psum A x' I).left ≫ ψ.left = U.left ≫ (psum G x I).left := by
  have e : psum A x' I ≫ ψ = U ≫ psum G x I :=
    (psum_hom (MonoidHom.mk' (· ≫ ψ) fun a b => MonObj.mul_comp a b ψ) x' I).trans
      ((congrArg (fun z => psum G z I) (funext hx)).trans (psum_hom (preHom U) x I).symm)
  exact congrArg (fun z => z.left) e

def chartPullCube (ψ : A ⟶ G) [IsMonHom ψ] (M : LB G.left) {T T' : Over S} {n : ℕ} (x' : Fin n → (T' ⟶ A))
    (x : Fin n → (T ⟶ G)) (U : T' ⟶ T) (hx : ∀ i, x' i ≫ ψ = U ≫ x i) :
    ChartPull (cubeLB A x' (M.pull ψ.left)) (cubeLB G x M) U.left :=
  chartPullLinComb M _ _ _ _ U.left fun I => psum_comp ψ x' x U hx I.down

omit [IsCommMonObj A] in
theorem cube_isLB {L : LB A.left} (hL : L.IsLB) {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ A)) : (cubeLB A x L).IsLB :=
  DVR.linComb_isLB L hL _ _

omit [IsCommMonObj A] in
theorem cube_congr {L M : LB A.left} (h : LBIso L M) {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ A)) :
    LBIso (cubeLB A x L) (cubeLB A x M) := lbIso_linComb h _ _

theorem adj_pull (ψ : A ⟶ G) [IsMonHom ψ] {L : LB A.left} {M : LB G.left} (hL : L.IsLB) (hM : M.IsLB)
    (h : LBIso L (M.pull ψ.left)) {u v : A ⟶ A} {u₀ v₀ : G ⟶ G} (hu : u ≫ ψ = ψ ≫ u₀) (hv : v ≫ ψ = ψ ≫ v₀)
    (H : LBIso (cubeLB G ![fst G G ≫ u₀, snd G G] M) (cubeLB G ![fst G G, snd G G ≫ v₀] M)) :
    LBIso (cubeLB A ![fst A A ≫ u, snd A A] L) (cubeLB A ![fst A A, snd A A ≫ v] L) := by
  have hP := pull_isLB hM ψ.left
  refine ((cube_congr h _).trans (cube_isLB hL _) (cube_isLB hP _) (cube_isLB hP _) ?_).trans
    (cube_isLB hL _) (cube_isLB hP _) (cube_isLB hL _) (cube_congr h _).symm
  refine LBIso.chartPull (chartPullCube ψ M _ _ (ψ ⊗ₘ ψ) fun i => ?_) (chartPullCube ψ M _ _ (ψ ⊗ₘ ψ) fun i => ?_) H
  · fin_cases i <;> simp [hu]
  · fin_cases i <;> simp [hv]

theorem prim_pull (ψ : A ⟶ G) [IsMonHom ψ] {L : LB A.left} {M : LB G.left} (hL : L.IsLB) (hM : M.IsLB)
    (h : LBIso L (M.pull ψ.left)) {u : A ⟶ A} {u₀ : G ⟶ G} (hu : u ≫ ψ = ψ ≫ u₀)
    (H : LBIso M (cubeLB G ![𝟙 G, u₀] M)) : LBIso L (cubeLB A ![𝟙 A, u] L) := by
  have hP := pull_isLB hM ψ.left
  refine (h.trans hL hP (cube_isLB hP _) ?_).trans hL (cube_isLB hP _) (cube_isLB hL _) (cube_congr h _).symm
  refine LBIso.chartPull (chartPullPull M _ ψ.left rfl) (chartPullCube ψ M _ _ ψ fun i => ?_) H
  fin_cases i <;> simp [hu]

end Cube

theorem cmHostUnit_add_conj_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) : H.w0 + H.bar H.w0 = 1 := by
  have hd : 0 < H.d := H.d_prime.pos
  have h1 : H.bar H.rt ^ 2 = H.rt ^ 2 := by rw [← map_pow, H.rt_sq]; simp
  have h2 : H.bar H.rt = -H.rt := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
    · exfalso
      obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
      have e := H.bar_eq H.rt
      rw [h] at e
      have e2 : starRingEnd ℂ (φ (H.rt : E)) = φ (H.rt : E) := by
        rw [← IsCMField.complexEmbedding_complexConj, ← e]
      have e3 : φ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
        have := congrArg (fun z : 𝓞 E => φ (z : E)) H.rt_sq
        simpa using this
      obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 e2
      rw [hr] at e3
      have e4 : r ^ 2 = -(H.d : ℝ) := by exact_mod_cast e3
      have : (0 : ℝ) < H.d := by exact_mod_cast hd
      nlinarith [sq_nonneg r]
    · exact h
  have h3 : 2 * H.bar H.w0 = 1 - H.rt := by
    have := congrArg H.bar H.two_weight_eq_one_add_root
    rw [map_mul, map_add, map_one, h2, map_ofNat] at this
    rw [this]; ring
  have h4 : (2 : 𝓞 E) * (H.w0 + H.bar H.w0) = 2 * 1 := by rw [mul_add, h3, H.two_weight_eq_one_add_root]; ring
  exact mul_left_cancel₀ two_ne_zero h4

end GlobalTheory.PelPrim

open GlobalTheory.PelPrim in

theorem GlobalTheory.pelClass_prim_and_iso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (ρ : o) (t : TObj g k J b (spMap em)), PELClass D a bas ρ em t → (a w = H.w0 → a w' = H.bar H.w0 → t.Prim w w') ∧ ∀ t' : TObj g k J b (spMap em), TMap t' t (𝟙 _) → PELClass D a bas ρ em t' := by
  intro E _ _ _ H D o _ g k J b em w w' a bas ρ t ⟨τ, φ, hφ, hL, hact, hpt⟩
  refine ⟨fun hw hw' => ?_, fun t' ⟨ψ, hψ, hL', hpt', hact'⟩ => ?_⟩
  · let _ := t.ab.comm
    have hinv : ∀ j, t.act j ≫ φ.inv = φ.inv ≫ τ.act.act (a j) := fun j => by
      rw [Iso.comp_inv_eq, Category.assoc, hact, φ.inv_hom_id_assoc]
    have hL₀ : LBIso t.L (τ.PP.L.pull φ.inv.left) :=
      lbIso_inv (by rw [← Over.comp_left, φ.inv_hom_id, Over.id_left]) hL
    refine ⟨?_, adj_pull φ.inv t.isLB τ.PP.isLB hL₀ (hinv w) (hinv w') ?_,
      prim_pull φ.inv t.isLB τ.PP.isLB hL₀ (hinv w) ?_⟩
    · rw [← cancel_epi φ.hom, MonObj.comp_mul, ← hact, ← hact, ← MonObj.mul_comp, ← τ.act.add, hw, hw', cmHostUnit_add_conj_eq_one,
        τ.act.one, Category.id_comp, Category.comp_id]
    · rw [hw, hw']; exact τ.adj _
    · rw [hw]; exact τ.prim
  · have : IsMonHom (Iso.refl t.A).hom := inferInstanceAs (IsMonHom (𝟙 t.A))
    obtain ⟨e, he, hl⟩ := grpPullback_iso hψ (isGrpPullback_of_iso (Iso.refl t.A))
    have hl' : e.hom.left = ψ := (Category.comp_id _).symm.trans hl
    subst hl'
    have hact₀ : ∀ j, t.act j ≫ e.inv = e.inv ≫ t'.act j := fun j => by
      have : t'.act j ≫ e.hom = e.hom ≫ t.act j := Over.OverMorphism.ext (hact' j)
      rw [Iso.comp_inv_eq, Category.assoc, this, e.inv_hom_id_assoc]
    have hpt₀ : ∀ i, t.pt i ≫ e.inv = t'.pt i := fun i => by
      have : t'.pt i ≫ e.hom = t.pt i := Over.OverMorphism.ext ((hpt' i).trans (Category.id_comp _))
      rw [Iso.comp_inv_eq, this]
    have hL₀ : LBIso t.L (t'.L.pull e.inv.left) :=
      lbIso_inv (by rw [← Over.comp_left, e.inv_hom_id, Over.id_left]) hL'
    refine ⟨τ, φ ≪≫ e.symm, inferInstanceAs (IsMonHom (φ.hom ≫ e.inv)),
      lbIso_comp t'.isLB t.isLB τ.PP.isLB hL₀ hL, fun j => ?_, fun K _ _ _ x β hx => ?_⟩
    · show _ ≫ φ.hom ≫ e.inv = (φ.hom ≫ e.inv) ≫ _
      rw [← Category.assoc, hact, Category.assoc, hact₀, Category.assoc]
    · obtain ⟨h₁, I, h₂, h₃⟩ := hpt K x β hx
      refine ⟨h₁, I, h₂, fun i => ?_⟩
      show _ ≫ φ.hom ≫ e.inv = _
      rw [← Category.assoc, h₃, Category.assoc, hpt₀]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ProjectiveRepresentationPullbackCoordinates
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM.RepBC
variable {X Y Z : Scheme.{0}}

theorem rr {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (a : Γ(X, U)) :
    resG X h₂ (resG X h₁ a) = resG X (h₂.trans h₁) a := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl

theorem r_self {U : X.Opens} (h : U ≤ U) (a : Γ(X, U)) : resG X h a = a := by
  have : (homOfLE h).op = 𝟙 _ := rfl
  simp only [resG, this, CategoryTheory.Functor.map_id]; rfl

theorem r_appLE (f : Y ⟶ X) {U : X.Opens} {V W : Y.Opens} (e : V ≤ f ⁻¹ᵁ U) (h : W ≤ V) (a : Γ(X, U)) :
    resG Y h ((f.appLE U V e).hom a) = (f.appLE U W (h.trans e)).hom a := by
  rw [← f.appLE_map e (homOfLE h).op]; rfl

theorem appLE_r (f : Y ⟶ X) {U U' : X.Opens} {V : Y.Opens} (e : V ≤ f ⁻¹ᵁ U) (h : U ≤ U') (a : Γ(X, U')) :
    (f.appLE U V e).hom (resG X h a) = (f.appLE U' V (e.trans (fun _ hy => h hy))).hom a := by
  rw [← f.map_appLE e (homOfLE h).op]; rfl

theorem appLE_appLE (f : Z ⟶ Y) (g : Y ⟶ X) {U : X.Opens} {V : Y.Opens} {W : Z.Opens} (e₁ : V ≤ g ⁻¹ᵁ U)
    (e₂ : W ≤ f ⁻¹ᵁ V) (e : W ≤ (f ≫ g) ⁻¹ᵁ U) (a : Γ(X, U)) :
    (f.appLE V W e₂).hom ((g.appLE U V e₁).hom a) = ((f ≫ g).appLE U W e).hom a := by
  rw [← Scheme.Hom.appLE_comp_appLE f g U V W e₁ e₂]; rfl

theorem pull_le (M : LB X) (f : Y ⟶ X) (j : PUnit → M.ι) : (M.pull f).U j ≤ f ⁻¹ᵁ M.U (j PUnit.unit) :=
  LB.wchart_le M (fun _ : PUnit => f) j PUnit.unit

theorem le_pull (M : LB X) (f : Y ⟶ X) (j : PUnit → M.ι) : f ⁻¹ᵁ M.U (j PUnit.unit) ≤ (M.pull f).U j :=
  fun _ h => Set.mem_iInter.2 fun _ => h

theorem pull_g (M : LB X) (f : Y ⟶ X) (j j' : PUnit → M.ι)
    (e : (M.pull f).U j ⊓ (M.pull f).U j' ≤ f ⁻¹ᵁ (M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit))) :
    ((M.pull f).g j j').val = (f.appLE _ _ e).hom (M.g (j PUnit.unit) (j' PUnit.unit)).val := by
  show ((∏ _k : PUnit, (res e (pullU f _ (M.g (j PUnit.unit) (j' PUnit.unit)))) ^ (1 : ℤ) :
    Γ(Y, (M.pull f).U j ⊓ (M.pull f).U j')ˣ)).val = _
  rw [Fintype.prod_unique, zpow_one]
  rfl

theorem pull_inf_le (M : LB X) (f : Y ⟶ X) (j j' : PUnit → M.ι) :
    (M.pull f).U j ⊓ (M.pull f).U j' ≤ f ⁻¹ᵁ (M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit)) :=
  fun _ h => ⟨pull_le M f j h.1, pull_le M f j' h.2⟩

def secPull (M : LB X) (f : Y ⟶ X) (s : M.Sec) : (M.pull f).Sec where
  f j := (f.appLE _ _ (pull_le M f j)).hom (s.f (j PUnit.unit))
  compat j j' := by
    have h := congrArg (f.appLE _ _ (pull_inf_le M f j j')).hom (s.compat (j PUnit.unit) (j' PUnit.unit))
    rw [map_mul] at h
    erw [← pull_g M f j j'] at h
    erw [appLE_r, appLE_r] at h
    erw [r_appLE, r_appLE]
    exact h

theorem isGen_val {L : LB X} (t : L.Gen) : t.IsGen ↔ ∀ i j, resG X (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) (t.s i).val =
    (L.g i j).val * resG X (inf_le_right : L.U i ⊓ L.U j ≤ L.U j) (t.s j).val :=
  forall₂_congr fun _ _ => Units.ext_iff

theorem le₁ (M : LB X) (π : Y ⟶ X) (x : Z ⟶ Y) (J : PUnit → PUnit → M.ι) :
    ((M.pull π).pull x).U J ≤ (M.pull (x ≫ π)).U (J PUnit.unit) :=
  fun _ h => le_pull M (x ≫ π) _ (pull_le M π _ (pull_le (M.pull π) x J h))

theorem le₂ (M : LB X) (π : Y ⟶ X) (x : Z ⟶ Y) (j : PUnit → M.ι) :
    (M.pull (x ≫ π)).U j ≤ ((M.pull π).pull x).U (fun _ => j) :=
  fun _ h => le_pull (M.pull π) x (fun _ => j) (le_pull M π _ (pull_le M (x ≫ π) j h))

theorem pullpull_g (M : LB X) (π : Y ⟶ X) (x : Z ⟶ Y) (J J' : PUnit → PUnit → M.ι)
    (e : ((M.pull π).pull x).U J ⊓ ((M.pull π).pull x).U J' ≤
      (x ≫ π) ⁻¹ᵁ (M.U (J PUnit.unit PUnit.unit) ⊓ M.U (J' PUnit.unit PUnit.unit))) :
    (((M.pull π).pull x).g J J').val =
      ((x ≫ π).appLE _ _ e).hom (M.g (J PUnit.unit PUnit.unit) (J' PUnit.unit PUnit.unit)).val := by
  rw [pull_g (M.pull π) x J J' (pull_inf_le _ _ _ _), pull_g M π _ _ (pull_inf_le _ _ _ _)]
  exact appLE_appLE x π _ _ e _

theorem secCoord_pull {σ : Type} (M : LB X) (th : σ → M.Sec) (π : Y ⟶ X) {T : Type} [CommRing T] (x : Sp T ⟶ Y)
    (v : σ → T) : SecCoord (M.pull π) (fun i => secPull M π (th i)) x v ↔ SecCoord M th (x ≫ π) v := by
  constructor
  · rintro ⟨τ, hτ, h⟩
    refine ⟨⟨fun j => res (le₂ M π x j) (τ.s fun _ => j)⟩, (isGen_val _).2 fun j j' => ?_, fun i j e => ?_⟩
    · have h0 := congrArg (resG (Sp T) (inf_le_inf (le₂ M π x j) (le₂ M π x j')))
        ((isGen_val τ).1 hτ (fun _ => j) (fun _ => j'))
      rw [map_mul] at h0
      erw [pullpull_g M π x (fun _ => j) (fun _ => j') ((inf_le_inf (le₁ M π x _) (le₁ M π x _)).trans (pull_inf_le M (x ≫ π) _ _)),
        rr, r_appLE] at h0
      erw [pull_g M (x ≫ π) j j' (pull_inf_le _ _ _ _)]
      exact (rr _ _ _).trans (h0.trans (congrArg _ ((rr _ _ _).trans (rr (le₂ M π x j') inf_le_right _).symm)))
    · have h0 := congrArg (resG (Sp T) (le₂ M π x j)) (h i (fun _ => j) (pull_le _ _ _))
      rw [map_mul, rr, r_appLE] at h0
      exact (appLE_appLE x π _ _ e _).symm.trans h0
  · rintro ⟨τ, hτ, h⟩
    refine ⟨⟨fun J => res (le₁ M π x J) (τ.s (J PUnit.unit))⟩, (isGen_val _).2 fun J J' => ?_, fun i J e => ?_⟩
    · have h0 := congrArg (resG (Sp T) (inf_le_inf (le₁ M π x J) (le₁ M π x J')))
        ((isGen_val τ).1 hτ (J PUnit.unit) (J' PUnit.unit))
      rw [map_mul] at h0
      erw [pull_g M (x ≫ π) (J PUnit.unit) (J' PUnit.unit) (pull_inf_le _ _ _ _), rr, r_appLE] at h0
      erw [pullpull_g M π x J J' ((inf_le_inf (le₁ M π x _) (le₁ M π x _)).trans (pull_inf_le M (x ≫ π) _ _))]
      exact (rr _ _ _).trans (h0.trans (congrArg _ ((rr _ _ _).trans (rr (le₁ M π x J') inf_le_right _).symm)))
    · have h0 := congrArg (resG (Sp T) (le₁ M π x J)) (h i (J PUnit.unit) (pull_le _ _ _))
      rw [map_mul, rr, r_appLE] at h0
      exact (appLE_appLE x π _ e _ _).trans h0

theorem projRep_baseChange : ∀ (R R' σ : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (I : Ideal (MvPolynomial σ R)) (Z Z' : Scheme.{0}) (s : Z ⟶ Sp R) (s' : Z' ⟶ Sp R') (π : Z' ⟶ Z) (M : LB Z) (th : σ → M.Sec), ProjRep I s M th → IsPullback π s' s (spMap φ) → ∃ th' : σ → (M.pull π).Sec, ProjRep (I.map (MvPolynomial.map φ)) s' (M.pull π) th' ∧ ∀ (T : Type) [CommRing T] (x : Sp T ⟶ Z') (v : σ → T), SecCoord (M.pull π) th' x v ↔ SecCoord M th (x ≫ π) v := by
  intro R R' σ _ _ φ I Z Z' s s' π M th ⟨hM, hloc, hpts⟩ hp
  refine ⟨fun i => secPull M π (th i), ⟨pull_isLB hM π, fun T _ β x v hx hv => ?_, fun T _ β v hu hF => ?_⟩,
    fun T _ x v => secCoord_pull M th π x v⟩
  · have hs : (x ≫ π) ≫ s = spMap (β.comp φ) := by
      rw [Category.assoc, hp.w, ← Category.assoc, hx, spMap_comp]
    obtain ⟨h1, h2⟩ := hloc T (β.comp φ) (x ≫ π) v hs ((secCoord_pull M th π x v).1 hv)
    refine ⟨h1, fun F hF => ?_⟩
    have : I.map (MvPolynomial.map φ) ≤ RingHom.ker (MvPolynomial.eval₂Hom β v) := by
      rw [Ideal.map_le_iff_le_comap]
      intro G hG
      rw [Ideal.mem_comap, RingHom.mem_ker, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_map]
      exact h2 G hG
    exact this hF
  · obtain ⟨y, ⟨hy, hv⟩, huniq⟩ := hpts T (β.comp φ) v hu fun G hG => by
      rw [← MvPolynomial.eval₂_map]
      exact hF _ (Ideal.mem_map_of_mem _ hG)
    have hw : y ≫ s = spMap β ≫ spMap φ := by rw [hy, spMap_comp]
    refine ⟨hp.lift y (spMap β) hw, ⟨hp.lift_snd _ _ _, (secCoord_pull M th π _ v).2 (by rw [hp.lift_fst]; exact hv)⟩, ?_⟩
    rintro x ⟨hx, hxv⟩
    apply hp.hom_ext
    · rw [hp.lift_fst]
      refine huniq _ ⟨?_, (secCoord_pull M th π x v).1 hxv⟩
      rw [Category.assoc, hp.w, ← Category.assoc, hx, spMap_comp]
    · rw [hp.lift_snd, hx]

end GlobalTheory.ZM.RepBC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothGenericFibreOfAffineOpens
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM

namespace GlobalTheory

theorem smoothOfRelativeDimension_genericFibre_of_affine :
    ∀ (o : Type) [CommRing o] [IsDomain o] (X : Scheme.{0}) (s : X ⟶ Sp o) (d : ℕ), (∀ (R : Type) [CommRing R] [Algebra o R] (x : Sp R ⟶ X), IsOpenImmersion x → x ≫ s = spMap (algebraMap o R) → SmoothOfRelativeDimension d (spMap (algebraMap (FractionRing o) (FractionRing o ⊗[o] R)))) → SmoothOfRelativeDimension d (pullback.snd s (spMap (algebraMap o (FractionRing o)))) := by
  intro o _ _ X s d h
  have hloc : IsZariskiLocalAtSource (@SmoothOfRelativeDimension d) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension d)
    (Scheme.Pullback.openCoverOfLeft X.affineOpenCover.openCover s
      (spMap (algebraMap o (FractionRing o)))) fun i => ?_
  let R : CommRingCat.{0} := X.affineOpenCover.X i
  let x : Spec R ⟶ X := X.affineOpenCover.f i
  have hx : IsOpenImmersion x := X.affineOpenCover.map_prop i
  let φ : CommRingCat.of o ⟶ R := Spec.preimage (x ≫ s)
  letI : Algebra o R := φ.hom.toAlgebra
  have hφ : x ≫ s = spMap (algebraMap o R) := (Spec.map_preimage (x ≫ s)).symm
  have H := h R x hx hφ
  have sq := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct o (FractionRing o) R)
  have sq' : IsPullback (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight (R := o) (A := FractionRing o) (B := R)).toRingHom))
      (spMap (algebraMap (FractionRing o) (FractionRing o ⊗[o] R))) (x ≫ s)
      (spMap (algebraMap o (FractionRing o))) := by
    rw [hφ]
    exact sq.flip
  have e : (Scheme.Pullback.openCoverOfLeft X.affineOpenCover.openCover s
      (spMap (algebraMap o (FractionRing o)))).f i ≫ pullback.snd s _ =
      sq'.isoPullback.inv ≫ spMap (algebraMap (FractionRing o) (FractionRing o ⊗[o] R)) := by
    rw [IsPullback.isoPullback_inv_snd]
    exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  rw [e]
  have : MorphismProperty.RespectsIso (@SmoothOfRelativeDimension d) := hloc.1
  exact @MorphismProperty.RespectsIso.precomp _ _ (@SmoothOfRelativeDimension d) this _ _ _
    sq'.isoPullback.inv sq'.isoPullback.isIso_inv _ H

end GlobalTheory
end

