import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0090
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0045
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HolomorphicMapModuliLiftsLocallyToPeriods
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0076
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.Bundle0007
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0079
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0017
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0088

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivOfPeriod
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.UnifPoint

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}} {g : ℕ}

def ReadsPeriods (t : SAB H S) {T : Over S} (c₀ : ℂˣ → Γ(T.left, ⊤)ˣ) (D : Datum H) (ty : Fin g → (E →+* ℂ))
    (P : D.La →+ (Fin g → ℂ)) (e : (Fin g → ℂ) → (T ⟶ t.G)) : Prop :=
  (∀ z, e z = 1 ↔ z ∈ P.range) ∧ (∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ t.act.act a) ∧
    ∀ (k : ℕ) (a a₂ : D.La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D.EF a a₂ : ℂ) / k) →
      Out.WeilIs t.G t.PP.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P a₂)) (c₀ c)

theorem int_eq_of_exp_eq {m n : ℤ} (h : ∀ k : ℕ, 0 < k → Complex.exp (-(2 * Real.pi * Complex.I) * (m : ℂ) / k) =
    Complex.exp (-(2 * Real.pi * Complex.I) * (n : ℂ) / k)) : m = n := by
  have hk : 0 < (n - m).natAbs + 1 := Nat.succ_pos _
  obtain ⟨j, hj⟩ := Complex.exp_eq_exp_iff_exists_int.1 (h _ hk)
  have h0 : (((n - m).natAbs + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have h1 : ((n - m : ℤ) : ℂ) = ((((n - m).natAbs + 1 : ℕ) : ℤ) * j : ℤ) := by
    apply mul_left_cancel₀ Complex.two_pi_I_ne_zero
    rw [Int.cast_mul, Int.cast_natCast, Int.cast_sub]
    generalize (((n - m).natAbs + 1 : ℕ) : ℂ) = k at h0 hj
    field_simp at hj
    linear_combination (2 * Real.pi * Complex.I) * hj
  have h2 : n - m = 0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs ⟨j, Int.cast_injective h1⟩ (by
    rw [Int.natAbs_natCast]; exact Nat.lt_succ_self _)
  omega

theorem discrete_periods {D : Datum H} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P) :
    DiscreteTopology P.range.toIntSubmodule := hP.2.2.1

theorem countable_periods {D : Datum H} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P) :
    (P.range : Set (Fin g → ℂ)).Countable :=
  have := hP.2.2.1
  countable_of_isDiscrete_finiteDimensional DiscreteTopology.isDiscrete

theorem exists_linearEquiv_of_period {t : SAB H S} {y : Sp ℂ ⟶ S} {D : Datum H} {ty : Fin g → (E →+* ℂ)}
    {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P) {e : (Fin g → ℂ) → (Over.mk y ⟶ t.G)} (he : IsExp e)
    (hk : ∀ z, e z = 1 ↔ z ∈ P.range) {g₀ : ℕ} {e₀ : (Fin g₀ → ℂ) → (Over.mk y ⟶ t.G)}
    (ha : ∀ z w, e₀ (z + w) = e₀ z * e₀ w) (hs : Function.Surjective e₀)
    (hh : IsHolTo Set.univ (fun z => (e₀ z).left)) (hc : {z | e₀ z = 1}.Countable) :
    ∃ h : (Fin g₀ → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ z, e (h z) = e₀ z := by
  have := t.semi.separated
  have := discrete_periods hP
  have : IsZLattice ℝ P.range.toIntSubmodule := ⟨hP.2.2.2.1⟩
  exact he.exists_linearEquiv P.range.toIntSubmodule hk ha hs hh hc

theorem exists_isometry {t : SAB H S} {y : Sp ℂ ⟶ S} {D D' : Datum H} {ty : Fin g → (E →+* ℂ)}
    {P : D.La →+ (Fin g → ℂ)} {P' : D'.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P) (hP' : IsPeriod D' ty P')
    {e e' : (Fin g → ℂ) → (Over.mk y ⟶ t.G)} (he : IsExp e) (he' : IsExp e')
    (hr : ReadsPeriods t unitOn D ty P e) (hr' : ReadsPeriods t unitOn D' ty P' e') :
    ∃ (gam : D.La ≃ₗ[𝓞 E] D'.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), (∀ a b, D'.EF (gam a) (gam b) = D.EF a b) ∧
      (∀ a, P' (gam a) = h (P a)) ∧ ∀ z, e' (h z) = e z := by
  obtain ⟨h, hh⟩ := exists_linearEquiv_of_period hP' he' hr'.1 he.1 he.2.1 he.2.2.1
    ((countable_periods hP).mono fun z hz => (hr.1 z).1 hz)
  have hcomm : ∀ (a : 𝓞 E) z, h (fun k => ty k (a : E) * z k) = fun k => ty k (a : E) * h z k := fun a z => by
    have := hP'.2.2.1
    have k := realLinear_eq_of_sub_mem_discrete (Γ := P'.range) DiscreteTopology.isDiscrete
      (L := (h.toLinearMap.restrictScalars ℝ) ∘ₗ LinearMap.mulLeft ℝ (fun k => ty k (a : E)))
      (L' := LinearMap.mulLeft ℝ (fun k => ty k (a : E)) ∘ₗ (h.toLinearMap.restrictScalars ℝ)) fun x =>
        (hr'.1 _).1 ((eq_iff_sub_of_add he'.1 _ _).1
          (((hh _).trans (hr.2.1 a x)).trans (by rw [← hh]; exact (hr'.2.1 a (h x)).symm)))
    exact DFunLike.congr_fun k z
  have hmem : ∀ a, ∃ b, P' b = h (P a) := fun a => (hr'.1 _).1 ((hh _).trans ((hr.1 _).2 ⟨a, rfl⟩))
  choose r₀ hr₀ using hmem
  let r₁ : D.La →ₗ[𝓞 E] D'.La :=
    { toFun := r₀
      map_add' := fun a b => hP'.2.1 (by rw [map_add, hr₀, hr₀, hr₀, map_add, map_add])
      map_smul' := fun c a => hP'.2.1 (by
        rw [hr₀, show P (c • a) = fun k => ty k (c : E) * P a k from funext (hP.1 c a), hcomm, ← hr₀]
        exact (funext (hP'.1 c (r₀ a))).symm) }
  have hb : Function.Bijective r₁ := by
    refine ⟨fun a b hab => hP.2.1 (h.injective (((hr₀ a).symm.trans (congrArg P' hab)).trans (hr₀ b))), fun b => ?_⟩
    obtain ⟨a, ha⟩ := (hr.1 (h.symm (P' b))).1 (by rw [← hh, h.apply_symm_apply]; exact (hr'.1 _).2 ⟨b, rfl⟩)
    exact ⟨a, hP'.2.1 ((hr₀ a).trans (by rw [ha, h.apply_symm_apply]))⟩
  refine ⟨LinearEquiv.ofBijective r₁ hb, h, fun a b => int_eq_of_exp_eq fun k hk => ?_, hr₀, hh⟩
  have w := hr.2.2 k a b (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
  have w' := hr'.2.2 k (r₀ a) (r₀ b) (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
  rw [hr₀, hr₀, ← map_smul h, ← map_smul h, hh, hh] at w'
  exact congrArg Units.val (weilIs_unique_fieldPoint _ _ _ t.PP.isLB ℂ y k _ _ _ _ w' w)

theorem div_eq_iff {L Q : Type*} [AddCommGroup L] [Group Q] {P : L →+ (Fin g → ℂ)} (hP : Function.Injective P)
    {e : (Fin g → ℂ) → Q} (he : ∀ z w, e (z + w) = e z * e w) (hk : ∀ z, e z = 1 ↔ z ∈ P.range) {n : ℕ} (hn : 0 < n)
    (a b : L) : e ((n : ℂ)⁻¹ • P a) = e ((n : ℂ)⁻¹ • P b) ↔ ∃ x, a = b + n • x := by
  have h0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  rw [eq_iff_sub_of_add he, hk, ← smul_sub, ← map_sub]
  refine exists_congr fun x => ?_
  rw [eq_inv_smul_iff₀ h0, Nat.cast_smul_eq_nsmul, ← map_nsmul, hP.eq_iff, eq_sub_iff_add_eq', eq_comm]

theorem exists_div_of_pow {L Q : Type*} [AddCommGroup L] [Group Q] {P : L →+ (Fin g → ℂ)}
    {e : (Fin g → ℂ) → Q} (he : ∀ z w, e (z + w) = e z * e w) (hs : Function.Surjective e)
    (hk : ∀ z, e z = 1 ↔ z ∈ P.range) {n : ℕ} (hn : 0 < n) {x : Q} (hx : x ^ n = 1) :
    ∃ a, x = e ((n : ℂ)⁻¹ • P a) := by
  have h0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  obtain ⟨z, rfl⟩ := hs x
  have hp : ∀ m : ℕ, e (m • z) = e z ^ m := fun m => by
    induction m with
    | zero => rw [zero_smul, pow_zero, map_zero_of_add he]
    | succ m ih => rw [succ_nsmul, he, ih, pow_succ]
  obtain ⟨a, ha⟩ := (hk _).1 ((hp n).trans hx)
  exact ⟨a, by rw [ha, ← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ h0]⟩

theorem exists_pointEquiv {S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {y : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G y φ) :
    ∃ β : (𝟙_ (Over S') ⟶ G') ≃* (Over.mk y ⟶ G), ∀ x, (β x).left = x.left ≫ φ := by
  have w : ∀ x : 𝟙_ (Over S') ⟶ G', x.left ≫ G'.hom = 𝟙 S' := fun x => Over.w x
  let f : (𝟙_ (Over S') ⟶ G') → (Over.mk y ⟶ G) := fun x => Over.homMk (x.left ≫ φ) (by
    show (x.left ≫ φ) ≫ G.hom = y
    rw [Category.assoc, h.1.w, ← Category.assoc, w]
    exact Category.id_comp y)
  have hb : Function.Bijective f := by
    refine ⟨fun a b hab => Over.OverMorphism.ext (h.1.hom_ext (congrArg (·.left) hab) ((w a).trans (w b).symm)),
      fun x => ?_⟩
    have hx : x.left ≫ G.hom = 𝟙 S' ≫ y := (Over.w x).trans (Category.id_comp y).symm
    exact ⟨Over.homMk (h.1.lift x.left (𝟙 S') hx) (h.1.lift_snd _ _ _), Over.OverMorphism.ext (h.1.lift_fst _ _ hx)⟩
  refine ⟨⟨Equiv.ofBijective f hb, fun a b => Over.OverMorphism.ext ?_⟩, fun _ => rfl⟩
  exact (h.2 _ a b (pushPt h.1.w a) (pushPt h.1.w b) rfl rfl).symm.trans
    (mul_left_congr (Category.id_comp y) _ _ _ _ rfl rfl)

theorem weilIs_congr {X : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} {a b : X ⟶ S} (h : a = b) {k : ℤ}
    {x y : Over.mk a ⟶ G} {x' y' : Over.mk b ⟶ G} (hx : x.left = x'.left) (hy : y.left = y'.left)
    {c : Γ(X, ⊤)ˣ} (H : Out.WeilIs G L k x y c) : Out.WeilIs G L k x' y' c := by
  subst h
  rwa [← Over.OverMorphism.ext hx, ← Over.OverMorphism.ext hy]

def WeilPull : Prop :=
  ∀ (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left)
    (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → IsGrpPullback G' G f φ → LBIso L' (L.pull φ) →
    ∀ (T : Over S') (k : ℤ) (x y : T ⟶ G') (x₀ y₀ : Over.mk (T.hom ≫ f) ⟶ G) (c : Γ(T.left, ⊤)ˣ),
      x₀.left = x.left ≫ φ → y₀.left = y.left ≫ φ → (Out.WeilIs G' L' k x y c ↔ Out.WeilIs G L k x₀ y₀ c)

theorem exists_fibre (hW : WeilPull) {t : SAB H S} {y : Sp ℂ ⟶ S} {t₁ : SAB H (Sp ℂ)} (m : SABMap t₁ t y)
    {D : Datum H} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P)
    {e : (Fin g → ℂ) → (Over.mk y ⟶ t.G)} (he : IsExp e) (hr : ReadsPeriods t unitOn D ty P e) :
    ∃ e₁ : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ t₁.G), (∀ z, (e₁ z).left ≫ m.φ = (e z).left) ∧
      (∀ z w, e₁ (z + w) = e₁ z * e₁ w) ∧ Function.Surjective e₁ ∧ ReadsPeriods t₁ unitOn D ty P e₁ ∧
      ∀ (g₀ : ℕ) (u : HolUnif t₁.G t₁.PP.L g₀), ∃ h : (Fin g₀ → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ z, e₁ (h z) = u.ex z := by
  obtain ⟨β, hβ⟩ := exists_pointEquiv m.cart
  have h₁ : ∀ z, (β.symm (e z)).left ≫ m.φ = (e z).left := fun z => by rw [← hβ, β.apply_symm_apply]
  refine ⟨fun z => β.symm (e z), h₁, fun z w => by simp only [he.1, map_mul], β.symm.surjective.comp he.2.1,
    ⟨fun z => by rw [← hr.1, β.symm.map_eq_one_iff], fun a z => ?_, fun k a b c hk hc => ?_⟩, fun g₀ u => ?_⟩
  · apply β.injective
    rw [β.apply_symm_apply, hr.2.1]
    apply Over.OverMorphism.ext
    rw [hβ, Over.comp_left, Over.comp_left, Category.assoc, m.act, ← Category.assoc, h₁]
  · obtain ⟨w, hw, -⟩ := m.lin
    refine (hW _ _ t.G t₁.G y m.φ _ _ t.PP.isLB t₁.PP.isLB m.cart ⟨w, hw⟩ _ k _ _ (pushPt m.cart.1.w _)
      (pushPt m.cart.1.w _) _ rfl rfl).2 ?_
    exact weilIs_congr (Category.id_comp y).symm (h₁ _).symm (h₁ _).symm (hr.2.2 k a b c hk hc)
  · have := u.discrete
    obtain ⟨h, hh⟩ := exists_linearEquiv_of_period hP he hr.1 (e₀ := fun z => β (u.ex z))
      (fun z w => by rw [u.ex_add, map_mul]) (β.surjective.comp u.ex_onto) (fun U f => by
        have k := u.hol (m.φ ⁻¹ᵁ U) ((m.φ.app U).hom f)
        simp only [hβ, Set.mem_univ, true_and, Points.valAt'_eq_valR] at k ⊢
        have k₂ : ∀ z, valR ((u.ex z).left ≫ m.φ) U f = valR (u.ex z).left (m.φ ⁻¹ᵁ U) ((m.φ.app U).hom f) :=
          fun z => Points.valR_comp (C := ℂ) (u.ex z).left m.φ U f
        exact ⟨k.1, k.2.congr fun z _ => k₂ z⟩)
      ((countable_of_isDiscrete_finiteDimensional (s := (u.Λ : Set (Fin g₀ → ℂ)))
        DiscreteTopology.isDiscrete).mono fun z hz => (u.ker z).1 (β.map_eq_one_iff.1 hz))
    exact ⟨h, fun z => by simp only [hh, β.symm_apply_apply]⟩

end GlobalTheory.UnifPoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HolomorphicMapModuliLiftsLocallyToPeriodsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_map_moduli_lifts_locally_to_periods : ThetaUnifAV → Out.Laws → (∀ (k
    : Type) [Field k] (X : Scheme.{0}) (s
    : X ⟶ Sp k), Smooth s → IsReduced X ∧ IsNormalScheme X ∧ IsLocallyNoetherian X) → (∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B
    : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o
    : Obj D l b s), IsAbelianScheme o.t.G ∧ SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p
    + D.q)) o.t.G.hom ∧ Out.Rigidified o.t.G o.t.PP.L ∧ Out.Sym o.t.G o.t.PP.L) → (∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B'
    : Type) [CommRing B] [CommRing B'] (b : Base l B) (b' : Base l B') (j : B →+* B') (S S'
    : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (f
    : S' ⟶ S), j b.ρ = b'.ρ → j b.ζ = b'.ζ → f ≫ s = s' ≫ spMap j → ∀ o : Obj D l b s, ∃ o' : Obj D l b' s', Nonempty (ObjMap
    o' o f)) → (∀ (k : Type) [Field k] (σ : k →+* ℂ) (X : Scheme.{0}) (s : X ⟶ Sp k) (G
    : Over X) [GrpObj G] (g m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (b₀
    : Fin m → ℂ) (e₀ : (Fin g → ℂ) → (Over.mk (y b₀) ⟶
    G)), LocallyOfFiniteType s → IsAbelianScheme G → SmoothOfRelativeDimension g G.hom → IsOpen B → b₀ ∈ B → (∀ b ∈ B, y b ≫ s = spMap σ) → IsHolTo B y → ((∀ z w, e₀ (z
    + w) = e₀ z * e₀ w) ∧ Function.Surjective e₀ ∧ IsHolTo Set.univ (fun z => (e₀ z).left) ∧
    (∀ w, ∃! v : epsPt (y b₀) ⟶ G, IsDerivAt0 (fun z => (e₀ z).left) w v.left) ∧ (∀ v : epsPt (y
    b₀) ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e₀
    0).left → ∃! w, IsDerivAt0 (fun z => (e₀ z).left) w v.left)) → ∃ (B' : Set (Fin m → ℂ)) (e
    : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)) (r
    : ℝ), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ e b₀ = e₀ ∧ 0 < r ∧ IsHolTo (B' ×ˢ Set.univ) (fun bz : (Fin
    m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left) ∧ (∀ b ∈ B', ((∀ z w, (e b) (z + w) = (e b) z * (e
    b) w) ∧ Function.Surjective (e b) ∧ IsHolTo Set.univ (fun z => ((e b) z).left) ∧
    (∀ w, ∃! v : epsPt (y b) ⟶ G, IsDerivAt0 (fun z => ((e b) z).left) w v.left) ∧ (∀ v : epsPt (y
    b) ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = ((e b)
    0).left → ∃! w, IsDerivAt0 (fun z => ((e b)
    z).left) w v.left)) ∧ ∀ z, ‖z‖ < r → e b z = 1 → z = 0) ∧ ∀ (n : ℕ) (W : Set (Fin n → ℂ)) (β
    : (Fin n → ℂ) → (Fin m → ℂ)) (x : ∀ w, Over.mk (y (β w)) ⟶ G) (w₀ : Fin n → ℂ) (z₀
    : Fin g → ℂ), IsOpen W → w₀ ∈ W → DifferentiableOn ℂ β W → Set.MapsTo β W B' → IsHolTo W (fun w => (x
    w).left) → e (β w₀) z₀ = x w₀ → ∃ ζ : (Fin n → ℂ) → (Fin g →
    ℂ), ζ w₀ = z₀ ∧ AnalyticAt ℂ ζ w₀ ∧ ∀ᶠ w in nhds w₀, e (β w) (ζ w) = x w) → (∀ (La
    : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (g m : ℕ) (B : Set (Fin m →
    ℂ)) (b₀ : Fin m → ℂ) (K : (Fin m → ℂ) → AddSubgroup (Fin g → ℂ)) (P : (Fin m → ℂ) → (La →+ (Fin
    g → ℂ))) (r : ℝ), IsOpen B → b₀ ∈ B → 0 < r → (∀ b ∈ B, ∀ z ∈ K b, ‖z‖ < r → z = 0) → (∀ (b
    : ℕ → (Fin m → ℂ)) (z : ℕ → (Fin g → ℂ)) (z₀ : Fin g → ℂ), Filter.Tendsto b Filter.atTop (nhds
    b₀) → Filter.Tendsto z Filter.atTop (nhds z₀) → (∀ i, z i ∈ K (b
    i)) → z₀ ∈ K b₀) → (∀ x, ContinuousAt (fun b => P b x) b₀) → (∀ b ∈ B, (P b).range ≤ K b) → (P
    b₀).range = K b₀ → Function.Injective (P b₀) → Submodule.span ℝ (Set.range (P
    b₀)) = ⊤ → ∀ᶠ b in nhds b₀, (P b).range = K b ∧ Function.Injective (P
    b) ∧ Submodule.span ℝ (Set.range (P b)) = ⊤ ∧ DiscreteTopology (P b).range) → (∀ (O
    : Type) [CommRing O] (g m : ℕ) (B : Set (Fin m → ℂ)) (b₀ : Fin m → ℂ) (F : (Fin m → ℂ) → (O →+*
    Matrix (Fin g) (Fin g) ℂ)) (ty : Fin g → (O →+* ℂ)), Module.Finite ℤ O → IsReduced (ℂ ⊗[ℤ]
    O) → IsOpen B → b₀ ∈ B → (∀ a i j, DifferentiableOn ℂ (fun b => F b a i j) B) → (∀ a, F b₀ a = Matrix.diagonal (fun i => ty i a)) → ∃ (B'
    : Set (Fin m → ℂ)) (h : (Fin m → ℂ) → Matrix (Fin g) (Fin
    g) ℂ), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ h b₀ = 1 ∧ (∀ i j, DifferentiableOn ℂ (fun b => h b i j) B') ∧ ∀ b ∈ B', IsUnit (h
    b) ∧ ∀ a, F b a * h b = h b * Matrix.diagonal (fun i => ty i a)) → (∀ (X
    : Scheme.{0}) [IsLocallyNoetherian X] (P : Out.PolAV X) (m k : ℕ) (B : Set (Fin m → ℂ)) (y
    : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (x x' : ∀ b, Over.mk (y b) ⟶ P.A) (c : ℂˣ) (b₀
    : Fin m → ℂ), 0 < k → IsUnit (k : Γ(X,
    ⊤)) → IsOpen B → IsPreconnected B → b₀ ∈ B → IsHolTo B (fun b => (x
    b).left) → IsHolTo B (fun b => (x' b).left) → (∀ b ∈ B, x b ^ k = 1 ∧ x' b ^ k = 1) → ((x b₀ =
    x' b₀ → ∀ b ∈ B, x b = x' b) ∧ (Out.WeilIs P.A P.L k (x b₀) (x' b₀) (unitOn c) →
    ∀ b ∈ B, Out.WeilIs P.A P.L k (x b) (x' b) (unitOn c)))) → ∀ (E : Type) [Field E] [NumberField
    E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g
    : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA
    l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (D' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (m : ℕ) (B
    : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ Xo.X)) (b₀ : Fin m → ℂ) (P₀ : D'.La →+ (Fin g →
    ℂ)) (e₀ : (Fin g → ℂ) → (Over.mk (y b₀) ⟶
    Xo.univ.t.G)), IsOpen B → b₀ ∈ B → (∀ b ∈ B, y b ≫ Xo.s = spMap σ) → IsHolTo B y → ((y b₀) ≫
    Xo.s = spMap σ ∧ IsPeriod D' ty P₀ ∧ ((∀ z w, e₀ (z + w) = e₀ z * e₀ w) ∧ Function.Surjective e₀
    ∧ IsHolTo Set.univ (fun z => (e₀ z).left) ∧ (∀ w, ∃! v : epsPt (y
    b₀) ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => (e₀ z).left) w v.left) ∧ (∀ v : epsPt (y
    b₀) ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e₀
    0).left → ∃! w, IsDerivAt0 (fun z => (e₀ z).left) w v.left)) ∧ (∀ z, e₀ z = 1 ↔ z ∈ (P₀).range)
    ∧ (∀ (a : 𝓞 E) z, e₀ (fun k => ty k (a : E) * z k) = e₀ z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a
    a₂ : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂
    : ℂ) / k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (e₀ ((k : ℂ)⁻¹ • P₀ a)) (e₀ ((k : ℂ)⁻¹ • P₀
    a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞
    E) D.La), toUnit _ ≫ Xo.univ.eta a = e₀ ((l.M : ℂ)⁻¹ • P₀ (t a))) ∧
    ∀ a, toUnit _ ≫ Xo.univ.etaA a = e₀ ((l.A : ℂ)⁻¹ • P₀ (t a))) → ∃ (B' : Set (Fin m → ℂ)) (P
    : (Fin m → ℂ) → (D'.La →+ (Fin g → ℂ))) (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶
    Xo.univ.t.G)), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ P b₀ = P₀ ∧ IsHolPeriods D' ty B' P ∧ IsHolTo (B'
    ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left) ∧ ∀ b ∈ B', ((y b) ≫
    Xo.s = spMap σ ∧ IsPeriod D' ty (P b) ∧ ((∀ z w, (e b) (z + w) = (e b) z * (e b) w) ∧
    Function.Surjective (e b) ∧ IsHolTo Set.univ (fun z => ((e b) z).left) ∧ (∀ w, ∃! v : epsPt (y
    b) ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => ((e b) z).left) w v.left) ∧ (∀ v : epsPt (y
    b) ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = ((e b)
    0).left → ∃! w, IsDerivAt0 (fun z => ((e b) z).left) w v.left)) ∧ (∀ z, (e b) z = 1 ↔ z ∈ ((P
    b)).range) ∧ (∀ (a : 𝓞 E) z, (e b) (fun k => ty k (a : E) * z k) = (e
    b) z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k → (c
    : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) /
    k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k ((e b) ((k : ℂ)⁻¹ • (P b) a)) ((e b) ((k : ℂ)⁻¹ •
    (P b) a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞
    E) D.La), toUnit _ ≫ Xo.univ.eta a = (e b) ((l.M : ℂ)⁻¹ • (P b) (t a))) ∧
    ∀ a, toUnit _ ≫ Xo.univ.etaA a = (e b) ((l.A : ℂ)⁻¹ • (P b) (t a))) := by
  first | exact @GlobalTheory.LocLift.holomorphic_map_lifts_to_periods | exact GlobalTheory.LocLift.holomorphic_map_lifts_to_periods | (intros; apply GlobalTheory.LocLift.holomorphic_map_lifts_to_periods <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IotaPointsAdditive
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorsionFormCompare
open scoped CategoryTheory.Obj

namespace GlobalTheory.IotaAdditive

open ReciprocityTheory.ChartRestriction.G.DVR

theorem val_eq_of_app_injective {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (h : Y' ⟶ Y)
    (hinj : ∀ U, Function.Injective (h.app U).hom) (t : LB.Gen (LB.LinComb L φ ε))
    (t' : LB.Gen (LB.LinComb L φ' ε')) (hF : FormEq φ ε φ' ε') (ht : t.IsGen) (ht' : t'.IsGen)
    (H : ∀ y J, Good L y J → val t h y J = val t' h y J) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (J)
    (hJ : Good L z J) : val t r z J = val t' r z J := by
  obtain ⟨u, hu, hv⟩ := exists_gen hL hF t ht
  have e : ∀ j, u.s j = t'.s j := fun j => Units.ext (hinj _ (fn_ext fun y hy => by
    choose I hI using fun χ : Y' ⟶ X => exists_chart hL (χ y)
    have hI' : Good L y I := hI
    have hy' : h y ∈ LB.wchart L φ' j := hy
    refine (gs_pull (𝟙 _) h y (LB.wchart L φ' j) hy' _).trans
      (Eq.trans ?_ (gs_pull (𝟙 _) h y (LB.wchart L φ' j) hy' _).symm)
    rw [Category.id_comp]
    refine (gs_unit h y _ hy' _).trans (Eq.trans (congrArg Units.val ?_) (gs_unit h y _ hy' _).symm)
    exact (gen_trans hu h y hy' (hI'.mem φ' h)).trans ((congrArg _ ((hv _ h y I hI').trans (H y I hI'))).trans
      (gen_trans ht' h y hy' (hI'.mem φ' h)).symm)))
  rw [← hv Z r z J hJ]
  exact congrArg (gm r z _) (e _)

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {W : (Spec (CommRingCat.of R)).Opens}

theorem restrict_app_injective (W : (Spec (CommRingCat.of R)).Opens) (U : W.toScheme.Opens) :
    Function.Injective ((jK R ∣_ W).app U).hom := by
  have : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
    show RingHom.ker (algebraMap R (FractionRing R)) ≤ _
    rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R _)]; exact bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (jK R)
  have : IsSchemeTheoreticallyDominant (jK R ∣_ W) :=
    IsSchemeTheoreticallyDominant.of_isPullback (isPullback_morphismRestrict (jK R) W).flip
  exact (jK R ∣_ W).app_injective U

theorem tau_isGen (ψW : PsiOn D W) (a b : D.X) : (ψW.tau a b).IsGen :=
  mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (ψW.psi_gen _)
    (invGen_isGen _ _ _ _ (ψW.psi_gen _))) (invGen_isGen _ _ _ _ (ψW.psi_gen _)))
    (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.rig_gen _))

theorem val_tau_generic (ψW : PsiOn D W) (a b : D.X) {z : (jK R ⁻¹ᵁ W).toScheme} {J} (hJ : Good D.P.L z J) :
    val (ψW.tau a b) (jK R ∣_ W) z J = val (D.tau a b) (jK R ⁻¹ᵁ W).ι z J := by
  have p : ∀ χ, val (ψW.psi χ) (jK R ∣_ W) z J = val (D.psi χ) (jK R ⁻¹ᵁ W).ι z J := fun χ => by
    have := ((val_pull hJ _ _ _).symm.trans (val_corr hJ (ψW.psi_eq χ) (𝟙 _))).trans (val_pull hJ _ _ _)
    rwa [Category.id_comp, Category.id_comp] at this
  have q : val (D.rigW W) (jK R ∣_ W) z J = val D.rigK (jK R ⁻¹ᵁ W).ι z J :=
    (val_pull hJ _ _ _).trans ((congrArg (fun r => val (L := D.P.L) D.rig r z J)
      (morphismRestrict_ι (jK R) W)).trans (val_pull hJ _ _ _).symm)
  exact ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (p _) ((val_inv _ _).trans (congrArg (·⁻¹) (p _)))))
    ((val_inv _ _).trans (congrArg (·⁻¹) (p _))))) ((val_inv _ _).trans (congrArg (·⁻¹) q)))).trans
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))).symm

theorem tau_mul (hB : D.TauBimult) (ψW : PsiOn D W) (a a' b : D.X) {T : Over (Spec (CommRingCat.of R))}
    (ρ : T ⟶ TW W) {z : T.left} {J} (hJ : Good D.P.L z J) :
    val (ψW.tau (a + a') b) ρ.left z J * th D z J (cP D T a) (cP D T a') (cP D T b) =
      val (ψW.tau a b) ρ.left z J * val (ψW.tau a' b) ρ.left z J := by
  have key := val_eq_of_app_injective D.P.isLB (jK R ∣_ W) (restrict_app_injective W)
    (LB.mulGen D.P.L _ _ _ _ (ψW.tau (a + a') b) (DegPre.cubAtT D (TW W) (cP D _ a) (cP D _ a') (cP D _ b)))
    (LB.mulGen D.P.L _ _ _ _ (ψW.tau a b) (ψW.tau a' b)) (fun U _ h => ?_)
    (mulGen_isGen _ _ _ _ _ _ _ (tau_isGen ψW _ _) (pullGen_isGen _ _ _ _ D.cub.isGen _))
    (mulGen_isGen _ _ _ _ _ _ _ (tau_isGen ψW _ _) (tau_isGen ψW _ _)) (fun y I hI => ?_) ρ.left z J hJ
  · have e := (val_mul hJ _ _ _).symm.trans (key.trans (val_mul hJ _ _ _))
    refine Eq.trans (congrArg₂ (· * ·) rfl ?_) e
    refine Eq.trans ?_ (val_cub D.cub ρ hJ (cP D _ a) (cP D _ a') (cP D _ b)).symm
    rw [comp_cP, comp_cP, comp_cP]
  · have p : ∀ x y w v : (TW W).left ⟶ D.P.A.left, ∏ i : ((PUnit ⊕ PUnit) ⊕ PUnit) ⊕ PUnit.{1},
        h (Sum.elim (Sum.elim (Sum.elim (fun _ => x) (fun _ => y)) (fun _ => w)) (fun _ => v) i) ^
          Sum.elim (Sum.elim (Sum.elim (fun _ => (-1 : ℤ)) (fun _ => - -1)) (fun _ => - -1)) (fun _ => -1) i =
        (h x)⁻¹ * h y * h w * (h v)⁻¹ := fun x y w v => by
      simp [Fintype.prod_sum_type]
    refine (prod_sum₂ (K' := thK) (U := U) _ (p (cP D _ (a + a' + b)).left (cP D _ (a + a')).left (cP D _ b).left
      (1 : TW W ⟶ D.P.A).left) (prod_cub (T := TW W) (U := U) (cP D _ a) (cP D _ a') (cP D _ b) h)).trans
      (Eq.trans ?_ (prod_sum₂ (U := U) _
        (p (cP D _ (a + b)).left (cP D _ a).left (cP D _ b).left (1 : TW W ⟶ D.P.A).left)
        (p (cP D _ (a' + b)).left (cP D _ a').left (cP D _ b).left (1 : TW W ⟶ D.P.A).left)).symm)
    simp only [cPoint_add]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · let T' : Over (Spec (CommRingCat.of R)) := Over.mk ((jK R ⁻¹ᵁ W).ι ≫ jK R)
    let κ : T' ⟶ TK R := Over.homMk (jK R ⁻¹ᵁ W).ι rfl
    let σ : T' ⟶ TW W := Over.homMk (jK R ∣_ W) (morphismRestrict_ι (jK R) W)
    have e := (val_mul hI _ _ _).symm.trans ((val_corr hI (hB a a' b) κ.left).trans (val_mul hI _ _ _))
    refine (val_mul hI _ _ _).trans (Eq.trans (congrArg₂ (· * ·) (val_tau_generic ψW _ _ hI) ?_) (e.trans
      ((val_mul hI _ _ _).trans (congrArg₂ (· * ·) (val_tau_generic ψW _ _ hI) (val_tau_generic ψW _ _ hI))).symm))
    refine (val_cub D.cub σ hI (cP D _ a) (cP D _ a') (cP D _ b)).trans
      (Eq.trans ?_ (val_cub D.cub κ hI (cP D _ a) (cP D _ a') (cP D _ b)).symm)
    simp only [comp_cP]

end GlobalTheory.IotaAdditive
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PreconnectedSpacePtsOfIsIntegral
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open Topology Filter

namespace GlobalTheory.OpenSubgroupPts

open GlobalTheory.Points

theorem isPreconnected_affineOpen {Y : Scheme.{0}} [IsIntegral Y] (p : Y ⟶ Sp ℂ) [LocallyOfFiniteType p]
    {U : Y.Opens} (hU : IsAffineOpen U) [Nonempty U] :
    IsPreconnected {x : Pts p | ⊤ ≤ x.1 ⁻¹ᵁ U} := by
  have key : ∀ {R : CommRingCat.{0}} [IsDomain R] (q : Spec R ⟶ Sp ℂ) [LocallyOfFiniteType q],
      PreconnectedSpace (Pts q) := by
    intro R _ q hft
    obtain ⟨φ, rfl⟩ := Spec.map_surjective q
    let _ := φ.hom.toAlgebra
    have : Algebra.FiniteType ℂ R := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 hft
    exact FiniteClasses.preconnectedSpace_pts R
  have := key (hU.fromSpec ≫ p)
  have h := isPreconnected_range (PtsOver.continuous_map (C := ℂ) hU.fromSpec (q := p) rfl (𝟙 _))
  rw [PtsOver.range_map, range_comp_of_isOpenImmersion, hU.opensRange_fromSpec] at h
  exact h

theorem preconnectedSpace_pts_of_isIntegral {Y : Scheme.{0}} [IsIntegral Y] (p : Y ⟶ Sp ℂ)
    [LocallyOfFiniteType p] : PreconnectedSpace (Pts p) := by
  refine ⟨isPreconnected_of_forall_pair fun x _ y _ => ?_⟩
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_le x.1 (le_preimage_top _)
  obtain ⟨V, hV, hy, -⟩ := exists_isAffineOpen_le y.1 (le_preimage_top _)
  have hx' := (le_preimage_iff x.1 U).1 hx
  have hy' := (le_preimage_iff y.1 V).1 hy
  have : Nonempty U := ⟨⟨_, hx'⟩⟩
  have : Nonempty V := ⟨⟨_, hy'⟩⟩
  obtain ⟨z, hz, hzm⟩ := ComplexPoints.exists_point_mem p (Z := (U : Set Y) ∩ V)
    (U.isOpen.inter V.isOpen).isLocallyClosed
    (nonempty_preirreducible_inter U.isOpen V.isOpen ⟨_, hx'⟩ ⟨_, hy'⟩)
  exact ⟨_, Set.subset_univ _, Or.inl hx, Or.inr hy, IsPreconnected.union (⟨z, hz⟩ : Pts p)
    ((le_preimage_iff z U).2 (hzm _).1) ((le_preimage_iff z V).2 (hzm _).2)
    (isPreconnected_affineOpen p hU) (isPreconnected_affineOpen p hV)⟩

theorem subgroup_eq_top_of_nhds_one :
    ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (x : Sp ℂ ⟶ X) (H : Subgroup (Over.mk x ⟶ G)) (U : G.left.Opens) (κ : Type) [Fintype κ] (f : κ → Γ(G.left, U)) (O : Set (κ → ℂ)), Smooth G.hom → GeometricallyConnected G.hom → IsOpen O → ⊤ ≤ (show Sp ℂ ⟶ G.left from (1 : Over.mk x ⟶ G).left) ⁻¹ᵁ U → (fun j => valAt' (1 : Over.mk x ⟶ G).left U (f j)) ∈ O → (∀ a : Over.mk x ⟶ G, ⊤ ≤ (show Sp ℂ ⟶ G.left from a.left) ⁻¹ᵁ U → (fun j => valAt' a.left U (f j)) ∈ O → a ∈ H) → H = ⊤ := by
  intro X G _ x H U κ _ f O hs hc hO h1 h1O hH
  let p := pullback.snd G.hom x
  have : IsIntegral (pullback G.hom x) :=
    isIntegral_of_isPullback_of_smooth (IsPullback.of_hasPullback G.hom x)
  have := preconnectedSpace_pts_of_isIntegral p
  let Y : Over X := Over.mk (p ≫ x)
  let π : Y ⟶ G := Over.homMk (pullback.fst G.hom x) pullback.condition
  let s : Y ⟶ Over.mk x := Over.homMk p rfl
  let inc : Pts p → (Over.mk x ⟶ Y) := fun y => Over.homMk y.1 (by
    show y.1 ≫ p ≫ x = x
    rw [← Category.assoc, y.2, Category.id_comp])
  have hin : ∀ y, inc y ≫ s = 𝟙 _ := fun y => Over.OverMorphism.ext y.2
  have hsurj : ∀ a : Over.mk x ⟶ G, ∃ y, inc y ≫ π = a := fun a =>
    ⟨⟨pullback.lift a.left (𝟙 _) ((Over.w a).trans (Category.id_comp x).symm), pullback.lift_snd _ _ _⟩,
      Over.OverMorphism.ext (pullback.lift_fst _ _ _)⟩
  have hopen : IsOpen {z : Sp ℂ ⟶ G.left | ⊤ ≤ z ⁻¹ᵁ U ∧ (fun j => valAt' z U (f j)) ∈ O} :=
    (continuousOn_pi.2 fun j => continuousOn_valR (C := ℂ) (f j)).isOpen_inter_preimage
      (isOpen_setOf_le_preimage U) hO
  have hl : IsLocallyConstant fun y : Pts p => inc y ≫ π ∈ H := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro y₀
    let τ : Y ⟶ G := (s ≫ (inc y₀ ≫ π)⁻¹) * π
    have hτ : ∀ y, inc y ≫ τ = (inc y₀ ≫ π)⁻¹ * (inc y ≫ π) := fun y => by
      rw [MonObj.comp_mul, ← Category.assoc, hin, Category.id_comp]
    have hcont : Continuous fun y : Pts p => (show Sp ℂ ⟶ G.left from (inc y ≫ τ).left) :=
      (continuous_comp (C := ℂ) (X := pullback G.hom x) τ.left).comp continuous_subtype_val
    have hN := (hopen.preimage hcont).mem_nhds (x := y₀) (by
      simp only [Set.mem_preimage, hτ, inv_mul_cancel]
      exact ⟨h1, h1O⟩)
    filter_upwards [hN] with y hy
    have h := hH _ hy.1 hy.2
    rw [hτ] at h
    have h' := H.mul_mem_cancel_right (y := inc y₀ ≫ π) h
    rw [mul_inv_cancel_left] at h'
    exact propext h'
  rw [eq_top_iff]
  intro a _
  obtain ⟨y, rfl⟩ := hsurj a
  obtain ⟨y₁, hy₁⟩ := hsurj 1
  have h := hl.apply_eq_of_preconnectedSpace y y₁
  simp only [hy₁] at h
  rw [h]
  exact H.one_mem

end GlobalTheory.OpenSubgroupPts
end

