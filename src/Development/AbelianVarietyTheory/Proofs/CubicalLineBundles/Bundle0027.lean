import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FamilyUniformisationFibreTheta
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieCombBaseChange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0044
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0021
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CountablePointsOfOnto
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CMCount

theorem eq_top_of_countable {V L : Type} [AddCommGroup V] [Module ℂ V] [Countable L] (W : Submodule ℂ V) (P : L → V)
    (h : ∀ z, ∃ a, z - P a ∈ W) : W = ⊤ := by
  by_contra hW
  obtain ⟨v, -, hv⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.2 hW)
  choose a ha using h
  have : Function.Injective fun c : ℂ => a (c • v) := fun c d e => by
    by_contra hne
    have h1 := W.sub_mem (ha (c • v)) (ha (d • v))
    simp only at e
    rw [e, sub_sub_sub_cancel_right, ← sub_smul] at h1
    exact hv ((W.smul_mem_iff (sub_ne_zero.2 hne)).1 h1)
  have : Countable ℂ := this.countable
  exact not_countable (Complex.ofReal_injective.countable)

theorem exists_basis {V L J : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [AddCommGroup L]
    (b : Module.Basis J ℤ L) (P : L →+ V) (hi : Function.Injective P) (hd : DiscreteTopology P.range)
    (hs : Submodule.span ℝ (Set.range P) = ⊤) : ∃ B : Module.Basis J ℝ V, ∀ i, B i = P (b i) := by
  let Λ : Submodule ℤ V := LinearMap.range P.toIntLinearMap
  have : DiscreteTopology Λ := hd
  have : IsZLattice ℝ Λ := ⟨hs⟩
  refine ⟨(b.map (LinearEquiv.ofInjective P.toIntLinearMap hi)).ofZLatticeBasis ℝ Λ, fun i => ?_⟩
  rw [Module.Basis.ofZLatticeBasis_apply]
  rfl

theorem exists_real_equiv {V L : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [AddCommGroup L]
    (P P' : L →+ V) (hi : Function.Injective P) (hd : DiscreteTopology P.range)
    (hs : Submodule.span ℝ (Set.range P) = ⊤) (hi' : Function.Injective P') (hd' : DiscreteTopology P'.range)
    (hs' : Submodule.span ℝ (Set.range P') = ⊤) : ∃ h : V ≃ₗ[ℝ] V, ∀ a, P' a = h (P a) := by
  let Λ : Submodule ℤ V := LinearMap.range P.toIntLinearMap
  have : DiscreteTopology Λ := hd
  have : IsZLattice ℝ Λ := ⟨hs⟩
  have : Module.Free ℤ L := Module.Free.of_equiv (LinearEquiv.ofInjective P.toIntLinearMap hi).symm
  let b := Module.Free.chooseBasis ℤ L
  obtain ⟨B, hB⟩ := exists_basis b P hi hd hs
  obtain ⟨B', hB'⟩ := exists_basis b P' hi' hd' hs'
  refine ⟨B.equiv B' (Equiv.refl _), fun a => ?_⟩
  have : P'.toIntLinearMap = ((B.equiv B' (Equiv.refl _)).toLinearMap.restrictScalars ℤ).comp P.toIntLinearMap :=
    b.ext fun i => by simp [← hB, ← hB']
  exact LinearMap.congr_fun this a

theorem exists_complex_equiv {U V I : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    [Module ℝ U] [Module ℝ V] [IsScalarTower ℝ ℂ U] [IsScalarTower ℝ ℂ V]
    (h : V ≃ₗ[ℝ] V) (F F' : I → (U →ₗ[ℂ] V)) (s : Set U) (hs : Submodule.span ℝ s = ⊤)
    (hF : ⨆ j, LinearMap.range (F j) = ⊤) (e : ∀ j, ∀ x ∈ s, F' j x = h (F j x)) :
    ∃ h' : V ≃ₗ[ℂ] V, ∀ v, h' v = h v := by
  have e' : ∀ j x, F' j x = h (F j x) := fun j x =>
    LinearMap.congr_fun (LinearMap.ext_on (f := (F' j).restrictScalars ℝ)
      (g := h.toLinearMap.comp ((F j).restrictScalars ℝ)) hs (e j)) x
  have hc : ∀ (c : ℂ) v, h (c • v) = c • h v := fun c v => by
    have hv : v ∈ ⨆ j, LinearMap.range (F j) := hF ▸ Submodule.mem_top
    induction hv using Submodule.iSup_induction' with
    | mem j x hx =>
      obtain ⟨x, rfl⟩ := hx
      rw [← map_smul, ← e', ← e', map_smul]
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
  exact ⟨{ h.toAddEquiv with map_smul' := hc }, fun _ => rfl⟩

theorem exists_compare {S S' : Scheme.{0}} {G : Over S} {A B : Over S'} [GrpObj G] [GrpObj A] [GrpObj B] {f : S' ⟶ S}
    {α : A.left ⟶ G.left} {β : B.left ⟶ G.left} (hA : IsGrpPullback A G f α) (hB : IsGrpPullback B G f β) :
    ∃ κ : A ⟶ B, IsMonHom κ ∧ ∀ (T : Over S') (z : T ⟶ B), ∃ y : T ⟶ A, y ≫ κ = z := by
  let κ : A ⟶ B := Over.homMk (hB.1.lift α A.hom hA.1.w) (hB.1.lift_snd ..)
  have hκ : κ.left ≫ β = α := hB.1.lift_fst ..
  refine ⟨κ, isMonHom_of_mul κ fun T x y => ?_, fun T z => ?_⟩
  · let x₀ : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk (x.left ≫ α) (by
      rw [Category.assoc, hA.1.w, Over.w_assoc]; rfl)
    let y₀ : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk (y.left ≫ α) (by
      rw [Category.assoc, hA.1.w, Over.w_assoc]; rfl)
    refine Over.OverMorphism.ext (hB.1.hom_ext ?_ (by rw [Over.w, Over.w]))
    rw [← hB.2 T (x ≫ κ) (y ≫ κ) x₀ y₀ (by simp [x₀, hκ]) (by simp [y₀, hκ]), hA.2 T x y x₀ y₀ rfl rfl,
      Over.comp_left, Category.assoc, hκ]
  · refine ⟨Over.homMk (hA.1.lift (z.left ≫ β) T.hom (by rw [Category.assoc, hB.1.w, Over.w_assoc]))
      (hA.1.lift_snd ..), Over.OverMorphism.ext (hB.1.hom_ext ?_ ?_)⟩
    · simp [hκ]
    · rw [Over.w, Over.w]

theorem exists_linear_onto {A B : Over (Sp ℂ)} [GrpObj A] [GrpObj B] {A₀ : Over (Sp ℂ)} [GrpObj A₀]
    (h₀ : IsAbelianScheme A₀) (hB : IsAbelianScheme B) {L₀ : LB A₀.left} {L : LB B.left} {g₀ g : ℕ}
    (u₀ : HolUnif A₀ L₀ g₀) (u : HolUnif B L g)
    (d₁ : ∀ v, IsTangent v → ∃! w, u.IsDiff w v) (d₂ : ∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v)
    (κ : A ⟶ B) [IsMonHom κ] (hκ : ∀ (T : Over (Sp ℂ)) (z : T ⟶ B), ∃ y : T ⟶ A, y ≫ κ = z)
    {I : Type} (ψ : I → (A₀ ⟶ A)) (hψ : ∀ i, IsMonHom (ψ i)) (ho : OntoAt ψ (𝟙 (Sp ℂ))) :
    ∃ F : I → ((Fin g₀ → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ j, ∀ x ∈ u₀.Λ, F j x ∈ u.Λ) ∧
      ∀ z, ∃ w ∈ ⨆ j, LinearMap.range (F j), z - w ∈ u.Λ := by
  choose F hF hΛ _ using fun j => HomLinear.exists_linear_of_isMonHom A₀ B h₀ hB L₀ L g₀ g u₀ u d₁ d₂ (ψ j ≫ κ) (by have := hψ j; infer_instance)
  refine ⟨F, hΛ, fun z => ?_⟩
  have key : ∀ l : List (𝟙_ (Over (Sp ℂ)) ⟶ A), (∀ y ∈ l, ∃ w ∈ ⨆ j, LinearMap.range (F j), y ≫ κ = u.ex w) →
      ∃ w ∈ ⨆ j, LinearMap.range (F j), l.prod ≫ κ = u.ex w := by
    intro l
    induction l with
    | nil => exact fun _ => ⟨0, Submodule.zero_mem _, by rw [(u.ker 0).2 u.Λ.zero_mem, List.prod_nil, MonObj.one_comp]⟩
    | cons y l ih =>
      intro h
      obtain ⟨w, hw, e⟩ := h y (by simp)
      obtain ⟨w', hw', e'⟩ := ih fun y hy => h y (by simp [hy])
      exact ⟨w + w', Submodule.add_mem _ hw hw', by rw [List.prod_cons, MonObj.mul_comp, e, e', u.ex_add]⟩
  obtain ⟨y, hy⟩ := hκ _ (u.ex z)
  obtain ⟨n, i, x, e⟩ := ho y
  obtain ⟨w, hw, e'⟩ := key (List.ofFn fun m => x m ≫ ψ (i m)) fun y hy => by
    obtain ⟨m, rfl⟩ := (List.mem_ofFn' _ _).1 hy
    obtain ⟨a, ha⟩ := u₀.ex_onto (x m)
    refine ⟨F (i m) a, Submodule.mem_iSup_of_mem (i m) ⟨a, rfl⟩, ?_⟩
    rw [hF, ha]
    exact Category.assoc ..
  refine ⟨w, hw, (u.ker _).1 ?_⟩
  have h1 : u.ex z = u.ex w := by rw [← hy, ← e', e]
  have h2 := u.ex_add (z - w) w
  rw [sub_add_cancel, h1] at h2
  exact mul_eq_right.1 h2.symm

end GlobalTheory.CMCount

namespace GlobalTheory

open CMCount

theorem countable_points_of_onto : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (P₀ : Out.PolAV (Sp ℂ)), Set.Countable {y : Sp ℂ ⟶ Xo.X | y ≫ Xo.s = spMap (algebraMap (KA l) ℂ) ∧ ∃ (t : SAB H (Sp ℂ)) (_ : SABMap t Xo.univ.t y) (n : ℕ) (ψ : Fin n → (P₀.A ⟶ t.G)), (∀ i, IsMonHom (ψ i)) ∧ OntoAt ψ (𝟙 (Sp ℂ))} := by
  intro hU hL E _ _ _ H D l Xo g ty FU P₀
  obtain ⟨rig, hrig⟩ := P₀.rigid
  obtain ⟨u₀, -⟩ := hU P₀ rig hrig
  obtain ⟨s, hsΛ, hs, hli⟩ := exists_linearIndependent ℝ (u₀.Λ : Set (Fin P₀.g → ℂ))
  rw [u₀.full] at hs
  have : Finite s := hli.finite
  have : Countable (𝓞 E) := Finsupp.Countable.of_moduleFinite (R := ℤ)
  have : ∀ i, Countable (FU.Di i).La := fun i =>
    have := (FU.Di i).fin
    Finsupp.Countable.of_moduleFinite (R := 𝓞 E)
  let R : (Sp ℂ ⟶ Xo.X) → (Σ i : Fin FU.n, Σ n : ℕ, Fin n → s → (FU.Di i).La) → Prop := fun y c =>
    ∃ P, IsPeriod (FU.Di c.1) ty P ∧ FU.u c.1 P = y ∧ ∃ F : Fin c.2.1 → ((Fin P₀.g → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
      ⨆ j, LinearMap.range (F j) = ⊤ ∧ ∀ j (x : s), F j x = P (c.2.2 j x)
  have huniq : ∀ c, {y | R y c}.Subsingleton := by
    rintro ⟨i, n, c⟩ _ ⟨P, hP, rfl, F, hF, e⟩ _ ⟨P', hP', rfl, F', -, e'⟩
    obtain ⟨h, hh⟩ := exists_real_equiv P P' hP.2.1 hP.2.2.1 hP.2.2.2.1 hP'.2.1 hP'.2.2.1 hP'.2.2.2.1
    obtain ⟨h', hh'⟩ := exists_complex_equiv h F F' s hs hF fun j x hx => by
      rw [e j ⟨x, hx⟩, e' j ⟨x, hx⟩, hh]
    exact (FU.fibre i P P' hP hP').2 ⟨LinearEquiv.refl _ _, h', fun _ _ => rfl, fun a _ => ⟨0, by simp⟩,
      fun a => ⟨0, by simp⟩, fun a => by rw [hh']; exact hh a⟩
  refine (Set.countable_iUnion fun c => (huniq c).countable).mono ?_
  rintro y ⟨hy, t, m, n, ψ, hψ, ho⟩
  obtain ⟨i, P, hP, rfl⟩ := FU.onto y hy
  obtain ⟨Q, φ, -, hQ, hQL, -⟩ := exists_polAV_pullback_of_isLocalRing E H _ Xo.univ.t Xo.univ.proper Xo.univ.ample
    Xo.univ.ktriv ℂ (FU.u i P)
  obtain ⟨u, -, -, Φ, -, d₁, d₂, -, -, hΦ, -⟩ := familyUnif_fibre_theta hU hL.weil E H D l Xo _ g ty FU i P hP Q φ hQ hQL
  obtain ⟨κ, hκ, hκ'⟩ := exists_compare m.cart hQ
  obtain ⟨F, hF, hF'⟩ := exists_linear_onto P₀.isAb Q.isAb u₀ u d₁ d₂ κ hκ' ψ hψ ho
  have hm : ∀ j (x : s), ∃ a, P a = Φ.symm (F j x) := fun j x =>
    (hΦ _).1 (by rw [Φ.apply_symm_apply]; exact hF j x (hsΛ x.2))
  choose c hc using hm
  refine Set.mem_iUnion.2 ⟨⟨i, n, c⟩, P, hP, rfl, fun j => Φ.symm.toLinearMap ∘ₗ F j, ?_, fun j x => (hc j x).symm⟩
  refine eq_top_of_countable _ P fun z => ?_
  obtain ⟨w, hw, hz⟩ := hF' (Φ z)
  obtain ⟨a, ha⟩ := (hΦ (z - Φ.symm w)).1 (by rwa [map_sub, Φ.apply_symm_apply])
  refine ⟨a, ?_⟩
  rw [ha, sub_sub_cancel]
  simp only [LinearMap.range_comp, ← Submodule.map_iSup]
  exact Submodule.mem_map_of_mem hw

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EigenLatticeNumberFieldBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem eigenBC_relation {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K']
    [Algebra K K'] {m : ℕ} (s : Fin m → 𝓞 K') (x : Fin m → K) (φ : 𝓞 K' →ₗ[𝓞 K] 𝓞 K)
    (h : ∑ i, (s i : K') * algebraMap K K' (x i) = 0) :
    ∑ i, ((φ (s i) : 𝓞 K) : K) * x i = 0 := by
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 K)) x
  choose y hy using hd
  have hd0 : ((d : 𝓞 K) : K) ≠ 0 := by
    have := nonZeroDivisors.coe_ne_zero d
    exact_mod_cast this
  have hy' : ∀ i, ((y i : 𝓞 K) : K) = ((d : 𝓞 K) : K) * x i := by
    intro i
    have := hy i
    rw [Algebra.smul_def] at this
    exact this
  have h1 : ∑ i, y i • s i = 0 := by
    apply RingOfIntegers.coe_injective
    rw [map_sum, map_zero]
    have : ∀ i, algebraMap (𝓞 K') K' (y i • s i)
        = algebraMap K K' ((d : 𝓞 K) : K) * ((s i : K') * algebraMap K K' (x i)) := by
      intro i
      rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply (𝓞 K) K K']
      have e : algebraMap (𝓞 K) K (y i) = ((d : 𝓞 K) : K) * x i := hy' i
      rw [e, map_mul]
      show _ * (s i : K') = _
      ring
    simp only [this]
    rw [← Finset.mul_sum, h, mul_zero]
  have h2 : ∑ i, y i * φ (s i) = 0 := by
    have := congrArg φ h1
    simpa [map_sum] using this
  have h3 := congrArg (algebraMap (𝓞 K) K) h2
  rw [map_sum, map_zero] at h3
  apply mul_left_cancel₀ hd0
  rw [mul_zero, Finset.mul_sum, ← h3]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul]
  have e : algebraMap (𝓞 K) K (y i) = ((d : 𝓞 K) : K) * x i := hy' i
  rw [e]
  show _ = _ * ((φ (s i) : 𝓞 K) : K)
  ring

theorem eigenBC_frame (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K']
    [Algebra K K'] : ∃ (m : ℕ) (b : Fin m → 𝓞 K') (φ : Fin m → (𝓞 K' →ₗ[𝓞 K] 𝓞 K)),
      ∀ s, s = ∑ k, φ k s • b k := by
  haveI : Module.FinitePresentation (𝓞 K) (𝓞 K') := Module.finitePresentation_of_finite _ _
  haveI : Module.Projective (𝓞 K) (𝓞 K') := Module.Flat.projective_of_finitePresentation
  obtain ⟨m, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective (𝓞 K) (𝓞 K')
  refine ⟨m, fun k => f (Pi.single k 1), fun k => (LinearMap.proj k).comp g, fun s => ?_⟩
  have := LinearMap.congr_fun hfg s
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
  conv_lhs => rw [← this, LinearMap.pi_apply_eq_sum_univ f (g s)]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [LinearMap.comp_apply, LinearMap.proj_apply]
  congr 2
  funext i
  simp [Pi.single_apply, eq_comm]

theorem eigenLattice_baseChange : ∀ (K K' O : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [CommRing O] (j : K →+* K') (n : ℕ) (Λ : Submodule (𝓞 K) (Fin n → K)) (r : O → Matrix (Fin n) (Fin n) K) (τ : O → K) (c' : Fin n → K'), Λ.FG → (c' ∈ Submodule.span (𝓞 K') ((fun c i => j (c i)) '' {c | c ∈ Λ ∧ ∀ a, (r a).mulVec c = τ a • c}) ↔ c' ∈ Submodule.span (𝓞 K') ((fun c i => j (c i)) '' (Λ : Set (Fin n → K))) ∧ ∀ a, ((r a).map j).mulVec c' = j (τ a) • c') := by
  intro K K' O _ _ _ _ _ j n Λ r τ c' _
  have hmap : ∀ a (c : Fin n → K), ((r a).map j).mulVec (fun i => j (c i))
      = fun i => j ((r a).mulVec c i) := by
    intro a c
    funext i
    simp [Matrix.mulVec, dotProduct, map_sum]
  constructor
  · intro h
    refine ⟨Submodule.span_mono (Set.image_mono fun c hc => hc.1) h, fun a => ?_⟩
    induction h using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, ⟨-, hc⟩, rfl⟩ := hx
      rw [hmap, hc a]
      funext i
      simp
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.mulVec_add, hx, hy, smul_add]
    | smul s x _ hx => rw [Matrix.mulVec_smul, hx, smul_comm]
  · rintro ⟨h, he⟩
    letI : Algebra K K' := j.toAlgebra
    obtain ⟨m, s, g, hg⟩ := Submodule.mem_span_set'.1 h
    choose l hl hlg using fun i => (g i).2
    have hc : ∀ t, c' t = ∑ i, (s i : K') * j (l i t) := by
      intro t
      rw [← hg, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hlg i]
      rfl
    obtain ⟨p, b, φ, hb⟩ := eigenBC_frame K K'
    have hc2 : c' = ∑ k, b k • (fun t => j ((∑ i, φ k (s i) • l i) t)) := by
      funext t
      rw [hc, Finset.sum_apply]
      have e : ∀ i, (s i : K') = ∑ k, j ((φ k (s i) : 𝓞 K) : K) * (b k : K') := by
        intro i
        have := congrArg (algebraMap (𝓞 K') K') (hb (s i))
        rw [map_sum] at this
        refine this.trans (Finset.sum_congr rfl fun k _ => ?_)
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply,
          IsScalarTower.algebraMap_apply (𝓞 K) K K']
        rfl
      rw [Finset.sum_congr rfl fun i _ => by rw [e i, Finset.sum_mul], Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      show _ = (b k : K') * j ((∑ i, φ k (s i) • l i) t)
      rw [Finset.sum_apply, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      show _ = (b k : K') * j (((φ k (s i) : 𝓞 K) : K) * l i t)
      rw [map_mul]; ring
    rw [hc2]
    refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨_, ⟨Λ.sum_mem fun i _ => Λ.smul_mem _ (hl i), fun a => ?_⟩, rfl⟩)
    funext t
    have key := eigenBC_relation s (fun i => (r a).mulVec (l i) t - τ a * l i t) (φ k) (by
      have h1 := congrFun (he a) t
      rw [← hg, Matrix.mulVec_sum, Finset.smul_sum, Finset.sum_apply, Finset.sum_apply,
        ← sub_eq_zero, ← Finset.sum_sub_distrib] at h1
      rw [← h1]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hlg i, Matrix.mulVec_smul, hmap]
      show (s i : K') * j _ = (s i : K') * j _ - j (τ a) * ((s i : K') * j (l i t))
      rw [map_sub, map_mul]; ring)
    rw [Matrix.mulVec_sum, Finset.smul_sum, Finset.sum_apply, Finset.sum_apply,
        ← sub_eq_zero, ← Finset.sum_sub_distrib, ← key]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec_smul]
    show ((φ k (s i) : 𝓞 K) : K) * _ - τ a * (((φ k (s i) : 𝓞 K) : K) * l i t) = _
    ring

end GlobalTheory.CM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EllPullExistsOAct
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section

namespace GlobalTheory.CM

theorem ellPull_exists_oAct {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {g : G'.left ⟶ G.left} (hg : IsGrpPullback G' G f g) {O : Type} [CommRing O] (o : OAct O G) :
    ∃ o' : OAct O G', ∀ a, (o'.act a).left ≫ g = g ≫ (o.act a).left := by
  have inj : ∀ {T : Over S'} {x y : T ⟶ G'}, pushPt hg.1.w x = pushPt hg.1.w y → x = y := fun {T x y} h =>
    Over.OverMorphism.ext (hg.1.hom_ext (congrArg (fun q => q.left) h) (by rw [Over.w, Over.w]))
  let act : O → (G' ⟶ G') := fun a => Over.homMk (hg.1.lift (g ≫ (o.act a).left) G'.hom
    (by rw [Category.assoc, Over.w, hg.1.w])) (hg.1.lift_snd _ _ _)
  have ha : ∀ a, (act a).left ≫ g = g ≫ (o.act a).left := fun a => hg.1.lift_fst _ _ _
  have pa : ∀ {T : Over S'} (x : T ⟶ G') a, pushPt hg.1.w (x ≫ act a) = pushPt hg.1.w x ≫ o.act a := fun x a =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, ha, Category.assoc])
  have pm : ∀ {T : Over S'} (x y : T ⟶ G'), pushPt hg.1.w (x * y) = pushPt hg.1.w x * pushPt hg.1.w y := fun x y =>
    map_mul (pushHom hg _) x y
  refine ⟨⟨act, fun a => isMonHom_of_mul _ fun T x y => inj ?_, inj ?_, fun a b => inj ?_, fun a b => inj ?_⟩, ha⟩
  · have := o.hom a
    rw [pa, pm, pm, pa, pa, MonObj.mul_comp]
  · rw [← Category.id_comp (act 1), pa, o.one, Category.comp_id]
  · rw [← Category.id_comp (act (a * b)), pa, pa, ← Category.id_comp (act a), pa, o.mul, Category.assoc]
  · refine Eq.trans ?_ (pm (act a) (act b)).symm
    rw [← Category.id_comp (act (a + b)), ← Category.id_comp (act a), ← Category.id_comp (act b), pa, pa, pa, o.add]
    exact MonObj.comp_mul _ _ _

theorem ellPull_prim {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {g : G'.left ⟶ G.left} (hg : IsGrpPullback G' G f g) {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB)
    (hL' : L'.IsLB) (i : LBIso (L.pull g) L') {w : G ⟶ G} {w' : G' ⟶ G'} (hw : w'.left ≫ g = g ≫ w.left)
    (h : LBIso L (cubeLB G ![𝟙 G, w] L)) : LBIso L' (cubeLB G' ![𝟙 G', w'] L') := by
  let U : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk g hg.1.w
  have H₁ : LBIso (L.pull g) (cubeLB G' ![𝟙 G', w'] (L.pull g)) := by
    refine LBIso.chartPull (chartPullPull L g U.left rfl)
      (chartPullLinComb L g _ _ _ U.left fun I => lamBC_psum_push hg _ _ U (fun k => ?_) I.down) h
    fin_cases k
    · refine Over.OverMorphism.ext ?_
      show 𝟙 _ ≫ g = g ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id]
    · exact Over.OverMorphism.ext hw
  have hLg : (L.pull g).IsLB := DVR.linComb_isLB _ hL _ _
  exact LBIso.trans hL' hLg (DVR.linComb_isLB _ hL' _ _) i.symm
    (LBIso.trans hLg (DVR.linComb_isLB _ hLg _ _) (DVR.linComb_isLB _ hL' _ _) H₁
      (PowPrimitive.lbIso_linComb i _ _))

theorem exists_ellMap : Out.PolBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (ω : R) (C : Ell H R ω) (R' : Type) [CommRing R'] (f : R →+* R'), ∃ (C' : Ell H R' (f ω)) (φ : C'.P.A.left ⟶ C.P.A.left), EllMap C' C f φ := by
  intro hB E _ _ _ H R _ ω C R' _ f
  obtain ⟨P', φ, hP⟩ := exists_isPolFibre hB f C.P
  obtain ⟨hdim, hg, hi⟩ := id hP
  obtain ⟨o', ho⟩ := ellPull_exists_oAct hg C.act
  have : IsCommMonObj P'.A := P'.isAb.comm
  have := C.P.smoothDim
  obtain ⟨v', hv', hv⟩ := exists_isLieBasis_baseChange R R' f C.P.A P'.A φ hg
    (SmoothOfRelativeDimension.smooth C.P.g C.P.A.hom) 1 ![C.v] C.basis
  have ev : ![v' 0] = v' := by
    funext i
    fin_cases i
    rfl
  have hv0 : (v' 0).left ≫ φ = spMap (Chart.dualMapR f) ≫ C.v.left := hv 0
  refine ⟨⟨P', hdim.trans C.dim, o', v' 0, ev ▸ hv', ?_, fun a b hab => ?_,
    ellPull_prim hg C.P.isLB P'.isLB hi (ho _) C.prim⟩, φ, rfl, hP, hv0, ho⟩
  · have e : (fun i => f (![ω] i)) = ![f ω] := by
      funext i
      fin_cases i
      rfl
    rw [ev, ← e]
    refine (lieComb_baseChange R R' f C.P.A P'.A φ hg 1 ![C.v] _ ![ω] v' _ hv C.eig).1 ?_
    show ((v' 0).left ≫ (o'.act (wK H)).left) ≫ φ = _ ≫ C.v.left ≫ (C.act.act (wK H)).left
    rw [Category.assoc, ho, ← Category.assoc, hv0, Category.assoc]
  · have e1 : (𝟙 P'.A : P'.A ⟶ P'.A).left ≫ φ = φ ≫ (𝟙 C.P.A : C.P.A ⟶ C.P.A).left := by
      show 𝟙 _ ≫ φ = φ ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id]
    exact lamEq_baseChange _ _ (spMap f) _ _ _ _ _ _ _ _ φ φ φ φ hg.1.w hg.1.w hg hg _ _ _ _ C.P.isLB C.P.isLB
      P'.isLB P'.isLB hi hi _ _ _ _ _ _ _ _ (ho a) e1 e1 (ho b) (C.adj a b hab)

end GlobalTheory.CM

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EqOfGeomPointsAlg
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

open TensorProduct in

theorem eq_of_geomPoints_alg (R K A : Type) [CommRing R] [IsDomain R] [Field K] [CharZero K]
    [Algebra R K] [IsFractionRing R K] [CommRing A] [Algebra R A] [Module.Flat R A]
    (het : (Algebra.TensorProduct.includeLeftRingHom : K →+* K ⊗[R] A).Etale) (a b : A)
    (h : ∀ (k' : Type) [Field k'] [IsAlgClosed k'] [CharZero k'] (ψ : A →+* k'), ψ a = ψ b) :
    a = b := by
  have het' : Algebra.Etale K (K ⊗[R] A) := by
    have : (algebraMap K (K ⊗[R] A)).Etale := het
    exact RingHom.etale_algebraMap.mp this
  have hred : _root_.IsReduced (K ⊗[R] A) :=
    Algebra.FormallyUnramified.isReduced_of_field K (K ⊗[R] A)
  have hinj : Function.Injective
      (Algebra.TensorProduct.includeRight : A →ₐ[R] K ⊗[R] A) :=
    Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective R K)
  apply hinj
  rw [← sub_eq_zero]
  apply IsNilpotent.eq_zero
  rw [← mem_nilradical, nilradical_eq_sInf, Ideal.mem_sInf]
  intro p hp
  have hp' : p.IsPrime := hp
  let k' := AlgebraicClosure p.ResidueField
  let χ : (K ⊗[R] A) →+* k' :=
    (algebraMap p.ResidueField k').comp (algebraMap (K ⊗[R] A) p.ResidueField)
  have : CharZero k' := by
    let : Algebra K k' := (χ.comp (algebraMap K (K ⊗[R] A))).toAlgebra
    exact charZero_of_injective_algebraMap (algebraMap K k').injective
  have h1 := h k' (χ.comp (Algebra.TensorProduct.includeRight : A →ₐ[R] K ⊗[R] A).toRingHom)
  rw [← Ideal.algebraMap_residueField_eq_zero]
  apply (algebraMap p.ResidueField k').injective
  rw [map_zero, map_sub, map_sub, sub_eq_zero]
  exact h1

theorem eq_of_geomPoints : ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K] (T : Over (Sp R)), IsFinite T.hom → Flat T.hom → Etale (pullback.snd T.hom (spMap (algebraMap R K))) → ∀ a b : Γ(T.left, ⊤), (∀ (k' : Type) [Field k'] [IsAlgClosed k'] [CharZero k'] (β : R →+* k') (t : Over.mk (spMap β) ⟶ T), t.left.appTop.hom a = t.left.appTop.hom b) → a = b := by
  intro R K _ _ _ _ _ _ T hfin hflat het a b h
  have haff : IsAffine T.left := isAffine_of_isAffineHom T.hom
  let A : CommRingCat := Γ(T.left, ⊤)
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (R := CommRingCat.of R) (S := A)
    (T.left.isoSpec.inv ≫ T.hom)
  let : Algebra R A := φ.hom.toAlgebra
  have hφ' : spMap (algebraMap R A) = T.left.isoSpec.inv ≫ T.hom := hφ
  have hfl : Module.Flat R A := by
    have : Flat (Spec.map φ) := by rw [hφ]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @Flat)).mp this
  have het2 : (Algebra.TensorProduct.includeLeftRingHom : K →+* TensorProduct R K A).Etale := by
    have h1 : Etale (pullback.fst (spMap (algebraMap R K)) (spMap (algebraMap R A))) := by
      have e : pullback.fst (spMap (algebraMap R K)) (spMap (algebraMap R A)) =
          (pullbackSymmetry _ _).hom ≫
          pullback.map _ _ T.hom (spMap (algebraMap R K)) T.left.isoSpec.inv (𝟙 _) (𝟙 _)
            (by simp [hφ']) (by simp) ≫ pullback.snd T.hom (spMap (algebraMap R K)) := by
        rw [pullback.map, pullback.lift_snd, Category.comp_id, pullbackSymmetry_hom_comp_snd]
      rw [e]
      infer_instance
    have h2 : Etale (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : K →+* TensorProduct R K A))) := by
      rw [← pullbackSpecIso_inv_fst]
      infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @Etale)).mp h2
  refine eq_of_geomPoints_alg R K A het2 a b ?_
  intro k' _ _ _ ψ
  let t : Over.mk (spMap (ψ.comp (algebraMap R A))) ⟶ T :=
    Over.homMk (spMap ψ ≫ T.left.isoSpec.inv) (by
      simp only [Over.mk_hom, Category.assoc]
      erw [← hφ', ← Spec.map_comp]
      rfl)
  have h3 := h k' _ t
  have key : ∀ x : Γ(T.left, ⊤), t.left.appTop.hom x =
      (Scheme.ΓSpecIso (CommRingCat.of k')).inv.hom (ψ x) := by
    intro x
    have e : (spMap ψ ≫ T.left.isoSpec.inv).appTop =
        CommRingCat.ofHom ψ ≫ (Scheme.ΓSpecIso (CommRingCat.of k')).inv := by
      rw [Scheme.Hom.comp_appTop, Scheme.ΓSpecIso_inv_naturality]
      congr 1
      have e2 : T.left.isoSpec.inv.appTop ≫ T.left.isoSpec.hom.appTop = 𝟙 _ := by
        rw [← Scheme.Hom.comp_appTop]; simp
      have e3 : T.left.isoSpec.hom.appTop = (Scheme.ΓSpecIso Γ(T.left, ⊤)).hom :=
        Scheme.toSpecΓ_appTop _
      rw [e3] at e2
      exact (Iso.comp_hom_eq_id _).mp e2
    exact congrArg (fun f => f.hom x) e
  rw [key, key] at h3
  exact (Scheme.ΓSpecIso (CommRingCat.of k')).symm.commRingCatIsoToRingEquiv.injective h3

end GlobalTheory.LamF
end

