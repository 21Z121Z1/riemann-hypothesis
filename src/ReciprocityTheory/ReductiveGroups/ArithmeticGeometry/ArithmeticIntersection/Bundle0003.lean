import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.LengthEqOfSurjOfKerEq
section
namespace ReciprocityTheory.ChartRestriction.G.AI

universe u

theorem length_eq_of_surj_of_ker_eq {A C M N : Type*} [CommRing A] [AddCommGroup C] [Module A C]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] (f : C →ₗ[A] M) (g : C →ₗ[A] N)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (h : LinearMap.ker f = LinearMap.ker g) : Module.length A M = Module.length A N := ((f.quotKerEquivOfSurjective hf).symm.trans ((Submodule.quotEquivOfEq _ _ h).trans
      (g.quotKerEquivOfSurjective hg))).length_eq

theorem mem_ker_lsmul_mk {A : Type u} [CommRing A] (a b x : A) :
    Ideal.Quotient.mk (Ideal.span {a}) x ∈
        LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b) ↔ ∃ y, b * x = a * y := by
  rw [LinearMap.mem_ker, LinearMap.lsmul_apply, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
    ← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  rfl

theorem length_ker_swap {A : Type u} [CommRing A] [IsDomain A] (a b : A) (ha : a ≠ 0) (hb : b ≠ 0) :
    Module.length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) =
      Module.length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {b}) a)) := by
  set S : Submodule A (A × A) :=
    LinearMap.ker (b • LinearMap.fst A A A - a • LinearMap.snd A A A) with hSdef
  have hS : ∀ p : A × A, p ∈ S ↔ b * p.1 = a * p.2 := by
    intro p
    rw [hSdef, LinearMap.mem_ker]
    simp [sub_eq_zero]
  have hf0 : ∀ p : S, (Ideal.span {a}).mkQ (p : A × A).1 ∈
      LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b) := by
    intro p
    exact (mem_ker_lsmul_mk a b _).mpr ⟨_, (hS _).mp p.2⟩
  have hg0 : ∀ p : S, (Ideal.span {b}).mkQ (p : A × A).2 ∈
      LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {b}) a) := by
    intro p
    exact (mem_ker_lsmul_mk b a _).mpr ⟨(p : A × A).1, ((hS _).mp p.2).symm⟩
  let f := LinearMap.codRestrict _
    ((Ideal.span {a}).mkQ ∘ₗ LinearMap.fst A A A ∘ₗ S.subtype) hf0
  let g := LinearMap.codRestrict _
    ((Ideal.span {b}).mkQ ∘ₗ LinearMap.snd A A A ∘ₗ S.subtype) hg0
  apply length_eq_of_surj_of_ker_eq f g
  · rintro ⟨k, hk⟩
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective k
    obtain ⟨y, hy⟩ := (mem_ker_lsmul_mk a b x).mp hk
    exact ⟨⟨(x, y), (hS _).mpr hy⟩, rfl⟩
  · rintro ⟨k, hk⟩
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective k
    obtain ⟨x, hx⟩ := (mem_ker_lsmul_mk b a y).mp hk
    exact ⟨⟨(x, y), (hS _).mpr hx.symm⟩, rfl⟩
  · ext ⟨⟨x, y⟩, hp⟩
    have hp' := (hS _).mp hp
    rw [LinearMap.mem_ker, LinearMap.mem_ker, ← Submodule.coe_eq_zero, ← Submodule.coe_eq_zero]
    show (Ideal.span {a}).mkQ x = 0 ↔ (Ideal.span {b}).mkQ y = 0
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton, Ideal.mem_span_singleton]
    simp only at hp'
    constructor
    · rintro ⟨z, rfl⟩
      refine ⟨z, ?_⟩
      apply mul_left_cancel₀ ha
      rw [← hp']
      ring
    · rintro ⟨w, rfl⟩
      refine ⟨w, ?_⟩
      apply mul_left_cancel₀ hb
      rw [hp']
      ring

theorem length_ne_top_of_killed {A N : Type*} [CommRing A] [AddCommGroup N] [Module A N]
    [Module.Finite A N] (I : Ideal A) (hI : ∀ r ∈ I, ∀ x : N, r • x = 0)
    (hfin : Module.length A (A ⧸ I) ≠ ⊤) : Module.length A N ≠ ⊤ := by
  rw [Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian] at hfin ⊢
  obtain ⟨hN, hA⟩ := hfin
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := N)
  let φ : Fin n → (A ⧸ I) →ₗ[A] N := fun i =>
    Submodule.liftQ I (LinearMap.toSpanSingleton A N (s i)) (by
      intro r hr
      rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
      exact hI r hr (s i))
  let Φ : (Fin n → A ⧸ I) →ₗ[A] N := ∑ i, (φ i).comp (LinearMap.proj i)
  have hΦ : Function.Surjective Φ := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hs, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨Pi.single i (Submodule.Quotient.mk 1), ?_⟩
    simp only [Φ, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    rw [Finset.sum_eq_single i]
    · rw [Pi.single_eq_same]
      simp only [φ, Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply, one_smul]
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp
  exact ⟨isNoetherian_of_surjective Φ (LinearMap.range_eq_top.mpr hΦ),
    isArtinian_of_surjective _ Φ hΦ⟩

theorem length_ker_ne_top {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] (a b : A)
    (ha : a ≠ 0) (hb : b ≠ 0) (hfin : Module.length A (A ⧸ Ideal.span {a, b}) ≠ ⊤) :
    Module.length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) ≠ ⊤ := by
  apply length_ne_top_of_killed (Ideal.span {a, b}) _ hfin
  rintro r hr ⟨k, hk⟩
  apply Subtype.ext
  simp only [Submodule.coe_smul, Submodule.coe_zero]
  obtain ⟨u, v, rfl⟩ := Ideal.mem_span_pair.mp hr
  have hbk : b • k = 0 := by simpa using hk
  have hak : a • k = 0 := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective k
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self a)
  rw [add_smul, mul_smul, mul_smul, hak, hbk, smul_zero, smul_zero, add_zero]

end ReciprocityTheory.ChartRestriction.G.AI
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.LengthEqRangeAddRange
section
namespace ReciprocityTheory.ChartRestriction.G.AI

open Module

theorem length_eq_ker_add_range {A : Type*} [Ring A] {M N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (φ : M →ₗ[A] N) :
    length A M = length A (LinearMap.ker φ) + length A (LinearMap.range φ) := by
  exact Module.length_eq_add_of_exact (LinearMap.ker φ).subtype φ.rangeRestrict
    (Submodule.injective_subtype _) φ.surjective_rangeRestrict
    (by rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype])

theorem length_eq_sub_add_quot {A : Type*} [Ring A] {M : Type*} [AddCommGroup M] [Module A M]
    (P : Submodule A M) : length A M = length A P + length A (M ⧸ P) :=
  Module.length_eq_add_of_exact P.subtype P.mkQ (Submodule.injective_subtype _) (Submodule.mkQ_surjective _)
    (LinearMap.exact_subtype_mkQ P)

theorem length_eq_range_add_range {A : Type*} [Ring A] {L M N : Type*}
    [AddCommGroup L] [Module A L] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] {ψ : L →ₗ[A] M} {φ : M →ₗ[A] N} (h : Function.Exact ψ φ) :
    length A M = length A (LinearMap.range ψ) + length A (LinearMap.range φ) := by
  rw [length_eq_ker_add_range φ, h.linearMap_ker_eq]

theorem length_six_term {A : Type*} [Ring A] {M₁ M₂ M₃ M₄ M₅ M₆ : Type*}
    [AddCommGroup M₁] [Module A M₁] [AddCommGroup M₂] [Module A M₂]
    [AddCommGroup M₃] [Module A M₃] [AddCommGroup M₄] [Module A M₄]
    [AddCommGroup M₅] [Module A M₅] [AddCommGroup M₆] [Module A M₆]
    {f₁ : M₁ →ₗ[A] M₂} {f₂ : M₂ →ₗ[A] M₃} {f₃ : M₃ →ₗ[A] M₄} {f₄ : M₄ →ₗ[A] M₅}
    {f₅ : M₅ →ₗ[A] M₆} (h₁ : Function.Injective f₁) (h₂ : Function.Exact f₁ f₂)
    (h₃ : Function.Exact f₂ f₃) (h₄ : Function.Exact f₃ f₄) (h₅ : Function.Exact f₄ f₅)
    (h₆ : Function.Surjective f₅) :
    length A M₁ + length A M₃ + length A M₅ = length A M₂ + length A M₄ + length A M₆ := by
  have e1 : length A M₁ = length A (LinearMap.range f₁) := (LinearEquiv.ofInjective f₁ h₁).length_eq
  have e6 : length A (LinearMap.range f₅) = length A M₆ :=
    (LinearEquiv.ofTop _ (LinearMap.range_eq_top.2 h₆)).length_eq
  rw [e1, length_eq_range_add_range h₂, length_eq_range_add_range h₃, length_eq_range_add_range h₄,
    length_eq_range_add_range h₅, ← e6]
  ring

def kerSmulMap {A : Type*} [CommRing A] {M N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (f : M →ₗ[A] N) (x : A) :
    LinearMap.ker (LinearMap.lsmul A M x) →ₗ[A] LinearMap.ker (LinearMap.lsmul A N x) :=
  f.restrict (fun m hm => by
    rw [LinearMap.mem_ker, LinearMap.lsmul_apply] at hm ⊢
    rw [← map_smul, hm, map_zero])

def cokerSmulMap {A : Type*} [CommRing A] {M N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (f : M →ₗ[A] N) (x : A) :
    (M ⧸ LinearMap.range (LinearMap.lsmul A M x)) →ₗ[A]
      (N ⧸ LinearMap.range (LinearMap.lsmul A N x)) :=
  Submodule.mapQ _ _ f (by
    rintro _ ⟨m, rfl⟩
    exact ⟨f m, by simp⟩)

theorem euler_ses {A : Type*} [CommRing A] {M' M M'' : Type*} [AddCommGroup M'] [Module A M']
    [AddCommGroup M] [Module A M] [AddCommGroup M''] [Module A M'']
    (f : M' →ₗ[A] M) (g : M →ₗ[A] M'') (hf : Function.Injective f) (hg : Function.Surjective g)
    (hex : Function.Exact f g) (x : A) :
    length A (LinearMap.ker (LinearMap.lsmul A M' x)) + length A (LinearMap.ker (LinearMap.lsmul A M'' x)) +
        length A (M ⧸ LinearMap.range (LinearMap.lsmul A M x)) =
      length A (LinearMap.ker (LinearMap.lsmul A M x)) +
        length A (M' ⧸ LinearMap.range (LinearMap.lsmul A M' x)) +
        length A (M'' ⧸ LinearMap.range (LinearMap.lsmul A M'' x)) := by
  have key : ∀ z : LinearMap.ker (LinearMap.lsmul A M'' x), ∃ (m : M) (m' : M'),
      g m = (z : M'') ∧ f m' = x • m := by
    intro z
    obtain ⟨m, hm⟩ := hg z
    have hz : x • (z : M'') = 0 := z.2
    obtain ⟨m', hm'⟩ := (hex (x • m)).1 (by rw [map_smul, hm, hz])
    exact ⟨m, m', hm, hm'⟩
  have indep : ∀ (m₁ : M) (m₁' : M') (m₂ : M) (m₂' : M'), g m₁ = g m₂ → f m₁' = x • m₁ →
      f m₂' = x • m₂ →
      Submodule.mkQ (LinearMap.range (LinearMap.lsmul A M' x)) m₁' =
        Submodule.mkQ (LinearMap.range (LinearMap.lsmul A M' x)) m₂' := by
    intro m₁ m₁' m₂ m₂' h h1 h2
    obtain ⟨n, hn⟩ := (hex (m₁ - m₂)).1 (by rw [map_sub, h, sub_self])
    have e : m₁' - m₂' = x • n := hf (by rw [map_sub, map_smul, hn, h1, h2, smul_sub])
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, e]
    exact ⟨n, rfl⟩
  choose lift liftP hlift using key
  obtain ⟨δ, hδ⟩ : ∃ δ : LinearMap.ker (LinearMap.lsmul A M'' x) →ₗ[A]
      (M' ⧸ LinearMap.range (LinearMap.lsmul A M' x)),
      ∀ (z : LinearMap.ker (LinearMap.lsmul A M'' x)) (m : M) (m' : M'), g m = (z : M'') → f m' = x • m →
        δ z = Submodule.mkQ (LinearMap.range (LinearMap.lsmul A M' x)) m' := by
    refine ⟨{ toFun := fun z => Submodule.mkQ (LinearMap.range (LinearMap.lsmul A M' x)) (liftP z),
              map_add' := ?_, map_smul' := ?_ }, ?_⟩
    · intro z₁ z₂
      show Submodule.mkQ _ (liftP (z₁ + z₂)) = Submodule.mkQ _ (liftP z₁) + Submodule.mkQ _ (liftP z₂)
      rw [← map_add]
      exact indep _ _ (lift z₁ + lift z₂) _
        (by rw [(hlift _).1, map_add, (hlift z₁).1, (hlift z₂).1, Submodule.coe_add]) (hlift _).2
        (by rw [map_add, (hlift z₁).2, (hlift z₂).2, smul_add])
    · intro a z
      show Submodule.mkQ _ (liftP (a • z)) = a • Submodule.mkQ _ (liftP z)
      rw [← map_smul]
      exact indep _ _ (a • lift z) _
        (by rw [(hlift _).1, map_smul, (hlift z).1, Submodule.coe_smul]) (hlift _).2
        (by rw [map_smul, (hlift z).2, smul_comm])
    · intro z m m' h h'
      exact indep _ _ m m' (by rw [(hlift z).1, h]) (hlift z).2 h'
  have h₁ : Function.Injective (kerSmulMap f x) := by
    intro a b h
    apply Subtype.ext
    apply hf
    exact congrArg Subtype.val h
  have h₂ : Function.Exact (kerSmulMap f x) (kerSmulMap g x) := by
    intro y
    constructor
    · intro hy
      have hy0 : g y = 0 := congrArg Subtype.val hy
      obtain ⟨m', hm'⟩ := (hex y).1 hy0
      have hyx : x • (y : M) = 0 := y.2
      refine ⟨⟨m', ?_⟩, Subtype.ext hm'⟩
      show x • m' = 0
      apply hf
      rw [map_smul, hm', hyx, map_zero]
    · rintro ⟨w, rfl⟩
      apply Subtype.ext
      exact (hex _).2 ⟨w, rfl⟩
  have h₃ : Function.Exact (kerSmulMap g x) δ := by
    intro z
    constructor
    · intro hz
      obtain ⟨m, hm⟩ := hg z
      have hzx : x • (z : M'') = 0 := z.2
      obtain ⟨m', hm'⟩ := (hex (x • m)).1 (by rw [map_smul, hm, hzx])
      rw [hδ z m m' hm hm', Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hz
      obtain ⟨n, hn⟩ := LinearMap.mem_range.1 hz
      have hn' : x • n = m' := hn
      refine ⟨⟨m - f n, ?_⟩, Subtype.ext ?_⟩
      · show x • (m - f n) = 0
        rw [smul_sub, ← map_smul, hn', hm', sub_self]
      · show g (m - f n) = z
        rw [map_sub, hm, (hex _).2 ⟨n, rfl⟩, sub_zero]
    · rintro ⟨y, rfl⟩
      have hyx : x • (y : M) = 0 := y.2
      rw [hδ _ y 0 rfl (by rw [map_zero, hyx]), map_zero]
  have h₄ : Function.Exact δ (cokerSmulMap f x) := by
    intro w
    obtain ⟨m', rfl⟩ := Submodule.mkQ_surjective _ w
    constructor
    · intro hw
      have hw' : Submodule.mkQ (LinearMap.range (LinearMap.lsmul A M x)) (f m') = 0 := hw
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hw'
      obtain ⟨m, hm⟩ := LinearMap.mem_range.1 hw'
      have hm2 : x • m = f m' := hm
      refine ⟨⟨g m, ?_⟩, hδ _ m m' rfl hm2.symm⟩
      show x • g m = 0
      rw [← map_smul, hm2]
      exact (hex _).2 ⟨m', rfl⟩
    · rintro ⟨z, hz⟩
      obtain ⟨m, hm⟩ := hg z
      have hzx : x • (z : M'') = 0 := z.2
      obtain ⟨n', hn'⟩ := (hex (x • m)).1 (by rw [map_smul, hm, hzx])
      rw [← hz, hδ z m n' hm hn']
      show Submodule.mkQ (LinearMap.range (LinearMap.lsmul A M x)) (f n') = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hn']
      exact ⟨m, rfl⟩
  have h₅ : Function.Exact (cokerSmulMap f x) (cokerSmulMap g x) := by
    intro w
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ w
    constructor
    · intro hw
      have hw' : Submodule.mkQ (LinearMap.range (LinearMap.lsmul A M'' x)) (g m) = 0 := hw
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hw'
      obtain ⟨m'', hm''⟩ := LinearMap.mem_range.1 hw'
      have hm2 : x • m'' = g m := hm''
      obtain ⟨t, ht⟩ := hg m''
      obtain ⟨m', hm'⟩ := (hex (m - x • t)).1 (by rw [map_sub, map_smul, ht, hm2, sub_self])
      refine ⟨Submodule.mkQ _ m', ?_⟩
      show Submodule.mkQ (LinearMap.range (LinearMap.lsmul A M x)) (f m') = Submodule.mkQ _ m
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, hm']
      refine ⟨-t, ?_⟩
      show x • -t = m - x • t - m
      rw [smul_neg]
      abel
    · rintro ⟨w', hw'⟩
      obtain ⟨m', rfl⟩ := Submodule.mkQ_surjective _ w'
      rw [← hw']
      show Submodule.mkQ (LinearMap.range (LinearMap.lsmul A M'' x)) (g (f m')) = 0
      rw [(hex _).2 ⟨m', rfl⟩, map_zero]
  have h₆ : Function.Surjective (cokerSmulMap g x) := by
    intro w
    obtain ⟨m'', rfl⟩ := Submodule.mkQ_surjective _ w
    obtain ⟨m, rfl⟩ := hg m''
    exact ⟨Submodule.mkQ _ m, rfl⟩
  exact length_six_term h₁ h₂ h₃ h₄ h₅ h₆

theorem euler_finLength {A : Type*} [CommRing A] {N : Type*} [AddCommGroup N] [Module A N]
    (hN : length A N ≠ ⊤) (x : A) :
    length A (N ⧸ LinearMap.range (LinearMap.lsmul A N x)) =
      length A (LinearMap.ker (LinearMap.lsmul A N x)) := by
  have h1 := length_eq_ker_add_range (LinearMap.lsmul A N x)
  have h2 := length_eq_sub_add_quot (LinearMap.range (LinearMap.lsmul A N x))
  have hle : length A (LinearMap.range (LinearMap.lsmul A N x)) ≤ length A N := by
    rw [h1]
    exact le_add_self
  have hR := ne_top_of_le_ne_top hN hle
  rw [h1, add_comm] at h2
  exact (WithTop.add_left_cancel hR h2).symm

end ReciprocityTheory.ChartRestriction.G.AI
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.SymExp
section
namespace ReciprocityTheory.ChartRestriction.G.AI

theorem symm_eq_of_card {V : Type*} [AddCommGroup V] [Module ℝ V] [DecidableEq V] {n : ℕ}
    (I : MultilinearMap ℝ (fun _ : Fin n => V) ℝ) (hI : IsSymmForm I) (v w : Fin n → V)
    (h : ∀ x : V, (Finset.univ.filter fun i => v i = x).card = (Finset.univ.filter fun i => w i = x).card) :
    I v = I w := by
  have e : ∀ c : V, {a // w a = c} ≃ {b // v b = c} := fun c =>
    Fintype.equivOfCardEq (by rw [Fintype.card_subtype, Fintype.card_subtype]; exact (h c).symm)
  have hσ : v ∘ (Equiv.ofFiberEquiv e) = w := funext fun i => Equiv.ofFiberEquiv_map e i
  rw [← hσ, hI]

theorem symm_piecewise_eq {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (I : MultilinearMap ℝ (fun _ : Fin n => V) ℝ) (hI : IsSymmForm I) (x y : V) (s t : Finset (Fin n))
    (hst : s.card = t.card) :
    I (s.piecewise (fun _ => x) fun _ => y) = I (t.piecewise (fun _ => x) fun _ => y) := by
  classical
  have e : ∀ c : Bool, {a // decide (a ∈ t) = c} ≃ {b // decide (b ∈ s) = c} := fun c =>
    Fintype.equivOfCardEq (by
      rw [Fintype.card_subtype, Fintype.card_subtype]
      cases c
      · have h1 : (Finset.univ.filter fun a => decide (a ∈ t) = false) = tᶜ := by ext; simp
        have h2 : (Finset.univ.filter fun b => decide (b ∈ s) = false) = sᶜ := by ext; simp
        rw [h1, h2, Finset.card_compl, Finset.card_compl, hst]
      · have h1 : (Finset.univ.filter fun a => decide (a ∈ t) = true) = t := by ext; simp
        have h2 : (Finset.univ.filter fun b => decide (b ∈ s) = true) = s := by ext; simp
        rw [h1, h2, hst])
  have hσ : ∀ i, (Equiv.ofFiberEquiv e i ∈ s ↔ i ∈ t) := fun i => by
    have := Equiv.ofFiberEquiv_map e i
    rw [← decide_eq_decide]
    exact this
  have hfun : (s.piecewise (fun _ => x) fun _ => y) ∘ (Equiv.ofFiberEquiv e) =
      t.piecewise (fun _ => x) fun _ => y := by
    funext i
    rw [Function.comp_apply]
    by_cases hi : i ∈ t
    · rw [Finset.piecewise_eq_of_mem _ _ _ hi, Finset.piecewise_eq_of_mem _ _ _ ((hσ i).2 hi)]
    · have hi' : Equiv.ofFiberEquiv e i ∉ s := fun h => hi ((hσ i).1 h)
      first
        | rw [Finset.piecewise_eq_of_notMem _ _ _ hi, Finset.piecewise_eq_of_notMem _ _ _ hi']
        | rw [Finset.piecewise_eq_of_not_mem _ _ _ hi, Finset.piecewise_eq_of_not_mem _ _ _ hi']
  rw [← hfun, hI]

theorem symm_piecewise_eq_mix {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (I : MultilinearMap ℝ (fun _ : Fin n => V) ℝ) (hI : IsSymmForm I) (x y : V) (s : Finset (Fin n)) :
    I (s.piecewise (fun _ => x) fun _ => y) = I (mix s.card x y) := by
  classical
  set t : Finset (Fin n) := Finset.univ.filter fun i : Fin n => (i : ℕ) < s.card with ht_def
  have ht : t.card = s.card := by
    have hle : s.card ≤ n := by simpa using Finset.card_le_univ s
    have hmap : t.map Fin.valEmbedding = Finset.range s.card := by
      ext m
      simp only [ht_def, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
        Finset.mem_range]
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact hi
      · intro hm
        exact ⟨⟨m, by omega⟩, hm, rfl⟩
    rw [← Finset.card_map Fin.valEmbedding, hmap, Finset.card_range]
  rw [symm_piecewise_eq I hI x y s t ht.symm]
  congr 1
  funext i
  simp [ht_def, mix, Finset.piecewise]

theorem symm_expand {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (I : MultilinearMap ℝ (fun _ : Fin n => V) ℝ) (hI : IsSymmForm I) (x y : V) (c : ℝ) :
    I (fun _ => y + c • x) =
      ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * c ^ j * I (mix j x y) := by
  classical
  have h1 : (fun _ : Fin n => y + c • x) = (fun _ => c • x) + (fun _ => y) := by
    funext i
    simp [add_comm]
  rw [h1, MultilinearMap.map_add_univ]
  have h2 : ∀ s : Finset (Fin n),
      I (s.piecewise (fun _ => c • x) fun _ => y) = c ^ s.card * I (mix s.card x y) := by
    intro s
    have h3 : (s.piecewise (fun _ => c • x) fun _ => y) =
        s.piecewise (fun i => c • (s.piecewise (fun _ => x) (fun _ => y)) i)
          (s.piecewise (fun _ => x) fun _ => y) := by
      funext i
      by_cases hi : i ∈ s <;> simp [Finset.piecewise, hi]
    rw [h3, MultilinearMap.map_piecewise_smul, symm_piecewise_eq_mix I hI, Finset.prod_const, smul_eq_mul]
  simp only [h2]
  have h4 := Finset.sum_powerset_apply_card (f := fun k => c ^ k * I (mix k x y))
    (x := (Finset.univ : Finset (Fin n)))
  rw [Finset.powerset_univ, Finset.card_univ, Fintype.card_fin] at h4
  rw [h4]
  simp only [nsmul_eq_mul, mul_assoc]

end ReciprocityTheory.ChartRestriction.G.AI
end

