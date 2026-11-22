import Mathlib

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.KaehlerBasisTower
section
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.KaehlerTower

theorem append_of_shortExact {A M₁ M₂ M₃ : Type*} [CommRing A]
    [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
    [Module A M₁] [Module A M₂] [Module A M₃]
    (f : M₁ →ₗ[A] M₂) (g : M₂ →ₗ[A] M₃) (hf : Function.Injective f)
    (hfg : Function.Exact f g) {e m : ℕ} (u : Fin e → M₁) (w : Fin m → M₂)
    (hu : LinearIndependent A u) (hus : Submodule.span A (Set.range u) = ⊤)
    (hw : LinearIndependent A (fun i => g (w i)))
    (hws : Submodule.span A (Set.range fun i => g (w i)) = ⊤) :
    LinearIndependent A (Fin.append (fun i => f (u i)) w) ∧
      Submodule.span A (Set.range (Fin.append (fun i => f (u i)) w)) = ⊤ := by
  have happ : Fin.append (fun i => f (u i)) w =
      Sum.elim (fun i => f (u i)) w ∘ finSumFinEquiv.symm := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp
    · simp
  have hfu : LinearIndependent A (fun i => f (u i)) :=
    hu.map' f (LinearMap.ker_eq_bot.mpr hf)
  have hw' : LinearIndependent A w := LinearIndependent.of_comp g hw
  have hcomp : ∀ y, g (f y) = 0 := fun y => (hfg (f y)).mpr ⟨y, rfl⟩
  have hdisj : Disjoint (Submodule.span A (Set.range fun i => f (u i)))
      (Submodule.span A (Set.range w)) := by
    rw [Submodule.disjoint_def]
    intro x hx hx'
    have hgx : g x = 0 := by
      have hle : Submodule.span A (Set.range fun i => f (u i)) ≤ LinearMap.ker g := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact hcomp _
      exact hle hx
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp hx'
    have h0 : ∑ i, c i • g (w i) = 0 := by simpa [map_sum] using hgx
    have hc := (Fintype.linearIndependent_iff.mp hw) c h0
    simp [hc]
  constructor
  · rw [happ]
    exact (hfu.sum_type hw' hdisj).comp _ finSumFinEquiv.symm.injective
  · rw [happ, Set.range_comp, finSumFinEquiv.symm.surjective.range_eq, Set.image_univ,
      Set.Sum.elim_range, Submodule.span_union, eq_top_iff]
    intro x _
    have hgx : g x ∈ Submodule.span A (Set.range fun i => g (w i)) := hws ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp hgx
    have hker : g (x - ∑ i, c i • w i) = 0 := by
      simp [map_sum, hc]
    obtain ⟨y, hy⟩ := (hfg _).mp hker
    have hy' : y ∈ Submodule.span A (Set.range u) := hus ▸ Submodule.mem_top
    have hfy : f y ∈ Submodule.span A (Set.range fun i => f (u i)) := by
      have := Submodule.mem_map_of_mem (f := f) hy'
      rwa [Submodule.map_span, ← Set.range_comp] at this
    have hsum : ∑ i, c i • w i ∈ Submodule.span A (Set.range w) :=
      Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have hx : x = f y + ∑ i, c i • w i := by rw [hy]; abel
    rw [hx]
    exact Submodule.add_mem_sup hfy hsum

theorem kaehler_basis_tower : ∀ (R S T : Type) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] [Algebra.FormallySmooth S T] (e m : ℕ) (z : Fin e → S) (w : Fin m → T),
    LinearIndependent S (fun i => KaehlerDifferential.D R S (z i)) →
    Submodule.span S (Set.range fun i => KaehlerDifferential.D R S (z i)) = ⊤ →
    LinearIndependent T (fun i => KaehlerDifferential.D S T (w i)) →
    Submodule.span T (Set.range fun i => KaehlerDifferential.D S T (w i)) = ⊤ →
    LinearIndependent T (fun i => KaehlerDifferential.D R T (Fin.append (fun i => algebraMap S T (z i)) w i)) ∧
    Submodule.span T (Set.range fun i => KaehlerDifferential.D R T (Fin.append (fun i => algebraMap S T (z i)) w i)) = ⊤ := by
  intro R S T _ _ _ _ _ _ _ _ e m z w hz hzs hw hws
  have hinj : Function.Injective (KaehlerDifferential.mapBaseChange R S T) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange R S T x).mp hx
    have : Subsingleton (Algebra.H1Cotangent S T) :=
      Algebra.FormallySmooth.subsingleton_h1Cotangent
    rw [Subsingleton.elim y 0, map_zero]
  have hex : Function.Exact (KaehlerDifferential.mapBaseChange R S T)
      (KaehlerDifferential.map R S T T) := KaehlerDifferential.exact_mapBaseChange_map R S T
  let b : Module.Basis (Fin e) S (Ω[S⁄R]) := Module.Basis.mk hz hzs.ge
  let bT := Algebra.TensorProduct.basis T b
  have hb : ∀ i, bT i = (1 : T) ⊗ₜ[S] KaehlerDifferential.D R S (z i) := by
    intro i
    simp [bT, b]
  have hmain := append_of_shortExact (KaehlerDifferential.mapBaseChange R S T)
    (KaehlerDifferential.map R S T T) hinj hex (fun i => bT i)
    (fun i => KaehlerDifferential.D R T (w i)) bT.linearIndependent bT.span_eq
    (by simpa [KaehlerDifferential.map_D] using hw)
    (by simpa [KaehlerDifferential.map_D] using hws)
  have hfun : (fun i => KaehlerDifferential.D R T (Fin.append (fun i => algebraMap S T (z i)) w i)) =
      Fin.append (fun i => KaehlerDifferential.mapBaseChange R S T (bT i))
        (fun i => KaehlerDifferential.D R T (w i)) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [hb, KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D]
    · simp
  rw [hfun]
  exact hmain

end GlobalTheory.CompanionTheory.KaehlerTower
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.KaehlerDifferentialsSpanLocal
section
open MvPolynomial

namespace GlobalTheory.CompanionTheory.Kaehler

theorem derivation_mem_span {S B M : Type} [CommRing S] [Algebra ℚ S] [CommRing B]
    [AddCommGroup M] [Module B M] (ψ : S →+* B) (D₀ : S →+ M)
    (leib : ∀ a b, D₀ (a * b) = ψ a • D₀ b + ψ b • D₀ a)
    {n : ℕ} (z : Fin n → S)
    (hz : Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤) (s : S) :
    D₀ s ∈ Submodule.span B (Set.range fun i => D₀ (z i)) := by
  let _ : Module S M := Module.compHom M ψ
  let _ : Module ℚ M := Module.compHom M (algebraMap ℚ S)
  have : IsScalarTower ℚ S M := ⟨fun q a x => by
    change ψ (q • a) • x = ψ (algebraMap ℚ S q) • (ψ a • x)
    rw [Algebra.smul_def, map_mul, mul_smul]⟩
  have hsm : ∀ (a : S) (x : M), a • x = ψ a • x := fun _ _ => rfl
  let D : Derivation ℚ S M := Derivation.mk' D₀.toRatLinearMap (fun a b => by
    simpa [hsm] using leib a b)
  have hD : ∀ a, D a = D₀ a := fun _ => rfl
  let L := D.liftKaehlerDifferential
  have hL : ∀ a, L (KaehlerDifferential.D ℚ S a) = D₀ a := fun a => by
    simp [L, hD]
  have key : ∀ x : Ω[S⁄ℚ], L x ∈ Submodule.span B (Set.range fun i => D₀ (z i)) := by
    intro x
    have hx : x ∈ Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) := by
      rw [hz]; trivial
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      rw [hL]
      exact Submodule.subset_span ⟨i, rfl⟩
    | zero => simp
    | add y w _ _ hy hw => rw [map_add]; exact add_mem hy hw
    | smul a y _ hy =>
      rw [map_smul, hsm]
      exact Submodule.smul_mem _ _ hy
  simpa [hL] using key (KaehlerDifferential.D ℚ S s)

theorem maximalIdeal_eq_span_of_span_D :
    ∀ (S B : Type) [CommRing S] [Algebra ℚ S] [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] [Algebra ℂ B] (ψ : S →+* B) (φ : S →+* ℂ),
    (∀ s, ψ s - algebraMap ℂ B (φ s) ∈ IsLocalRing.maximalIdeal B) →
    ∀ (T : Set S), IsLocalRing.maximalIdeal B = Ideal.span ((fun s => ψ s - algebraMap ℂ B (φ s)) '' T) →
    ∀ (n : ℕ) (z : Fin n → S),
    Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤ →
    IsLocalRing.maximalIdeal B = Ideal.span (Set.range fun i => ψ (z i) - algebraMap ℂ B (φ (z i))) := by
  intro S B _ _ _ _ _ _ ψ φ hmem T hT n z hz
  set m := IsLocalRing.maximalIdeal B with hm
  set f : S → B := fun s => ψ s - algebraMap ℂ B (φ s) with hf
  set J : Ideal B := Ideal.span (Set.range fun i => f (z i)) with hJ
  have hJm : J ≤ m := by
    rw [hJ, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hmem (z i)
  let D₀ : S →+ m.Cotangent :=
    { toFun := fun s => m.toCotangent ⟨f s, hmem s⟩
      map_zero' := by
        have : (⟨f 0, hmem 0⟩ : m) = 0 := by ext; simp [hf]
        rw [this, map_zero]
      map_add' := fun a b => by
        rw [← map_add]
        congr 1
        ext
        simp [hf]
        ring }
  have hD₀ : ∀ s, D₀ s = m.toCotangent ⟨f s, hmem s⟩ := fun _ => rfl
  have leib : ∀ a b, D₀ (a * b) = ψ a • D₀ b + ψ b • D₀ a := by
    intro a b
    rw [hD₀, hD₀, hD₀, ← map_smul, ← map_smul, ← map_add, Ideal.toCotangent_eq]
    have h2 : f a * f b ∈ m ^ 2 := by
      rw [pow_two]; exact Ideal.mul_mem_mul (hmem a) (hmem b)
    have : ((⟨f (a * b), hmem (a * b)⟩ : m) : B)
        - ((ψ a • (⟨f b, hmem b⟩ : m) + ψ b • (⟨f a, hmem a⟩ : m) : m) : B) = -(f a * f b) := by
      simp [hf]
      ring
    rw [this]
    exact (m ^ 2).neg_mem h2
  have hspan : ∀ s, D₀ s ∈ Submodule.span B (Set.range fun i => D₀ (z i)) :=
    derivation_mem_span ψ D₀ leib z hz
  let Q : Submodule B m.Cotangent := Submodule.map m.toCotangent (Submodule.comap m.subtype J)
  have hPQ : Submodule.span B (Set.range fun i => D₀ (z i)) ≤ Q := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨⟨f (z i), hmem (z i)⟩, Ideal.subset_span ⟨i, rfl⟩, rfl⟩
  have hfs : ∀ s, f s ∈ J ⊔ m • m := by
    intro s
    obtain ⟨y, hyJ, hy⟩ := hPQ (hspan s)
    have hy' := (Ideal.toCotangent_eq (I := m)).1 (hy.trans (hD₀ s))
    have hsub : f s = (y : B) - ((y : B) - f s) := by ring
    rw [hsub]
    refine Submodule.sub_mem _ (Submodule.mem_sup_left hyJ) (Submodule.mem_sup_right ?_)
    simpa [pow_two] using hy'
  have hle : m ≤ J ⊔ m • m := by
    conv_lhs => rw [hT]
    rw [Ideal.span_le]
    rintro _ ⟨s, _, rfl⟩
    exact hfs s
  apply le_antisymm _ hJm
  exact Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian m)
    (IsLocalRing.maximalIdeal_le_jacobson _) hle

end GlobalTheory.CompanionTheory.Kaehler
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LinIndepDescent
section
open Matrix

namespace GlobalTheory.CompanionTheory.Arith.DedekindDescent

theorem single_ext (F K : Type) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    (σ : F →+* ℂ) {κ : Type} [Fintype κ] (b : κ → ℂ)
    (hb : ∀ c : κ → F, ∑ k, σ (c k) * b k = 0 → c = 0) (x : κ → K)
    (h : ∀ τ : K →+* ℂ, τ.comp (algebraMap F K) = σ → ∑ k, b k * τ (x k) = 0) : x = 0 := by
  let _ : Algebra F ℂ := σ.toAlgebra
  have : CharZero F := ⟨fun a b hab => Nat.cast_injective (R := ℂ) (by
    have := congrArg σ hab
    simpa only [map_natCast] using this)⟩
  have key : ∀ y : K, ∑ k, σ (Algebra.trace F K (x k * y)) * b k = 0 := by
    intro y
    have htr : ∀ k, σ (Algebra.trace F K (x k * y)) = ∑ φ : K →ₐ[F] ℂ, φ (x k * y) :=
      fun k => trace_eq_sum_embeddings ℂ (x := x k * y)
    simp only [htr, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun φ _ => ?_
    have hφ := h (φ : K →+* ℂ) φ.comp_algebraMap
    have hsplit : ∑ k, φ (x k * y) * b k = φ y * ∑ k, b k * (φ : K →+* ℂ) (x k) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, AlgHom.coe_toRingHom]
      ring
    rw [hsplit, hφ, mul_zero]
  funext k0
  by_contra hne
  have h0 := congrFun (hb _ (key (x k0)⁻¹)) k0
  simp only [Pi.zero_apply] at h0 hne
  rw [mul_inv_cancel₀ hne, ← map_one (algebraMap F K), Algebra.trace_algebraMap, nsmul_eq_mul,
    mul_one, Nat.cast_eq_zero] at h0
  exact (Module.finrank_pos (R := F) (M := K)).ne' h0

theorem linIndep_descent : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (J : Type) (K : J → Type) [∀ j, Field (K j)] [∀ j, Algebra F (K j)] [∀ j, FiniteDimensional F (K j)] (ι : Type) [Fintype ι] (v : ι → ∀ j, K j), (∀ a : ι → F, (∀ j, ∑ l, algebraMap F (K j) (a l) * v l j = 0) → a = 0) → ∀ d : ι → ℂ, (∀ j (τ : K j →+* ℂ), τ.comp (algebraMap F (K j)) = σ → ∑ l, d l * τ (v l j) = 0) → d = 0 := by
  intro F _ σ J K _ _ _ ι _ v hv d hd
  let _ : Algebra F ℂ := σ.toAlgebra
  let S := Submodule.span F (Set.range d)
  have : FiniteDimensional F S := FiniteDimensional.span_of_finite F (Set.finite_range d)
  let B := Module.finBasis F S
  have hmem : ∀ l, d l ∈ S := fun l => Submodule.subset_span ⟨l, rfl⟩
  have hval : ∀ e : Fin (Module.finrank F S) → F,
      ((∑ k, e k • B k : S) : ℂ) = ∑ k, σ (e k) * (B k : ℂ) := by
    intro e
    simp only [AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul, Algebra.smul_def,
      RingHom.algebraMap_toAlgebra]
  have hdc : ∀ l, d l = ∑ k, σ (B.repr ⟨d l, hmem l⟩ k) * (B k : ℂ) := by
    intro l
    rw [← hval]
    exact (congrArg Subtype.val (B.sum_repr ⟨d l, hmem l⟩)).symm
  have hbind : ∀ e : Fin (Module.finrank F S) → F, ∑ k, σ (e k) * (B k : ℂ) = 0 → e = 0 := by
    intro e he
    have h1 : ∑ k, e k • B k = 0 := by
      apply Subtype.ext
      rw [hval, he]
      rfl
    funext k
    exact Fintype.linearIndependent_iff.1 B.linearIndependent e h1 k
  have hx : ∀ j k, ∑ l, algebraMap F (K j) (B.repr ⟨d l, hmem l⟩ k) * v l j = 0 := by
    intro j
    have hτ' : ∀ τ : K j →+* ℂ, τ.comp (algebraMap F (K j)) = σ →
        ∀ a, τ (algebraMap F (K j) a) = σ a := fun τ hτ a => by rw [← hτ]; rfl
    have := single_ext F (K j) σ (fun k => (B k : ℂ)) hbind
      (fun k => ∑ l, algebraMap F (K j) (B.repr ⟨d l, hmem l⟩ k) * v l j) (fun τ hτ => by
        refine Eq.trans ?_ (hd j τ hτ)
        simp only [map_sum, map_mul, hτ' τ hτ]
        rw [Finset.sum_congr rfl fun l _ => congrArg (· * τ (v l j)) (hdc l)]
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring)
    intro k
    exact congrFun this k
  have hc0 : ∀ k, (fun l => B.repr ⟨d l, hmem l⟩ k) = 0 := fun k => hv _ fun j => hx j k
  funext l
  rw [hdc l, Pi.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  have := congrFun (hc0 k) l
  simp only [Pi.zero_apply] at this
  rw [this, map_zero, zero_mul]

end GlobalTheory.CompanionTheory.Arith.DedekindDescent
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalSubringIntegralClosureMax
section
namespace GlobalTheory.CompanionTheory.Domination

theorem isUnit_subring_iff {K : Type} [Field K] (D : Subring K) (d : D) :
    IsUnit d ↔ (d : K) ≠ 0 ∧ (d : K)⁻¹ ∈ D := by
  constructor
  · rintro ⟨u, rfl⟩
    have h : ((u : D) : K) * (((u⁻¹ : Dˣ) : D) : K) = 1 := by
      exact_mod_cast congrArg Subtype.val u.mul_inv
    refine ⟨left_ne_zero_of_mul_eq_one h, ?_⟩
    rw [inv_eq_of_mul_eq_one_right h]
    exact ((u⁻¹ : Dˣ) : D).2
  · rintro ⟨h0, h⟩
    exact isUnit_iff_exists_inv.2 ⟨⟨_, h⟩, Subtype.ext (by simp [h0])⟩

theorem isMaximal_of_comap {K : Type} [Field K] (R T : Subring K) (hRT : R ≤ T)
    (hint : ∀ t ∈ T, IsIntegral R t) (P : Ideal T) [P.IsPrime]
    (hc : (P.comap (Subring.inclusion hRT)).IsMaximal) : P.IsMaximal := by
  let _ : Algebra R T := (Subring.inclusion hRT).toAlgebra
  have : Algebra.IsIntegral R T := ⟨fun t ↦ by
    let f : T →ₐ[R] K := { T.subtype with commutes' := fun r ↦ rfl }
    exact (isIntegral_algHom_iff f Subtype.val_injective).1 (hint t t.2)⟩
  exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap P hc

theorem eq_ofPrime {K : Type} [Field K] (T D : Subring K) (P : Ideal T) [P.IsPrime]
    (hP : ∀ t : T, t ∈ P ↔ ¬ ((t : K) ≠ 0 ∧ (t : K)⁻¹ ∈ D)) (hTD : T ≤ D)
    (gen : ∀ a ∈ D, ∃ u ∈ T, ∃ v ∈ T, v ≠ 0 ∧ v⁻¹ ∈ D ∧ a = u / v) :
    D = (LocalSubring.ofPrime T P).toSubring := by
  ext a
  simp only [LocalSubring.ofPrime, LocalSubring.range_toSubring]
  show a ∈ D ↔ a ∈ Set.range _
  rw [Set.mem_range]
  constructor
  · intro ha
    obtain ⟨u, hu, v, hv, h0, hvD, rfl⟩ := gen a ha
    have hvP : (⟨v, hv⟩ : T) ∈ P.primeCompl := by
      show (⟨v, hv⟩ : T) ∉ P
      rw [hP]
      exact not_not.2 ⟨h0, hvD⟩
    refine ⟨IsLocalization.mk' _ (⟨u, hu⟩ : T) (⟨⟨v, hv⟩, hvP⟩ : P.primeCompl), ?_⟩
    rw [IsLocalization.lift_mk'_spec]
    show u = v * (u / v)
    field_simp
  · rintro ⟨y, rfl⟩
    obtain ⟨⟨u, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl y
    have hs : ¬ ((s : T) ∈ P) := s.2
    rw [hP, not_not] at hs
    have key : ∀ z : K, ((u : T) : K) = ((s : T) : K) * z → z ∈ D := by
      intro z hz
      have hz' : z = (u : K) * ((s : T) : K)⁻¹ := by
        rw [hz]
        field_simp [hs.1]
      rw [hz']
      exact D.mul_mem (hTD u.2) hs.2
    dsimp only
    apply key
    exact (IsLocalization.lift_mk'_spec (S := Localization.AtPrime P) (g := T.subtype) _ _ _ _).1 rfl

theorem eq_localisation_integralClosure :
    ∀ {K : Type} [Field K] (R D B : Subring K) [IsLocalRing R] [IsLocalRing D], R ≤ D →
      (∀ r ∈ R, r ≠ 0 → r⁻¹ ∈ D → r⁻¹ ∈ R) → (integralClosure R K).toSubring ≤ D →
      B ≤ (integralClosure R K).toSubring →
      (∀ a ∈ D, ∃ u ∈ B, ∃ v ∈ B, v ≠ 0 ∧ v⁻¹ ∈ D ∧ a = u / v) →
      ∃ (P : Ideal (integralClosure R K).toSubring) (_ : P.IsMaximal),
        D = (LocalSubring.ofPrime _ P).toSubring ∧
        ∀ t : (integralClosure R K).toSubring, t ∈ P ↔ ¬ ((t : K) ≠ 0 ∧ (t : K)⁻¹ ∈ D) := by
  intro K _ R D B _ _ hRD hdom hTD hBT gen
  let P : Ideal (integralClosure R K).toSubring :=
    (IsLocalRing.maximalIdeal D).comap (Subring.inclusion hTD)
  have hP : ∀ t : (integralClosure R K).toSubring, t ∈ P ↔ ¬ ((t : K) ≠ 0 ∧ (t : K)⁻¹ ∈ D) := by
    intro t
    show Subring.inclusion hTD t ∈ IsLocalRing.maximalIdeal D ↔ _
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_subring_iff]
    rfl
  have : P.IsPrime := Ideal.comap_isPrime _ _
  have hRT : R ≤ (integralClosure R K).toSubring := fun r hr ↦ by
    show IsIntegral R (algebraMap R K ⟨r, hr⟩)
    exact isIntegral_algebraMap
  have hint : ∀ t ∈ (integralClosure R K).toSubring, IsIntegral R t := fun t ht ↦ ht
  have hPmax : P.IsMaximal := by
    apply isMaximal_of_comap R _ hRT hint P
    have hc : P.comap (Subring.inclusion hRT) = IsLocalRing.maximalIdeal R := by
      ext r
      rw [Ideal.mem_comap, hP, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_subring_iff]
      show ¬ ((r : K) ≠ 0 ∧ (r : K)⁻¹ ∈ D) ↔ ¬ ((r : K) ≠ 0 ∧ (r : K)⁻¹ ∈ R)
      exact not_congr ⟨fun ⟨h0, h⟩ ↦ ⟨h0, hdom _ r.2 h0 h⟩, fun ⟨h0, h⟩ ↦ ⟨h0, hRD h⟩⟩
    rw [hc]
    exact IsLocalRing.maximalIdeal.isMaximal R
  refine ⟨P, hPmax, ?_, hP⟩
  refine eq_ofPrime _ D P hP hTD fun a ha ↦ ?_
  obtain ⟨u, hu, v, hv, h0, hvD, rfl⟩ := gen a ha
  exact ⟨u, hBT hu, v, hBT hv, h0, hvD, rfl⟩

end GlobalTheory.CompanionTheory.Domination
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalizationKaehlerPrimeIdeal
section
namespace GlobalTheory.CompanionTheory.Ar.BoundaryPull

open MvPolynomial

theorem coe_aeval_subalgebra {K : Type} [Field K] [CharZero K] {τ : Type}
    (S : Subalgebra ℚ K) (r : τ → K) (h : ∀ p, r p ∈ S) (g : MvPolynomial τ ℤ) :
    ((aeval (fun p => (⟨r p, h p⟩ : S)) g : S) : K) = aeval r g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

theorem vanishing_rename_iff :
    ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [CharZero Ω₀] [CharZero Ω] [Algebra Ω₀ Ω] (σ σ' : Type)
    (r₀ : σ → Ω₀) (r₁ : σ' → Ω) (v : σ → σ'), (∀ p, algebraMap Ω₀ Ω (r₀ p) = r₁ (v p)) →
    ∀ (bd : Ideal (MvPolynomial σ ℤ)) (S : Subalgebra ℚ Ω₀) (S' : Subalgebra ℚ Ω) (θ : S →+* S'),
    (∀ s, ((θ s : S') : Ω) = algebraMap Ω₀ Ω s) → (∀ p, r₀ p ∈ S) → (∀ p, r₁ p ∈ S') →
    ∀ q : Ideal S',
    ((∀ g ∈ bd.map (MvPolynomial.rename v), ∀ s : S', (s : Ω) = MvPolynomial.aeval r₁ g → s ∈ q) ↔
      (∀ g ∈ bd, ∀ s : S, (s : Ω₀) = MvPolynomial.aeval r₀ g → s ∈ q.comap θ)) := by
  intro Ω₀ Ω _ _ _ _ _ σ σ' r₀ r₁ v hv bd S S' θ hθ h₀ h₁ q
  have key : ∀ b : MvPolynomial σ ℤ,
      MvPolynomial.aeval r₁ (MvPolynomial.rename v b) = algebraMap Ω₀ Ω (MvPolynomial.aeval r₀ b) := by
    intro b
    induction b using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p i hp => simp [hp, hv]
  constructor
  · intro H g hg s hs
    refine Ideal.mem_comap.2 (H (MvPolynomial.rename v g) (Ideal.mem_map_of_mem _ hg) (θ s) ?_)
    rw [hθ, hs, key]
  · intro H g hg s hs
    have claim : ∃ t ∈ q, (t : Ω) = MvPolynomial.aeval r₁ g := by
      have hspan : g ∈ Ideal.span ((MvPolynomial.rename v : MvPolynomial σ ℤ → MvPolynomial σ' ℤ) '' (bd : Set _)) := hg
      refine Submodule.span_induction (p := fun g _ => ∃ t ∈ q, (t : Ω) = MvPolynomial.aeval r₁ g)
        ?_ ?_ ?_ ?_ hspan
      · rintro _ ⟨b, hb, rfl⟩
        let s₀ : S := aeval (fun p => (⟨r₀ p, h₀ p⟩ : S)) b
        have hs₀ : (s₀ : Ω₀) = aeval r₀ b := coe_aeval_subalgebra S r₀ h₀ b
        refine ⟨θ s₀, Ideal.mem_comap.1 (H b hb s₀ hs₀), ?_⟩
        rw [hθ, hs₀, key]
      · exact ⟨0, q.zero_mem, by simp⟩
      · rintro x y _ _ ⟨t, ht, hx⟩ ⟨u, hu, hy⟩
        exact ⟨t + u, q.add_mem ht hu, by simp [hx, hy]⟩
      · rintro c x _ ⟨t, ht, hx⟩
        refine ⟨aeval (fun p => (⟨r₁ p, h₁ p⟩ : S')) c * t, q.mul_mem_left _ ht, ?_⟩
        simp [coe_aeval_subalgebra S' r₁ h₁ c, hx]
    obtain ⟨t, ht, hts⟩ := claim
    have : s = t := Subtype.ext (hs.trans hts.symm)
    exact this ▸ ht

end GlobalTheory.CompanionTheory.Ar.BoundaryPull
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.MaximalIdealMembershipOfLocal
section
namespace GlobalTheory.CompanionTheory.IntegralClosureLocal

theorem mem_maximal_iff_not_inv_mem {K : Type} [Field K] (R : Subring K) [IsLocalRing R]
    (P : Ideal (integralClosure R K).toSubring) (hP : P.IsMaximal)
    (t : (integralClosure R K).toSubring) (htR : (t : K) ∈ R) :
    t ∈ P ↔ ¬ ((t : K) ≠ 0 ∧ (t : K)⁻¹ ∈ R) := by
  let f : R →+* (integralClosure R K).toSubring :=
    (algebraMap R K).codRestrict (integralClosure R K).toSubring
      (fun r => (integralClosure R K).algebraMap_mem r)
  letI : Algebra R (integralClosure R K).toSubring := f.toAlgebra
  haveI : Algebra.IsIntegral R (integralClosure R K).toSubring := by
    refine ⟨fun x => ?_⟩
    obtain ⟨p, hp, h⟩ : IsIntegral R (x : K) := x.2
    refine ⟨p, hp, ?_⟩
    apply Subtype.ext
    have key := Polynomial.hom_eval₂ p f (integralClosure R K).toSubring.subtype x
    exact key.trans h
  have hm : (P.comap (algebraMap R (integralClosure R K).toSubring)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
  have hmax : P.comap (algebraMap R (integralClosure R K).toSubring)
      = IsLocalRing.maximalIdeal R := IsLocalRing.eq_maximalIdeal hm
  have hrt : algebraMap R (integralClosure R K).toSubring ⟨t, htR⟩ = t := Subtype.ext rfl
  have h1 : t ∈ P ↔ (⟨t, htR⟩ : R) ∈ IsLocalRing.maximalIdeal R := by
    rw [← hmax, Ideal.mem_comap, hrt]
  rw [h1, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_iff_not]
  constructor
  · intro hu
    obtain ⟨u, hu⟩ := hu
    have hne : (t : K) ≠ 0 := by
      intro h0
      have : (u : R) = 0 := by rw [hu]; exact Subtype.ext h0
      exact u.ne_zero this
    refine ⟨hne, ?_⟩
    have hmul : ((u : R) : K) * (((u⁻¹ : Rˣ) : R) : K) = 1 := by
      rw [← Subring.coe_mul, Units.mul_inv, Subring.coe_one]
    have hut : ((u : R) : K) = (t : K) := by rw [hu]
    rw [hut] at hmul
    have : (t : K)⁻¹ = (((u⁻¹ : Rˣ) : R) : K) := inv_eq_of_mul_eq_one_right hmul
    rw [this]
    exact Subtype.coe_prop _
  · rintro ⟨hne, hinv⟩
    refine IsUnit.of_mul_eq_one (⟨(t : K)⁻¹, hinv⟩ : R) ?_
    exact Subtype.ext (mul_inv_cancel₀ hne)

end GlobalTheory.CompanionTheory.IntegralClosureLocal
end

