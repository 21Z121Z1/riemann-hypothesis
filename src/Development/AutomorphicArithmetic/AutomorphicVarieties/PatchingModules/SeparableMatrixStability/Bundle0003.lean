import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapEta
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0002
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0003
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0010
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0005
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.PlProps
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0009

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.CoefficientsBoundedOfSelmerBoundary
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem ar_family {A M M' S : Type} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M] [AddCommGroup M'] [Module A M']
    [Module.Finite A M'] (I : Ideal A) (f : S → M →ₗ[A] M') :
    ∃ c : ℕ, ∀ (m : ℕ) (x : M), (∀ s, f s x ∈ I ^ (m + c) • (⊤ : Submodule A M')) →
      ∀ φ : M →ₗ[A] A, (∀ y, (∀ s, f s y = 0) → φ y = 0) → φ x ∈ I ^ m := by
  classical
  have hfg : (Submodule.span A (Set.range f)).FG := IsNoetherian.noetherian _
  obtain ⟨n, v, hv⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hfg
  let Φ : M →ₗ[A] (Fin n → M') := LinearMap.pi v
  obtain ⟨c, hc⟩ := UpperTheory.V.AlgebraTools.comap_pow_le I Φ
  have key : ∀ {ι : Type} (g : ι → M →ₗ[A] M') (N : Submodule A M') (x : M), (∀ i, g i x ∈ N) →
      ∀ u ∈ Submodule.span A (Set.range g), u x ∈ N := by
    intro ι g N x hx u hu
    induction hu using Submodule.span_induction with
    | mem u hu => obtain ⟨i, rfl⟩ := hu; exact hx i
    | zero => simp
    | add a b _ _ ha hb => exact N.add_mem ha hb
    | smul r a _ ha => exact N.smul_mem r ha
  refine ⟨c, fun m x hx φ hφ => ?_⟩
  have h0 : x ∈ (I ^ (m + c) • (⊤ : Submodule A (Fin n → M'))).comap Φ := by
    have h1 : ∀ i, v i x ∈ I ^ (m + c) • (⊤ : Submodule A M') := fun i =>
      key f _ x hx _ (hv ▸ Submodule.subset_span ⟨i, rfl⟩)
    rw [Submodule.mem_comap, ← Finset.univ_sum_single (Φ x)]
    refine Submodule.sum_mem _ fun i _ => ?_
    have h2 : LinearMap.single A (fun _ : Fin n => M') i (v i x) ∈
        (I ^ (m + c) • (⊤ : Submodule A M')).map (LinearMap.single A (fun _ : Fin n => M') i) :=
      Submodule.mem_map_of_mem (h1 i)
    rw [Submodule.map_smul''] at h2
    exact Submodule.smul_mono le_rfl le_top h2
  have hle : LinearMap.ker Φ ⊔ I ^ m • (⊤ : Submodule A M) ≤ Submodule.comap φ (I ^ m : Ideal A) := by
    refine sup_le (fun y hy => ?_) (Submodule.smul_le.2 fun a ha y _ => ?_)
    · have h1 : ∀ i, v i y ∈ (⊥ : Submodule A M') := fun i => congrFun (LinearMap.mem_ker.mp hy) i
      rw [Submodule.mem_comap, hφ y fun s => key v ⊥ y h1 (f s) (hv ▸ Submodule.subset_span ⟨s, rfl⟩)]
      exact zero_mem _
    · rw [Submodule.mem_comap, map_smul, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ ha
  exact hle (hc m h0)

private theorem dd_smul {A : Type} [CommRing A] {g : ℕ} (c : A) (y : DD A g) : c • y = DD.C c * y := rfl

private theorem dd_finite (A : Type) [CommRing A] [IsNoetherianRing A] (g : ℕ) : Module.Finite A (DD A g) := by
  let f : DD A g →ₗ[A] A × (Fin g → A) × (Fin g → A) × A :=
    { toFun := DD.equiv
      map_add' := fun _ _ => rfl
      map_smul' := fun c y => by
        ext <;> simp [dd_smul, DD.equiv] }
  exact Module.Finite.of_injective f DD.equiv.injective

private theorem dd_ker {A : Type} [CommRing A] {g : ℕ} (s : A) (y : DD A g)
    (hy : DD.map g (Ideal.Quotient.mkₐ A (Ideal.span {s})) y = 0) : ∃ y' : DD A g, y = s • y' := by
  have key : ∀ a : A, Ideal.Quotient.mkₐ A (Ideal.span {s}) a = 0 → ∃ b, a = s * b := fun a ha =>
    Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 ha)
  obtain ⟨a, ha⟩ := key y.a (congrArg DD.a hy)
  choose b hb using fun j => key (y.ep j) (congrFun (congrArg DD.ep hy) j)
  choose b' hb' using fun j => key (y.ep' j) (congrFun (congrArg DD.ep' hy) j)
  obtain ⟨d, hd⟩ := key y.eta (congrArg DD.eta hy)
  refine ⟨⟨a, b, b', d⟩, ?_⟩
  ext <;> simp [dd_smul, ha, hb, hb', hd]

private theorem exists_antisymmetric_lift_of_section {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {g n a : ℕ} (f : A →ₐ[A] X)
    (σ : X →+ A) (hσ : ∀ y, f (σ y) = y) (Y : Matrix (Fin n) (Fin n) (DD X g)) (hY : Y ∈ W1 n A X g a)
    (hT : Yᵀ = -Y) : ∃ Y' ∈ W1 n A A g a, Y'ᵀ = -Y' ∧ Y'.map (DD.map g f) = Y := by
  let S : DD X g → DD A g := fun y => ⟨σ y.a, fun j => σ (y.ep j), fun j => σ (y.ep' j), σ y.eta⟩
  have hS : ∀ (b1 b2 b3 b4 : Bool) y, y ∈ ddPart A X g b1 b2 b3 b4 → S y ∈ ddPart A A g b1 b2 b3 b4 := by
    rintro b1 b2 b3 b4 y ⟨h1, h2, h3, h4⟩
    refine ⟨fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_⟩
    · simp [S, h1 e]
    · funext j; simp [S, h2 e]
    · funext j; simp [S, h3 e]
    · simp [S, h4 e]
  refine ⟨Y.map S, fun i j => ⟨fun e => hS _ _ _ _ _ ((hY i j).1 e), fun e => hS _ _ _ _ _ ((hY i j).2 e)⟩, ?_, ?_⟩
  · refine Matrix.ext fun i j => ?_
    have e : Y j i = -Y i j := congrFun (congrFun hT i) j
    show S (Y j i) = -S (Y i j)
    rw [e]
    ext <;> simp [S]
  · refine Matrix.ext fun i j => ?_
    show DD.map g f (S (Y i j)) = Y i j
    ext <;> simp [S, hσ]

private theorem map_first_order_lift_eq {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) {X : Type} [CommRing X]
    [Algebra x.A X] (f : x.A →ₐ[x.A] X) (g : F.G₀) : (k.ρ1 x.A g).map (DD.map k.g f) = k.ρ1 X g := by
  have e1 : (x.ρX (DD x.A k.g) g).map (DD.map k.g f) = x.ρX (DD X k.g) g :=
    Matrix.ext fun i j => (DD.map k.g f).commutes _
  have e2 : (DD.epM fun j => (k.κ j g).map (algebraMap x.A x.A)).map (DD.map k.g f) =
      DD.epM fun j => (k.κ j g).map (algebraMap x.A X) := by
    refine Matrix.ext fun i j => ?_
    refine DD.ext (map_zero f) (funext fun r => f.commutes _) (funext fun r => map_zero f) (map_zero f)
  rw [Kap.ρ1, Kap.ρ1, Matrix.map_mul, e1, Matrix.map_add _ (map_add _), e2, Matrix.map_one _ (map_zero _) (map_one _)]

private theorem exists_section (K : Type) [Field K] (I : Ideal (PowerSeries K)) :
    ∃ σ : (PowerSeries K ⧸ I) →+ PowerSeries K, ∀ y, Ideal.Quotient.mkₐ (PowerSeries K) I (σ y) = y := by
  obtain ⟨σ, hσ⟩ := (Ideal.Quotient.mkₐ K I).toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.2 Ideal.Quotient.mk_surjective)
  exact ⟨σ.toAddMonoidHom, fun y => LinearMap.congr_fun hσ y⟩

theorem UpperTheory.V.Pa.coefficients_bounded_of_selmer_boundary :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (k : Kap x) (e : ℕ) (z : Fin e → G.G₀ → Matrix (Fin n) (Fin n) (DD x.A k.g)), TopFG G.Γ → (∀ i, z i ∈ Sel1 h x.A k) → (∀ c : Fin e → x.A, ∑ i, c i • z i ∈ Bd1 h x.A k → c = 0) → ∃ C : ℕ, ∀ (m : ℕ) (c : Fin e → x.A), (fun g => ((∑ i, c i • z i) g).map (x.redD k.g m)) ∈ Bd1 h (x.Am m) k → ∀ i, c i ∈ Ideal.span {x.t ^ (m - C)} := by
  intro l _ L G G0 h n x k e z _ _ hind
  haveI := dd_finite x.A k.g
  let V : Submodule x.A (Matrix (Fin n) (Fin n) (DD x.A k.g)) :=
    { carrier := {Y | Y ∈ W1 n x.A x.A k.g x.a ∧ Yᵀ = -Y}
      add_mem' := fun ha hb => ⟨add_mem ha.1 hb.1, by rw [transpose_add, ha.2, hb.2, neg_add]⟩
      zero_mem' := ⟨zero_mem _, by simp⟩
      smul_mem' := fun c Y hY => ⟨Submodule.smul_mem _ c hY.1, by rw [transpose_smul, hY.2, smul_neg]⟩ }
  let f : G.G₀ → ((Fin e → x.A) × V) →ₗ[x.A] Matrix (Fin n) (Fin n) (DD x.A k.g) := fun g =>
    { toFun := fun p => (∑ i, p.1 i • z i) g - dY G.frame (fun g => k.ρ1 x.A (h.p₀ g)) p.2 g
      map_add' := fun p q => by
        simp only [dY, Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul, Finset.sum_add_distrib, Submodule.coe_add,
          Matrix.mul_add, Matrix.add_mul]
        abel
      map_smul' := fun c p => by
        simp only [dY, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum,
          Submodule.coe_smul, Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply, smul_sub] }
  haveI : Module.Finite x.A (Matrix (Fin n) (Fin n) (DD x.A k.g)) :=
    inferInstanceAs (Module.Finite x.A (Fin n → Fin n → DD x.A k.g))
  haveI : Module.Finite x.A V := Module.Finite.of_injective V.subtype V.subtype_injective
  obtain ⟨C, hC⟩ := ar_family (Ideal.span {x.t}) f
  refine ⟨C, fun m c hc i => ?_⟩
  rcases le_total m C with hm | hm
  · rw [Nat.sub_eq_zero_of_le hm, pow_zero, Ideal.span_singleton_one]
    trivial
  obtain ⟨m, rfl⟩ : ∃ r, m = r + C := ⟨m - C, by omega⟩
  obtain ⟨Y, hY, hT, hYe⟩ := hc
  obtain ⟨σ, hσ⟩ := exists_section x.K (Ideal.span {x.t ^ (m + C)})
  obtain ⟨Y', hY', hT', rfl⟩ := exists_antisymmetric_lift_of_section _ σ hσ Y hY hT
  rw [Nat.add_sub_cancel, ← Ideal.span_singleton_pow]
  refine hC m (c, ⟨Y', hY', hT'⟩) (fun g => ?_) ((LinearMap.proj i).comp (LinearMap.fst _ _ _)) fun p hp => ?_
  · have h0 : (f g (c, ⟨Y', hY', hT'⟩)).map (x.redD k.g (m + C)) = 0 := by
      show ((∑ i, c i • z i) g - dY G.frame (fun g => k.ρ1 x.A (h.p₀ g)) Y' g).map (x.redD k.g (m + C)) = 0
      rw [Matrix.map_sub _ (map_sub _), congrFun hYe g, sub_eq_zero, dY, dY, Matrix.map_sub _ (map_sub _),
        Matrix.map_mul, Matrix.map_mul, map_first_order_lift_eq, map_first_order_lift_eq]
    choose Z hZ using fun a b => dd_ker (x.t ^ (m + C)) _ (congrFun (congrFun h0 a) b)
    have h1 : f g (c, ⟨Y', hY', hT'⟩) = x.t ^ (m + C) • Matrix.of Z := Matrix.ext hZ
    rw [h1, Ideal.span_singleton_pow]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) trivial
  · exact congrFun (hind p.1 ⟨p.2, p.2.2.1, p.2.2.2, funext fun g => sub_eq_zero.1 (hp g)⟩) i
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.EventuallyFactorThroughTowerIffLimit
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private def stabR {P Z : Type} [Group P] (c : P → Z) : Subgroup P where
  carrier := {k | ∀ g, c (g * k) = c g}
  one_mem' g := by rw [mul_one]
  mul_mem' {a b} ha hb g := by rw [← mul_assoc, hb, ha]
  inv_mem' {a} ha g := by
    have := ha (g * a⁻¹)
    rw [inv_mul_cancel_right] at this
    exact this.symm

private theorem stabR_open {P Z : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
    (c : P → Z) (hc : IsLocallyConstant c) : IsOpen (stabR c : Set P) := by
  classical
  apply Subgroup.isOpen_of_mem_nhds (g := 1)
  have key : ∀ z ∈ Set.range c, ∀ᶠ k in nhds (1 : P), ∀ g, c g = z → c (g * k) = z := by
    intro z _
    have hK : IsCompact (c ⁻¹' {z}) := (hc.isClosed_fiber z).isCompact
    obtain ⟨V, hV, hKV⟩ := compact_open_separated_mul_right hK (hc.isOpen_fiber z) le_rfl
    filter_upwards [hV] with k hk g hg
    exact hKV (Set.mul_mem_mul hg hk)
  have hall := (Filter.eventually_all_finite hc.range_finite).2 key
  filter_upwards [hall] with k hk
  exact (show ∀ g, c (g * k) = c g from fun g => hk (c g) ⟨g, rfl⟩ g rfl)

private theorem fac_iff {P A Z : Type} [Group P] [Group A] (f : P →* A) (hf : Function.Surjective f) (c : P → Z) :
    (∃ z : A → Z, ∀ g, z (f g) = c g) ↔ f.ker ≤ stabR c := by
  constructor
  · rintro ⟨z, hz⟩ k hk
    show ∀ g, c (g * k) = c g
    intro g
    rw [← hz, ← hz, map_mul, MonoidHom.mem_ker.1 hk, mul_one]
  · intro hle
    refine ⟨fun a => c (Classical.choose (hf a)), fun g => ?_⟩
    show c (Classical.choose (hf (f g))) = c g
    have hspec : f (Classical.choose (hf (f g))) = f g := Classical.choose_spec (hf (f g))
    generalize Classical.choose (hf (f g)) = g' at hspec ⊢
    have hk : g'⁻¹ * g ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hspec, inv_mul_cancel]
    have := (show ∀ y, c (y * (g'⁻¹ * g)) = c y from hle hk) g'
    rw [mul_inv_cancel_left] at this
    exact this.symm

private theorem ker_iff {P A : Type} [Group P] [Group A] (H : Subgroup P) (B : Subgroup A) (π : P →* A)
    (f : H →* B) (hf : ∀ g, (f g : A) = π g) (hH : π.ker ≤ H) (S : Subgroup H) :
    f.ker ≤ S ↔ π.ker ≤ (S.map H.subtype).normalCore := by
  have hker : ∀ h : H, h ∈ f.ker ↔ (h : P) ∈ π.ker := by
    intro h
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, ← hf, OneMemClass.coe_eq_one]
  constructor
  · intro hle
    rw [Subgroup.normal_le_normalCore]
    intro k hk
    have hkH : k ∈ H := hH hk
    exact ⟨⟨k, hkH⟩, hle ((hker ⟨k, hkH⟩).2 hk), rfl⟩
  · intro hle h hh
    obtain ⟨s, hs, hsh⟩ := (Subgroup.normalCore_le _) (hle ((hker h).1 hh))
    have : s = h := Subtype.ext hsh
    rw [← this]
    exact hs

theorem UpperTheory.V.Pa.eventually_factor_through_tower_iff_limit :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (Z : Type) (c : Λ.Ph0 → Z), IsLocallyConstant c → ∀ᶠ N in (Λ.U : Filter ℕ), ((∃ zN : (T.GN N).G₀ → Z, ∀ g, zN (Λ.π0 N g) = c g) ↔ ∃ z : Λ.G.G₀ → Z, ∀ g, z (Λ.πo0 g) = c g) := by
  intro l _ L G0 T Λ Z c hc
  set K0 : Subgroup Λ.Ph := (Λ.G.η.comp Λ.πo).ker with hK0def
  have hK0 : IsOpen (K0 : Set Λ.Ph) := Λ.Ph0_open
  haveI : CompactSpace Λ.Ph0 := isCompact_iff_compactSpace.mp (K0.isClosed_of_isOpen hK0).isCompact
  have hS : IsOpen (stabR c : Set Λ.Ph0) := stabR_open c hc
  have hO : IsOpen (((stabR c).map K0.subtype : Subgroup Λ.Ph) : Set Λ.Ph) := by
    rw [Subgroup.coe_map]
    exact hK0.isOpenMap_subtype_val _ hS
  let O : OpenSubgroup Λ.Ph := ⟨(stabR c).map K0.subtype, hO⟩
  haveI : Finite (Λ.Ph ⧸ O.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ hO
  haveI : O.toSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  let V : OpenNormalSubgroup Λ.Ph :=
    { toSubgroup := O.toSubgroup.normalCore
      isOpen' := Subgroup.isOpen_of_isClosed_of_finiteIndex _ (O.toSubgroup.normalCore_isClosed O.isClosed) }
  have hHo : Λ.πo.ker ≤ K0 := by
    intro k hk
    rw [hK0def, MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.mem_ker.1 hk, map_one]
  filter_upwards [Λ.ker_lim V] with N hN
  have hHN : (Λ.π N).ker ≤ K0 := by
    intro k hk
    rw [hK0def, MonoidHom.mem_ker, MonoidHom.comp_apply, ← Λ.η_π N, MonoidHom.mem_ker.1 hk, map_one]
  rw [fac_iff _ (Λ.π0_surj N), fac_iff _ Λ.πo0_surj,
    ker_iff K0 _ (Λ.π N) (Λ.π0 N) (fun g => rfl) hHN, ker_iff K0 _ Λ.πo Λ.πo0 (fun g => rfl) hHo]
  have e : (Λ.π N).ker ⊔ ((stabR c).map K0.subtype).normalCore =
      Λ.πo.ker ⊔ ((stabR c).map K0.subtype).normalCore := hN
  rw [← sup_eq_right, e, sup_eq_right]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.EventuallyFactorizationCompatibleWithLocalMaps
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem exists_open_normal {P Z : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
    [TotallyDisconnectedSpace P] (K : Subgroup P) (hK : IsOpen (K : Set P)) (c : K → Z) (hc : IsLocallyConstant c) :
    ∃ V : OpenNormalSubgroup P, ∀ g g' : K, (g : P)⁻¹ * g' ∈ V → c g = c g' := by
  have hKc : IsClosed (K : Set P) := Subgroup.isClosed_of_isOpen K hK
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc.isCompact
  have hfin : (Set.range c).Finite := hc.range_finite
  have hS : ∀ z, ∃ W ∈ nhds (1 : P), ∀ x ∈ (Subtype.val '' (c ⁻¹' {z}) : Set P), ∀ w ∈ W,
      x * w ∈ (Subtype.val '' (c ⁻¹' {z}) : Set P) := by
    intro z
    have hcpt : IsCompact (Subtype.val '' (c ⁻¹' {z}) : Set P) :=
      (hc.isClosed_fiber z).isCompact.image continuous_subtype_val
    have ho : IsOpen (Subtype.val '' (c ⁻¹' {z}) : Set P) :=
      hK.isOpenMap_subtype_val _ (hc.isOpen_fiber z)
    open scoped Pointwise in
    obtain ⟨W, hW, hWS⟩ := compact_open_separated_mul_right hcpt ho subset_rfl
    open scoped Pointwise in
    exact ⟨W, hW, fun x hx w hw => hWS (Set.mul_mem_mul hx hw)⟩
  choose W hW hWS using hS
  have hI : (⋂ z ∈ Set.range c, W z) ∈ nhds (1 : P) := (Filter.biInter_mem hfin).2 fun z _ => hW z
  obtain ⟨O, hOI, hOo, h1O⟩ := mem_nhds_iff.1 hI
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hOo h1O
  refine ⟨H, fun g g' hgg => ?_⟩
  have h1 : (g : P)⁻¹ * g' ∈ W (c g) := Set.mem_iInter₂.1 (hOI (hH hgg)) (c g) ⟨g, rfl⟩
  have h2 : (g : P) ∈ Subtype.val '' (c ⁻¹' {c g}) := ⟨g, rfl, rfl⟩
  have h3 := hWS (c g) _ h2 _ h1
  rw [mul_inv_cancel_left] at h3
  obtain ⟨a', ha', he⟩ := h3
  have e : a' = g' := Subtype.ext he
  rw [← e]
  exact ha'.symm

theorem UpperTheory.V.Pa.eventually_factorization_compatible_with_local_maps :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (Z : Type) (c : Λ.Ph0 → Z), IsLocallyConstant c → ∀ᶠ N in (Λ.U : Filter ℕ), ∀ (zN : (T.GN N).G₀ → Z) (z : Λ.G.G₀ → Z), (∀ g, zN (Λ.π0 N g) = c g) → (∀ g, z (Λ.πo0 g) = c g) → (∀ v g, zN ((T.GN N).φ v g) = z (Λ.G.φ v g)) ∧ (∀ w g, zN ((T.GN N).φu w g) = z (Λ.G.φu w g)) ∧ ∀ j, zN (T.ph N j) = z (Λ.ph j) ∧ zN (T.ta N j) = z (Λ.ta j) := by
  intro l _ L G0 T Λ Z c hc
  obtain ⟨V, hV⟩ := exists_open_normal _ Λ.Ph0_open c hc
  filter_upwards [Λ.φ_lim V, Λ.φu_lim V, Λ.ph_lim V, Λ.ta_lim V] with N h1 h2 h3 h4 zN z hN ho
  have key : ∀ (a : (T.GN N).G₀) (b : Λ.G.G₀), Close (Λ.π N) Λ.πo V.toSubgroup (a : (T.GN N).Γ) (b : Λ.G.Γ) →
      zN a = z b := by
    rintro a b ⟨g, g', ea, eb, hg⟩
    have m : g ∈ (Λ.G.η.comp Λ.πo).ker := (Λ.η_π N g).symm.trans (by rw [ea]; exact a.2)
    have m' : g' ∈ (Λ.G.η.comp Λ.πo).ker := show Λ.G.η (Λ.πo g') = 1 by rw [eb]; exact b.2
    have ea' : a = Λ.π0 N ⟨g, m⟩ := Subtype.ext ea.symm
    have eb' : b = Λ.πo0 ⟨g', m'⟩ := Subtype.ext eb.symm
    rw [ea', eb', hN, ho]
    exact hV _ _ hg
  exact ⟨fun v g => key _ _ (h1 v g), fun w g => key _ _ (h2 w g), fun j => ⟨key _ _ (h3 j), key _ _ (h4 j)⟩⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.EventuallyLocallyConstantCompTowerEq
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.eventually_locallyConstant_comp_tower_eq :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (Z : Type) (ρ : G0.G₀ → Z), IsLocallyConstant ρ → ∀ᶠ N in (Λ.U : Filter ℕ), ∀ g, ρ ((T.h N).p₀ (Λ.π0 N g)) = ρ (Λ.h.p₀ (Λ.πo0 g)) := by
  intro l _ L G0 T Λ Z ρ hρ
  have hKo : IsOpen ((G0.η.ker : Subgroup G0.Γ) : Set G0.Γ) := G0.η_open
  have hKc : IsClosed ((G0.η.ker : Subgroup G0.Γ) : Set G0.Γ) := Subgroup.isClosed_of_isOpen _ hKo
  haveI : CompactSpace G0.G₀ := isCompact_iff_compactSpace.mp hKc.isCompact
  have hfin : (Set.range ρ).Finite := hρ.range_finite
  have hS : ∀ z, ∃ V ∈ nhds (1 : G0.Γ), ∀ v ∈ V, ∀ x ∈ (Subtype.val '' (ρ ⁻¹' {z}) : Set G0.Γ),
      v * x ∈ (Subtype.val '' (ρ ⁻¹' {z}) : Set G0.Γ) := by
    intro z
    have hc : IsCompact (Subtype.val '' (ρ ⁻¹' {z}) : Set G0.Γ) :=
      (hρ.isClosed_fiber z).isCompact.image continuous_subtype_val
    have ho : IsOpen (Subtype.val '' (ρ ⁻¹' {z}) : Set G0.Γ) :=
      hKo.isOpenMap_subtype_val _ (hρ.isOpen_fiber z)
    open scoped Pointwise in
    obtain ⟨V, hV, hVS⟩ := compact_open_separated_mul_left hc ho subset_rfl
    open scoped Pointwise in
    exact ⟨V, hV, fun v hv x hx => hVS (Set.mul_mem_mul hv hx)⟩
  choose V hV hVS using hS
  have hW : (⋂ z ∈ Set.range ρ, V z) ∈ nhds (1 : G0.Γ) := (Filter.biInter_mem hfin).2 fun z _ => hV z
  obtain ⟨O, hOW, hOo, h1O⟩ := mem_nhds_iff.1 hW
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hOo h1O
  filter_upwards [Λ.p_lim H] with N hN g
  set a := (T.h N).p₀ (Λ.π0 N g)
  set b := Λ.h.p₀ (Λ.πo0 g)
  have hab : (a : G0.Γ) * (b : G0.Γ)⁻¹ ∈ (H : Set G0.Γ) := hN g.1
  have h1 : (a : G0.Γ) * (b : G0.Γ)⁻¹ ∈ V (ρ b) := Set.mem_iInter₂.1 (hOW (hH hab)) (ρ b) ⟨b, rfl⟩
  have h2 : (b : G0.Γ) ∈ Subtype.val '' (ρ ⁻¹' {ρ b}) := ⟨b, rfl, rfl⟩
  have h3 := hVS (ρ b) _ h1 _ h2
  rw [inv_mul_cancel_right] at h3
  obtain ⟨a', ha', he⟩ := h3
  have e : a' = a := Subtype.ext he
  rw [← e]
  exact ha'
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.GdetDesc
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem gdesc_ker {A G G' : Type} [CommRing A] [Group G] [Group G'] (f : G →* G')
    (hf : Function.Surjective f) (J : TwoSidedIdeal (MonoidAlgebra A G))
    (hJ : ∀ k, f k = 1 → MonoidAlgebra.single k 1 - 1 ∈ J) (x : MonoidAlgebra A G)
    (hx : MonoidAlgebra.mapDomainAlgHom A A f x = 0) : x ∈ J := by
  have key : ∀ y : MonoidAlgebra A G,
      y - MonoidAlgebra.mapDomain (Function.surjInv hf) (MonoidAlgebra.mapDomainAlgHom A A f y) ∈ J := by
    intro y
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb =>
      rw [map_add, MonoidAlgebra.mapDomain_add, add_sub_add_comm]
      exact J.add_mem ha hb
    | single g a =>
      have h1 := J.mul_mem_left (MonoidAlgebra.single (Function.surjInv hf (f g)) a) _
        (hJ ((Function.surjInv hf (f g))⁻¹ * g) (by simp [Function.surjInv_eq]))
      rw [mul_sub, MonoidAlgebra.single_mul_single, mul_inv_cancel_left, mul_one, mul_one] at h1
      simpa using h1
  simpa [hx] using key x

private theorem gdesc_toT {A G G' : Type} [CommRing A] [Group G] [Group G'] (f : G →* G')
    (B : Type) [CommRing B] [Algebra A B] (x : MonoidAlgebra B G) :
    toT A G' B (MonoidAlgebra.mapDomainRingHom B f x) =
      Algebra.TensorProduct.map (AlgHom.id B B) (MonoidAlgebra.mapDomainAlgHom A A f) (toT A G B x) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single g s => simp [toT_single]

theorem UpperTheory.V.Pa.gdet_desc :
    ∀ (n : ℕ) (A G G' : Type) [CommRing A] [Group G] [Group G'] (f : G →* G') (D : GDet n A G), Function.Surjective f → (∀ k, f k = 1 → D.Kills (MonoidAlgebra.single k 1 - 1)) → ∃ D' : GDet n A G', D'.comap f = D := by
  intro n A G G' _ _ _ f D hf hk
  have hs : Function.Surjective (MonoidAlgebra.mapDomainAlgHom A A f) := by
    intro y
    induction y using MonoidAlgebra.induction_linear with
    | zero => exact ⟨0, map_zero _⟩
    | add a b ha hb =>
      obtain ⟨a, rfl⟩ := ha
      obtain ⟨b, rfl⟩ := hb
      exact ⟨a + b, map_add _ _ _⟩
    | single g a =>
      obtain ⟨g, rfl⟩ := hf g
      exact ⟨MonoidAlgebra.single g a, by simp⟩
  obtain ⟨D', hD', -⟩ := UpperTheory.V.CA.d_factor D.toDet (MonoidAlgebra.mapDomainAlgHom A A f) hs
    (gdesc_ker f hf _ fun k h => (UpperTheory.V.CA.d_ker _ _).1.2 ((UpperTheory.V.CA.d_toDet D _).2.2.2.2 (hk k h)))
  refine ⟨GDet.ofDet D', ?_⟩
  rw [← GDet.ofDet_toDet D, ← hD']
  exact GDet.ext fun B _ _ x => congrArg (D'.D B) (gdesc_toT f B x)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.HomDesc
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.hom_desc :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (A A' B B' : Glob l L) (a : A.Hom A') (b : B.Hom B') (h : A.Hom B), a.p.ker ≤ (b.p.comp h.p).ker → ∃ h' : A'.Hom B', ∀ x, h'.p (a.p x) = b.p (h.p x) := by
  intro l _ L A A' B B' a b h hk
  have hT1 : T1Space A'.Γ := by
    refine ⟨fun x => ?_⟩
    have h1 : IsPreconnected (closure ({x} : Set A'.Γ)) := isPreconnected_singleton.closure
    have h2 := h1.subsingleton
    have h3 : closure ({x} : Set A'.Γ) = {x} :=
      h2.eq_singleton_of_mem (subset_closure (Set.mem_singleton x))
    exact closure_eq_iff_isClosed.mp h3
  have hT2 : T2Space A'.Γ := inferInstance
  let q : A'.Γ →* B'.Γ := a.p.liftOfRightInverse (Function.surjInv a.surj)
    (Function.rightInverse_surjInv a.surj) ⟨b.p.comp h.p, hk⟩
  have hq : ∀ x, q (a.p x) = b.p (h.p x) := fun x =>
    a.p.liftOfRightInverse_comp_apply _ _ ⟨b.p.comp h.p, hk⟩ x
  have hquot : Topology.IsQuotientMap a.p :=
    a.cont.isClosedMap.isQuotientMap a.cont a.surj
  refine ⟨⟨q, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hq⟩
  · rw [hquot.continuous_iff]
    have : (q : A'.Γ → B'.Γ) ∘ a.p = fun x => b.p (h.p x) := funext hq
    rw [this]
    exact b.cont.comp h.cont
  · intro y
    obtain ⟨z, rfl⟩ := b.surj y
    obtain ⟨x, rfl⟩ := h.surj z
    exact ⟨a.p x, hq x⟩
  · intro g
    obtain ⟨x, rfl⟩ := a.surj g
    rw [hq, b.η, h.η, a.η]
  · rw [← a.c, hq, h.c, b.c]
  · intro g
    obtain ⟨x, rfl⟩ := a.surj g
    rw [hq, b.ε, h.ε, a.ε]
  · intro v g
    rw [← a.φ, hq, h.φ, b.φ]
  · intro v g
    rw [← a.φu, hq, h.φu, b.φu]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.HomlDesc
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.homl_desc :
    ∀ (l : ℕ) [Fact l.Prime] (Γ Γ' : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [Group Γ'] [TopologicalSpace Γ'] [IsTopologicalGroup Γ'] [CompactSpace Γ'] [TotallyDisconnectedSpace Γ'] (f : Γ →* Γ') (H : Subgroup Γ'), Continuous f → Function.Surjective f → Finite (HomL l (H.comap f)) → Finite (HomL l H) ∧ Nat.card (HomL l H) ≤ Nat.card (HomL l (H.comap f)) := by
  intro l _ Γ Γ' _ _ _ _ _ _ _ _ _ _ f H hf hsurj hfin
  let g : (H.comap f) →* H := f.subgroupComap H
  have hg : Continuous g := (hf.comp continuous_subtype_val).subtype_mk _
  have hgs : Function.Surjective g := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hsurj y
    exact ⟨⟨x, hy⟩, rfl⟩
  let Φ : HomL l H → HomL l (H.comap f) := fun φ =>
    ⟨φ.1.comp g, by
      show IsOpen (g ⁻¹' (φ.1.ker : Set H))
      exact φ.2.preimage hg⟩
  have hinj : Function.Injective Φ := by
    intro φ ψ h
    apply Subtype.ext
    apply MonoidHom.ext
    intro y
    obtain ⟨x, rfl⟩ := hgs y
    have := congrArg (fun χ : HomL l (H.comap f) => χ.1 x) h
    simpa [Φ] using this
  have hF : Finite (HomL l H) := Finite.of_injective Φ hinj
  exact ⟨hF, Nat.card_le_card_of_injective Φ hinj⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.PlMap
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.pl_map :
    ∀ (l : ℕ) [Fact l.Prime] (Γ Γ' : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [Group Γ'] [TopologicalSpace Γ'] [IsTopologicalGroup Γ'] [CompactSpace Γ'] [TotallyDisconnectedSpace Γ'] (f : Γ →* Γ') (H : Subgroup Γ') [H.Normal], IsOpen (H : Set Γ') → Continuous f → Function.Surjective f → (PL l (H.comap f)).map f = PL l H := by
  intro l _ Γ Γ' _ _ _ _ _ _ _ _ _ _ f H _ hH hf hsurj
  have hH' : IsOpen ((H.comap f : Subgroup Γ) : Set Γ) := hH.preimage hf
  haveI : CompactSpace H :=
    isCompact_iff_compactSpace.mp (Subgroup.isClosed_of_isOpen H hH).isCompact
  haveI : CompactSpace (H.comap f) :=
    isCompact_iff_compactSpace.mp (Subgroup.isClosed_of_isOpen _ hH').isCompact
  let g : (H.comap f) →* H := f.subgroupComap H
  have hg : Continuous g := (hf.comp continuous_subtype_val).subtype_mk _
  have hgs : Function.Surjective g := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hsurj y
    exact ⟨⟨x, hy⟩, rfl⟩
  have hcomp : f.comp (H.comap f).subtype = H.subtype.comp g := by
    ext x
    rfl
  rw [(pl_props l Γ (H.comap f) hH').2.2.2.2.2, (pl_props l Γ' H hH).2.2.2.2.2]
  unfold proLResOf
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, proLRes_map l _ _ g hg hgs]
end

