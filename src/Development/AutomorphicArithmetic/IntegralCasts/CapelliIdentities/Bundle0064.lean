import Mathlib

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SumSupportEq
section
open scoped Classical

@[reducible] noncomputable def UpperTheory.Reformulated.B.Yfa1.MRing.{u_1, u_2, u_3} :
    {K : Type u_1} → (K → Type u_2) → (R : Type u_3) → [CommRing R] → Type (max u_3 u_2 u_1) :=
    fun {K : Type u_1} (ι : K → Type u_2) (R : Type u_3) [CommRing R] ↦ MvPolynomial ((k : K) × ι k) R

noncomputable def UpperTheory.Reformulated.B.Yfa1.cycEval.{u_1, u_2, u_3} :
    {K : Type u_1} →
      {ι : K → Type u_2} →
        {R : Type u_3} →
          [inst : CommRing R] → (Ideal (UpperTheory.Reformulated.B.Yfa1.MRing ι R) → ℤ) → (Ideal (UpperTheory.Reformulated.B.Yfa1.MRing ι R) → ℤ) → ℤ :=
    fun {K : Type u_1} {ι : K → Type u_2} {R : Type u_3} [CommRing R] (n Z : Ideal (UpperTheory.Reformulated.B.Yfa1.MRing ι R) → ℤ) ↦
      ∑ᶠ (W : Ideal (UpperTheory.Reformulated.B.Yfa1.MRing ι R)), Z W * n W

noncomputable def UpperTheory.Reformulated.B.Yfa1.eventualValue.{u_1} :
    {K : Type u_1} → ((K → ℤ) → ℤ) → ℤ :=
    fun {K : Type u_1} (f : (K → ℤ) → ℤ) ↦
      if h : ∃ (c : ℤ), ∀ᶠ (m : K → ℤ) in Filter.atTop, f m = c then h.choose else (0 : ℤ)

noncomputable def UpperTheory.Reformulated.B.Yfa1.diffStep.{u_1} :
    {K : Type u_1} → (K → ℤ) → ((K → ℤ) → ℤ) → (K → ℤ) → ℤ :=
    fun {K : Type u_1} (b : K → ℤ) (h : (K → ℤ) → ℤ) (m : K → ℤ) ↦ h m - h (m - b)

noncomputable def UpperTheory.Reformulated.B.Yfa1.mixedDiff.{u_1} :
    {K : Type u_1} → {n : ℕ} → (Fin n → K → ℤ) → ((K → ℤ) → ℤ) → (K → ℤ) → ℤ :=
    fun {K : Type u_1} {n : ℕ} (bs : Fin n → K → ℤ) (h : (K → ℤ) → ℤ) ↦
      List.foldr UpperTheory.Reformulated.B.Yfa1.diffStep h (List.ofFn bs)

noncomputable def UpperTheory.Reformulated.B.Yfa1.blockWeight.{u_1, u_2} :
    {K : Type u_1} → (ι : K → Type u_2) → [DecidableEq K] → (k : K) × ι k → K → ℕ :=
    fun {K : Type u_1} (ι : K → Type u_2) [DecidableEq K] (v : (k : K) × ι k) ↦ Pi.single v.fst (1 : ℕ)

noncomputable def UpperTheory.Reformulated.B.Yfa1.gradedPiece.{u_1, u_2, u_3} :
    {K : Type u_1} →
      [DecidableEq K] →
        {ι : K → Type u_2} →
          {F : Type u_3} →
            [inst : Field F] →
              (P : Ideal (UpperTheory.Reformulated.B.Yfa1.MRing ι F)) → (K → ℕ) → Submodule F (UpperTheory.Reformulated.B.Yfa1.MRing ι F ⧸ P) :=
    fun {K : Type u_1} [DecidableEq K] {ι : K → Type u_2} {F : Type u_3} [Field F] (P : Ideal (UpperTheory.Reformulated.B.Yfa1.MRing ι F))
        (m : K → ℕ) ↦
      Submodule.map (Ideal.Quotient.mkₐ F P).toLinearMap
        (MvPolynomial.weightedHomogeneousSubmodule F (UpperTheory.Reformulated.B.Yfa1.blockWeight ι) m)

noncomputable def UpperTheory.Reformulated.B.Yfa1.hilbFn.{u_1, u_2, u_3} :
    {K : Type u_1} →
      [DecidableEq K] →
        {ι : K → Type u_2} → {F : Type u_3} → [inst : Field F] → Ideal (UpperTheory.Reformulated.B.Yfa1.MRing ι F) → (K → ℤ) → ℤ :=
    fun {K : Type u_1} [DecidableEq K] {ι : K → Type u_2} {F : Type u_3} [Field F] (P : Ideal (UpperTheory.Reformulated.B.Yfa1.MRing ι F))
        (m : K → ℤ) ↦
      if ∀ (k : K), (0 : ℤ) ≤ m k then (↑(Module.finrank F ↥(UpperTheory.Reformulated.B.Yfa1.gradedPiece P fun (k : K) ↦ (m k).toNat)) : ℤ)
      else (0 : ℤ)

noncomputable def UpperTheory.Reformulated.B.Yfa1.intNum.{u_1, u_2, u_4} :
    {K : Type u_1} →
      [DecidableEq K] →
        {ι : K → Type u_2} →
          (F : Type u_4) → [inst : Field F] → Ideal (UpperTheory.Reformulated.B.Yfa1.MRing ι F) → {n : ℕ} → (Fin n → K → ℤ) → ℤ :=
    fun {K : Type u_1} [DecidableEq K] {ι : K → Type u_2} (F : Type u_4) [Field F] (P : Ideal (UpperTheory.Reformulated.B.Yfa1.MRing ι F))
        {n : ℕ} (bs : Fin n → K → ℤ) ↦
      UpperTheory.Reformulated.B.Yfa1.eventualValue (UpperTheory.Reformulated.B.Yfa1.mixedDiff bs (UpperTheory.Reformulated.B.Yfa1.hilbFn P))

noncomputable def UpperTheory.Reformulated.B.Yfa1.specialIdeal.{u_1, u_2, u_3} :
    {K : Type u_1} →
      {ι : K → Type u_2} →
        {O : Type u_3} →
          [inst : CommRing O] →
            [inst_1 : IsDomain O] →
              [inst_2 : IsDiscreteValuationRing O] →
                Ideal (UpperTheory.Reformulated.B.Yfa1.MRing ι O) → Ideal (UpperTheory.Reformulated.B.Yfa1.MRing ι (IsLocalRing.ResidueField O)) :=
    fun {K : Type u_1} {ι : K → Type u_2} {O : Type u_3} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
        (W : Ideal (UpperTheory.Reformulated.B.Yfa1.MRing ι O)) ↦
      Ideal.map (MvPolynomial.map (IsLocalRing.residue O)) W

noncomputable def UpperTheory.Reformulated.B.Yfa1.vNum.{u_1, u_2, u_3} :
    {K : Type u_1} →
      [DecidableEq K] →
        {ι : K → Type u_2} →
          {O : Type u_3} →
            [inst : CommRing O] →
              [inst_1 : IsDomain O] →
                [IsDiscreteValuationRing O] → Ideal (UpperTheory.Reformulated.B.Yfa1.MRing ι O) → {n : ℕ} → (Fin n → K → ℤ) → ℤ :=
    fun {K : Type u_1} [DecidableEq K] {ι : K → Type u_2} {O : Type u_3} [CommRing O] [IsDomain O]
        [IsDiscreteValuationRing O] (W : Ideal (UpperTheory.Reformulated.B.Yfa1.MRing ι O)) {n : ℕ} (bs : Fin n → K → ℤ) ↦
      UpperTheory.Reformulated.B.Yfa1.intNum (IsLocalRing.ResidueField O) (UpperTheory.Reformulated.B.Yfa1.specialIdeal W) bs

noncomputable def UpperTheory.Reformulated.B.Yfa1.vNumL.{u_1, u_2, u_3} :
    {K : Type u_1} →
      [DecidableEq K] →
        {ι : K → Type u_2} →
          {O : Type u_3} →
            [inst : CommRing O] →
              [inst_1 : IsDomain O] → [IsDiscreteValuationRing O] → Ideal (UpperTheory.Reformulated.B.Yfa1.MRing ι O) → List (K → ℤ) → ℤ :=
    fun {K : Type u_1} [DecidableEq K] {ι : K → Type u_2} {O : Type u_3} [CommRing O] [IsDomain O]
        [IsDiscreteValuationRing O] (W : Ideal (UpperTheory.Reformulated.B.Yfa1.MRing ι O)) (l : List (K → ℤ)) ↦
      UpperTheory.Reformulated.B.Yfa1.vNum W l.get

noncomputable def UpperTheory.Reformulated.B.Yfa1.cycList :
    {K : Type} →
      {ι : K → Type} →
        [DecidableEq K] →
          {O : Type} →
            [inst : CommRing O] →
              [inst_1 : IsDomain O] →
                [IsDiscreteValuationRing O] → (Ideal (UpperTheory.Reformulated.B.Yfa1.MRing ι O) → ℤ) → List (K → ℤ) → ℤ :=
    fun {K : Type} {ι : K → Type} [DecidableEq K] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
        (Z : Ideal (UpperTheory.Reformulated.B.Yfa1.MRing ι O) → ℤ) (l : List (K → ℤ)) ↦
      UpperTheory.Reformulated.B.Yfa1.cycEval (fun (W : Ideal (UpperTheory.Reformulated.B.Yfa1.MRing ι O)) ↦ UpperTheory.Reformulated.B.Yfa1.vNumL W l) Z

noncomputable def UpperTheory.Reformulated.B.Yfa1.classList.{u_1, u_3} :
    {K : Type u_1} → {σ : Type u_3} → (σ → K → ℤ) → (σ →₀ ℕ) → List (K → ℤ) :=
    fun {K : Type u_1} {σ : Type u_3} (cls : σ → K → ℤ) (μ : σ →₀ ℕ) ↦
      (Multiset.map cls ((Finsupp.toMultiset : (σ →₀ ℕ) → Multiset σ) μ)).toList

noncomputable def UpperTheory.Reformulated.B.Yfa1.cycNum :
    {K : Type} →
      {ι : K → Type} →
        {σ : Type} →
          [DecidableEq K] →
            {O : Type} →
              [inst : CommRing O] →
                [inst_1 : IsDomain O] →
                  [IsDiscreteValuationRing O] →
                    (Ideal (UpperTheory.Reformulated.B.Yfa1.MRing ι O) → ℤ) → (σ → K → ℤ) → MvPolynomial σ ℝ → List (K → ℤ) → ℝ :=
    fun {K : Type} {ι : K → Type} {σ : Type} [DecidableEq K] {O : Type} [CommRing O] [IsDomain O]
        [IsDiscreteValuationRing O] (Z : Ideal (UpperTheory.Reformulated.B.Yfa1.MRing ι O) → ℤ) (cls : σ → K → ℤ) (H : MvPolynomial σ ℝ)
        (Q : List (K → ℤ)) ↦
      ∑ μ ∈ H.support, MvPolynomial.coeff μ H * (↑(UpperTheory.Reformulated.B.Yfa1.cycList Z (UpperTheory.Reformulated.B.Yfa1.classList cls μ ++ Q)) : ℝ)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SummableProdCoord
section
private lemma sum_prod_le {ι : Type*} [Fintype ι] [DecidableEq ι] {α : Type*} {g : α → ℝ}
    (hg : ∀ x, 0 ≤ g x) (hs : Summable g) (s : Finset (ι → α)) :
    ∑ ξ ∈ s, ∏ i, g (ξ i) ≤ ∏ _i : ι, ∑' x, g x := by
  haveI : DecidableEq α := Classical.decEq α
  let t : ι → Finset α := fun i => s.image fun η : ι → α => η i
  have hsub : s ⊆ Fintype.piFinset t := by
    intro ξ hξ
    rw [Fintype.mem_piFinset]
    intro i
    exact Finset.mem_image.2 ⟨ξ, hξ, rfl⟩
  have h1 : ∑ ξ ∈ s, ∏ i, g (ξ i) ≤ ∑ ξ ∈ Fintype.piFinset t, ∏ i, g (ξ i) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      fun ξ _ _ => Finset.prod_nonneg fun i _ => hg (ξ i)
  have h2 : ∏ i, ∑ x ∈ t i, g x = ∑ ξ ∈ Fintype.piFinset t, ∏ i, g (ξ i) :=
    Finset.prod_univ_sum t fun _ x => g x
  have h3 : ∏ i, ∑ x ∈ t i, g x ≤ ∏ _i : ι, ∑' x, g x := by
    apply Finset.prod_le_prod
    · intro i _
      exact Finset.sum_nonneg fun x _ => hg x
    · intro i _
      exact hs.sum_le_tsum (t i) fun x _ => hg x
  exact h1.trans (h2.symm.le.trans h3)

theorem UpperTheory.Reformulated.B.Qo1.summable_prod_coord.{u_2, u_3} :
    ∀ {ι : Type u_2} [inst : Fintype ι] [DecidableEq ι] {α : Type u_3} {g : α → ℝ},
    (∀ (x : α), (0 : ℝ) ≤ g x) → Summable g → Summable fun (ξ : ι → α) ↦ ∏ i : ι, g (ξ i) := by
  intro ι _ _ α g hg hs
  have h0 : ∀ ξ : ι → α, 0 ≤ ∏ i, g (ξ i) := fun ξ => Finset.prod_nonneg fun i _ => hg (ξ i)
  exact summable_of_sum_le h0 (sum_prod_le hg hs)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SummandLocalization
section
theorem UpperTheory.Reformulated.B.SummandLocalization.aux1.{u_1, u_2} :
    ∀ {R : Type u_2} [inst : CommRing R] {W : Type u_1} [inst_1 : AddCommGroup W] [inst_2 : _root_.Module R W]
      (S : Submonoid R) (L : Submodule R W) {x y : W},
      x ∈ {x : W | ∃ s ∈ S, s • x ∈ L} → y ∈ {x : W | ∃ s ∈ S, s • x ∈ L} → x + y ∈ {x : W | ∃ s ∈ S, s • x ∈ L} := by
  rintro R _ W _ _ S L x y ⟨s, hs, hx⟩ ⟨t, ht, hy⟩
  refine ⟨s * t, S.mul_mem hs ht, ?_⟩
  rw [smul_add, mul_smul s t y, mul_comm s t, mul_smul t s x]
  exact L.add_mem (L.smul_mem t hx) (L.smul_mem s hy)

theorem UpperTheory.Reformulated.B.SummandLocalization.aux2.{u_1, u_2} :
    ∀ {R : Type u_1} [inst : CommRing R] {W : Type u_2} [inst_1 : AddCommGroup W] [inst_2 : _root_.Module R W]
      (S : Submonoid R) (L : Submodule R W), ∃ s ∈ S, s • (0 : W) ∈ L := by
  intro R _ W _ _ S L
  exact ⟨1, S.one_mem, by rw [smul_zero]; exact L.zero_mem⟩

theorem UpperTheory.Reformulated.B.SummandLocalization.aux3.{u_1, u_2} :
    ∀ {R : Type u_2} [inst : CommRing R] {W : Type u_1} [inst_1 : AddCommGroup W] [inst_2 : _root_.Module R W]
      (S : Submonoid R) (L : Submodule R W) (r : R) {x : W},
      x ∈ {x : W | ∃ s ∈ S, s • x ∈ L} → r • x ∈ {x : W | ∃ s ∈ S, s • x ∈ L} := by
  rintro R _ W _ _ S L r x ⟨s, hs, hx⟩
  refine ⟨s, hs, ?_⟩
  rw [smul_comm]
  exact L.smul_mem r hx

noncomputable def UpperTheory.Reformulated.B.SummandLocalization.locS.{u_1, u_4} :
    {R : Type u_1} →
      [inst : CommRing R] →
        {W : Type u_4} →
          [inst_1 : AddCommGroup W] → [inst_2 : _root_.Module R W] → Submonoid R → Submodule R W → Submodule R W :=
    fun {R : Type u_1} [inst : CommRing R] {W : Type u_4} [inst_1 : AddCommGroup W] [inst_2 : _root_.Module R W]
        (S : Submonoid R) (L : Submodule R W) ↦
      { carrier := {x : W | ∃ s ∈ S, s • x ∈ L}, add_mem' := @UpperTheory.Reformulated.B.SummandLocalization.aux1 R inst W inst_1 inst_2 S L,
        zero_mem' := UpperTheory.Reformulated.B.SummandLocalization.aux2 S L, smul_mem' := UpperTheory.Reformulated.B.SummandLocalization.aux3 S L : Submodule R W }

noncomputable def UpperTheory.Reformulated.B.SummandLocalization.locF :
    {K F W : Type} →
      [inst : Field K] →
        [inst_1 : Field F] →
          [Algebra F K] →
            [inst_3 : AddCommGroup W] →
              [inst_4 : _root_.Module (NumberField.RingOfIntegers K) W] →
                Ideal (NumberField.RingOfIntegers F) →
                  Submodule (NumberField.RingOfIntegers K) W → Submodule (NumberField.RingOfIntegers K) W :=
    fun {K F W : Type} [Field K] [Field F] [Algebra F K] [AddCommGroup W] [_root_.Module (NumberField.RingOfIntegers K) W]
        (𝔭 : Ideal (NumberField.RingOfIntegers F)) (L : Submodule (NumberField.RingOfIntegers K) W) ↦
      UpperTheory.Reformulated.B.SummandLocalization.locS
        (Submonoid.closure
          {s : NumberField.RingOfIntegers K |
            ∃ t ∉ 𝔭,
              (Algebra.algebraMap (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers K) :
                    NumberField.RingOfIntegers F → NumberField.RingOfIntegers K)
                  t =
                s})
        L

noncomputable def UpperTheory.Reformulated.B.SummandLocalization.SummandLoc :
    Prop :=
    ∀ (K F V : Type) [inst : Field K] [NumberField K] [inst_2 : Field F] [NumberField F] [inst_4 : Algebra F K]
      [inst_5 : AddCommGroup V] [inst_6 : _root_.Module K V] [FiniteDimensional K V]
      [inst_8 : _root_.Module (NumberField.RingOfIntegers K) V] [inst_9 : IsScalarTower (NumberField.RingOfIntegers K) K V]
      (X : Submodule K V) (𝔭 : Ideal (NumberField.RingOfIntegers F)),
      𝔭.IsMaximal →
        ∀ (Λ : Submodule (NumberField.RingOfIntegers K) V),
          (∃ (Λ₀ : Submodule (NumberField.RingOfIntegers K) V), Submodule.IsLattice K Λ₀ ∧ UpperTheory.Reformulated.B.SummandLocalization.locF 𝔭 Λ₀ = Λ) →
            ∃ (π : V →ₗ[K] V), (∀ (v : V), (π : V → V) v ∈ X) ∧ (∀ x ∈ X, (π : V → V) x = x) ∧ ∀ y ∈ Λ, (π : V → V) y ∈ Λ

private theorem UpperTheory.Reformulated.B.SummandLocalization.lattice_isLocalizedModule {R K W : Type*} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [AddCommGroup W] [Module K W] [Module R W] [IsScalarTower R K W]
    (M : Submodule R W) (hM : Submodule.span K (M : Set W) = ⊤) :
    IsLocalizedModule (nonZeroDivisors R) M.subtype where
  map_units s := by
    have hs : algebraMap R K s ≠ 0 := (IsLocalization.map_units K s).ne_zero
    rw [Module.End.isUnit_iff]
    have h : ((algebraMap R (Module.End R W)) s : W → W) = fun w => (algebraMap R K s) • w := by
      funext w
      simp
    rw [h]
    exact MulAction.bijective (Units.mk0 _ hs)
  surj y := by
    have hy : y ∈ Submodule.span K (M : Set W) := hM ▸ Submodule.mem_top
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors R) K (M : Set W) y hy
    rw [Submodule.span_eq] at ht
    exact ⟨⟨⟨_, ht⟩, t⟩, rfl⟩
  exists_of_eq h := ⟨1, by rw [Subtype.ext h]⟩

private theorem UpperTheory.Reformulated.B.SummandLocalization.exists_proj {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    (X : Submodule K V) (L : Submodule R V) (hL : Submodule.IsLattice K L) :
    ∃ π : V →ₗ[K] V, (∀ v, π v ∈ X) ∧ (∀ x ∈ X, π x = x) ∧ ∀ y ∈ L, π y ∈ L := by
  let q : V →ₗ[R] V ⧸ X := X.mkQ.restrictScalars R
  let M : Submodule R (V ⧸ X) := L.map q
  have hM : Submodule.span K (M : Set (V ⧸ X)) = ⊤ := by
    have h : (M : Set (V ⧸ X)) = X.mkQ '' (L : Set V) := rfl
    rw [h, ← Submodule.map_span, hL.span_eq_top, Submodule.map_top, Submodule.range_mkQ]
  haveI : Module.Finite R M := Module.Finite.iff_fg.2 (hL.fg.map q)
  haveI : Module.IsTorsionFree R (V ⧸ X) := Module.IsTorsionFree.trans_faithfulSMul R K (V ⧸ X)
  haveI : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  haveI : Module.Projective R M := Module.Flat.projective_of_finitePresentation
  have hsurj : Function.Surjective (q.submoduleMap L) := LinearMap.submoduleMap_surjective q L
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (q.submoduleMap L) LinearMap.id hsurj
  haveI := UpperTheory.Reformulated.B.SummandLocalization.lattice_isLocalizedModule M hM
  have hb : IsBaseChange K M.subtype := IsLocalizedModule.isBaseChange (nonZeroDivisors R) K M.subtype
  let σ : (V ⧸ X) →ₗ[K] V := hb.lift (L.subtype ∘ₗ s)
  have hσ : ∀ m : M, σ m = (s m : V) := fun m => hb.lift_eq (L.subtype ∘ₗ s) m
  have hq : X.mkQ ∘ₗ σ = LinearMap.id := by
    apply LinearMap.ext_on hM
    intro m hm
    have h1 := congrArg Subtype.val (LinearMap.congr_fun hs ⟨m, hm⟩)
    rw [LinearMap.comp_apply, hσ ⟨m, hm⟩]
    exact h1
  refine ⟨LinearMap.id - σ ∘ₗ X.mkQ, fun v => ?_, fun x hx => ?_, fun y hy => ?_⟩
  · rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
    have h1 := LinearMap.congr_fun hq (X.mkQ v)
    rw [LinearMap.comp_apply, LinearMap.id_apply] at h1
    rw [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, h1, sub_self]
  · have h1 : X.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero X).2 hx
    rw [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, h1, map_zero, sub_zero]
  · have h1 := hσ ⟨q y, Submodule.mem_map_of_mem hy⟩
    have h2 : σ (X.mkQ y) ∈ L := by
      have h3 : σ (X.mkQ y) = _ := h1
      rw [h3]
      exact Subtype.property _
    exact L.sub_mem hy h2

theorem UpperTheory.Reformulated.B.SummandLocalization.summand_localization :
    UpperTheory.Reformulated.B.SummandLocalization.SummandLoc := by
  rintro K F V _ _ _ _ _ _ _ _ _ _ X 𝔭 _ Λ ⟨Λ₀, hΛ₀, rfl⟩
  obtain ⟨π, h1, h2, h3⟩ := UpperTheory.Reformulated.B.SummandLocalization.exists_proj X Λ₀ hΛ₀
  refine ⟨π, h1, h2, ?_⟩
  rintro y ⟨s, hs, hy⟩
  refine ⟨s, hs, ?_⟩
  rw [← LinearMap.map_smul_of_tower]
  exact h3 _ hy
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SxLimPt
section
theorem UpperTheory.Reformulated.B.Qg4.sxLimPt :
    ∀ {Λ A R S : Type} [inst : CommRing Λ] [inst_1 : CommRing A] [inst_2 : Algebra Λ A]
    [inst_3 : CommRing R] [inst_4 : Algebra Λ R] (I : Ideal R) [IsAdicComplete I R] (e : S → A) (y : S → R),
    (∀ (N : ℕ),
        ∃ (f : A →ₐ[Λ] R ⧸ I ^ (N + (1 : ℕ))),
          ∀ (s : S),
            (f : A → R ⧸ I ^ (N + (1 : ℕ))) (e s) =
              (Ideal.Quotient.mk (I ^ (N + (1 : ℕ))) : R → R ⧸ I ^ (N + (1 : ℕ))) (y s)) →
      (∀ (N : ℕ) (f f' : A →ₐ[Λ] R ⧸ I ^ (N + (1 : ℕ))),
          (∀ (s : S), (f : A → R ⧸ I ^ (N + (1 : ℕ))) (e s) = (f' : A → R ⧸ I ^ (N + (1 : ℕ))) (e s)) → f = f') →
        ∃ (f : A →ₐ[Λ] R), ∀ (s : S), (f : A → R) (e s) = y s := by
  intro Λ A R S _ _ _ _ _ I _ e y hex huniq
  choose f hf using hex
  have hc : ∀ {m n : ℕ} (hle : m + 1 ≤ n + 1),
      (Ideal.Quotient.factorₐ Λ (Ideal.pow_le_pow_right hle)).comp (f n) = f m := by
    intro m n hle
    refine huniq m _ _ fun s => ?_
    rw [AlgHom.comp_apply, hf, hf]
    rfl
  let g : (n : ℕ) → A →ₐ[Λ] R ⧸ I ^ n := fun n =>
    (Ideal.Quotient.factorₐ Λ (Ideal.pow_le_pow_right (Nat.le_succ n))).comp (f n)
  have hg : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorₐ Λ (Ideal.pow_le_pow_right hle)).comp (g n) = g m := by
    intro m n hle
    refine AlgHom.ext fun a => ?_
    simp only [g, ← hc (Nat.succ_le_succ hle), AlgHom.comp_apply]
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (f n a)
    rw [← hr]
    rfl
  refine ⟨IsAdicComplete.liftAlgHom I g hg, fun s => ?_⟩
  have key : (fun s => IsAdicComplete.liftAlgHom I g hg (e s)) = y := by
    apply IsHausdorff.funext' I
    intro n t
    have h1 := IsAdicComplete.mk_liftAlgHom I g hg n (e t)
    refine h1.trans ?_
    simp only [g, AlgHom.comp_apply, hf]
    rfl
  exact congrFun key s
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SymmetricShiftIsUnit
section
open Matrix

private lemma UpperTheory.symmetric_shift_isUnit {K : Type} [Field K] {κ : Type} [Fintype κ] [DecidableEq κ]
    (A C : Matrix κ κ K) (hker : ∀ x : κ → K, A *ᵥ x = 0 → C *ᵥ x = 0 → x = 0)
    (hs : Aᵀ * C = Cᵀ * A) : ∃ X : Matrix κ κ K, X.IsSymm ∧ IsUnit (A + X * C) := by
  obtain ⟨V, U, s, hV, hU, heq⟩ := exists_rank_normal_form A
  obtain ⟨W, hVW, hWV⟩ : ∃ W, V * W = 1 ∧ W * V = 1 := isUnit_iff_exists.1 hV
  obtain ⟨T, hUT⟩ : ∃ T, U * T = 1 := hU.exists_right_inv
  have hPP : (V * A * U) * (V * A * U) = V * A * U := by
    rw [heq, submatrix_mul_equiv]; simp [fromBlocks_multiply]
  have hPt : (V * A * U)ᵀ = V * A * U := by
    rw [heq, transpose_submatrix]; simp [fromBlocks_transpose]
  set P := V * A * U with hP
  have h1 : V * A = P * T := by rw [hP, Matrix.mul_assoc (V * A), hUT, Matrix.mul_one]
  have h2 : P * Wᵀ = Uᵀ * Aᵀ := by
    rw [← hPt, ← transpose_mul, ← transpose_mul, hP, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hWV,
      Matrix.one_mul]
  refine ⟨W * (1 - P) * Wᵀ, ?_, ?_⟩
  · simp [Matrix.IsSymm, transpose_mul, transpose_sub, hPt, Matrix.mul_assoc]
  · refine mulVec_injective_iff_isUnit.1 ?_
    rw [← coe_mulVecLin, ← LinearMap.ker_eq_bot]
    refine ker_mulVecLin_eq_bot_iff.2 fun y hy => ?_
    set M := A + W * (1 - P) * Wᵀ * C with hM
    have e1 : V * M = P * T + (1 - P) * (Wᵀ * C) := by
      rw [hM, Matrix.mul_add, h1]
      simp only [← Matrix.mul_assoc, hVW, Matrix.one_mul]
    have e2 : W * P * V * M = A := by
      rw [Matrix.mul_assoc _ V, e1, Matrix.mul_assoc W, Matrix.mul_add, ← Matrix.mul_assoc P P,
        ← Matrix.mul_assoc P (1 - P), Matrix.mul_sub, hPP, Matrix.mul_one, sub_self,
        Matrix.zero_mul, add_zero, ← h1, ← Matrix.mul_assoc, hWV, Matrix.one_mul]
    have hA : A *ᵥ y = 0 := by rw [← e2, ← mulVec_mulVec, hy, mulVec_zero]
    have e3 : C = Vᵀ * V * M - Vᵀ * V * A + Vᵀ * (Uᵀ * Cᵀ) * A := by
      have : Vᵀ * Wᵀ = 1 := by rw [← transpose_mul, hWV, transpose_one]
      rw [Matrix.mul_assoc _ V, Matrix.mul_assoc _ V, e1, h1, Matrix.mul_assoc _ (Uᵀ * Cᵀ),
        Matrix.mul_assoc Uᵀ, ← hs, ← Matrix.mul_assoc Uᵀ, ← h2, ← Matrix.mul_sub,
        ← Matrix.mul_add, add_sub_cancel_left, Matrix.mul_assoc P, ← Matrix.add_mul,
        sub_add_cancel, Matrix.one_mul, ← Matrix.mul_assoc, this, Matrix.one_mul]
    refine hker y hA ?_
    rw [e3, add_mulVec, sub_mulVec, ← mulVec_mulVec _ _ M, ← mulVec_mulVec _ _ A,
      ← mulVec_mulVec _ _ A, hy, hA]
    simp

private lemma UpperTheory.matrix_ext_bilinear {K : Type} [Field K] {κ : Type} [Fintype κ] [DecidableEq κ]
    {M N : Matrix κ κ K} (h : ∀ x y : κ → K, x ⬝ᵥ M *ᵥ y = x ⬝ᵥ N *ᵥ y) : M = N := by
  ext i j
  simpa using h (Pi.single i 1) (Pi.single j 1)

private lemma UpperTheory.dot_mulVec_eq {K : Type} [Field K] {κ : Type} [Fintype κ]
    (M N : Matrix κ κ K) (x y : κ → K) : (M *ᵥ x) ⬝ᵥ (N *ᵥ y) = x ⬝ᵥ (Mᵀ * N) *ᵥ y := by
  rw [← mulVec_mulVec, dotProduct_mulVec x, vecMul_transpose]

theorem UpperTheory.symplectic_generation :
    ∀ (K : Type) [Field K] (κ : Type) [Fintype κ] [DecidableEq κ]
        (P : ((κ → K) × (κ → K) → (κ → K) × (κ → K)) → Prop),
        (∀ f g, P f → P g → P (f ∘ g)) →
        P (fun w => (w.2, -w.1)) →
        (∀ S : Matrix κ κ K, S.IsSymm → P (fun w => (w.1, w.2 + S.mulVec w.1))) →
        (∀ A A' : Matrix κ κ K, A' * A = 1 → P (fun w => (A.mulVec w.1, A'.transpose.mulVec w.2))) →
        ∀ g : (κ → K) × (κ → K) →ₗ[K] (κ → K) × (κ → K),
          (∀ w w', dotProduct (g w).1 (g w').2 - dotProduct (g w').1 (g w).2 = dotProduct w.1 w'.2 - dotProduct w'.1 w.2) →
          P g := by
  intro K _ κ _ _ P hcomp hJ hL hD g hg
  have hU : ∀ S : Matrix κ κ K, S.IsSymm → P (fun w => (w.1 + S *ᵥ w.2, w.2)) := by
    intro S hS
    convert hcomp _ _ hJ (hcomp _ _ (hL _ hS.neg) (hcomp _ _ hJ (hcomp _ _ hJ hJ))) using 1
    funext w
    simp [neg_mulVec, mulVec_neg]
  have hinv : ∀ A B C D : Matrix κ κ K, IsUnit A → Aᵀ * C = Cᵀ * A → Bᵀ * D = Dᵀ * B →
      Aᵀ * D - Cᵀ * B = 1 →
      P (fun w => (A *ᵥ w.1 + B *ᵥ w.2, C *ᵥ w.1 + D *ᵥ w.2)) := by
    intro A B C D hA h1 h2 h3
    obtain ⟨E, hAE, hEA⟩ : ∃ E, A * E = 1 ∧ E * A = 1 := isUnit_iff_exists.1 hA
    have hT : Eᵀ * Aᵀ = 1 := by rw [← transpose_mul, hAE, transpose_one]
    have s1 : Eᵀ * Cᵀ = C * E := by
      calc Eᵀ * Cᵀ = Eᵀ * (Cᵀ * A) * E := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc, hAE, Matrix.mul_one]
        _ = C * E := by rw [← h1, ← Matrix.mul_assoc, hT, Matrix.one_mul]
    have hDe : Eᵀ = D - C * E * B := by
      rw [← Matrix.mul_one Eᵀ, ← h3, Matrix.mul_sub, ← Matrix.mul_assoc, hT, Matrix.one_mul,
        ← Matrix.mul_assoc, s1]
    have hEe : E = Dᵀ - Bᵀ * (C * E) := by
      rw [← s1]
      simpa [transpose_sub, transpose_mul] using congrArg transpose hDe
    have s2 : (E * B).IsSymm := by
      rw [Matrix.IsSymm, transpose_mul, hDe]
      conv_rhs => rw [hEe]
      rw [Matrix.mul_sub, Matrix.sub_mul, h2]
      simp only [Matrix.mul_assoc]
    have s3 : (C * E).IsSymm := by rw [Matrix.IsSymm, transpose_mul, s1]
    convert hcomp _ _ (hL _ s3) (hcomp _ _ (hD A E hEA) (hU _ s2)) using 1
    funext w
    have a1 : A * (E * B) = B := by rw [← Matrix.mul_assoc, hAE, Matrix.one_mul]
    have a2 : C * E * A = C := by rw [Matrix.mul_assoc, hEA, Matrix.mul_one]
    simp only [Function.comp, mulVec_add, mulVec_mulVec, a1, a2, hDe, sub_mulVec, Prod.mk.injEq,
      true_and]
    abel
  obtain ⟨A, B, C, D, hw⟩ : ∃ A B C D : Matrix κ κ K,
      ∀ w, g w = (A *ᵥ w.1 + B *ᵥ w.2, C *ᵥ w.1 + D *ᵥ w.2) := by
    refine ⟨LinearMap.toMatrix' (LinearMap.fst K _ _ ∘ₗ g ∘ₗ LinearMap.inl K _ _),
      LinearMap.toMatrix' (LinearMap.fst K _ _ ∘ₗ g ∘ₗ LinearMap.inr K _ _),
      LinearMap.toMatrix' (LinearMap.snd K _ _ ∘ₗ g ∘ₗ LinearMap.inl K _ _),
      LinearMap.toMatrix' (LinearMap.snd K _ _ ∘ₗ g ∘ₗ LinearMap.inr K _ _), fun w => ?_⟩
    simp only [LinearMap.toMatrix'_mulVec]
    have : g w = g (w.1, 0) + g (0, w.2) := by rw [← map_add]; simp
    rw [this]
    rfl
  simp only [hw] at hg
  have h1 : Aᵀ * C = Cᵀ * A := UpperTheory.matrix_ext_bilinear fun x y => by
    have := hg (x, 0) (y, 0)
    simp only [mulVec_zero, add_zero, dotProduct_zero, sub_self] at this
    rw [← UpperTheory.dot_mulVec_eq, ← UpperTheory.dot_mulVec_eq, dotProduct_comm (C *ᵥ x)]
    exact sub_eq_zero.1 this
  have h2 : Bᵀ * D = Dᵀ * B := UpperTheory.matrix_ext_bilinear fun x y => by
    have := hg (0, x) (0, y)
    simp only [mulVec_zero, zero_add, zero_dotProduct, sub_self] at this
    rw [← UpperTheory.dot_mulVec_eq, ← UpperTheory.dot_mulVec_eq, dotProduct_comm (D *ᵥ x)]
    exact sub_eq_zero.1 this
  have h3 : Aᵀ * D - Cᵀ * B = 1 := UpperTheory.matrix_ext_bilinear fun x y => by
    have := hg (x, 0) (0, y)
    simp only [mulVec_zero, zero_add, add_zero, zero_dotProduct, sub_zero] at this
    rw [sub_mulVec, dotProduct_sub, ← UpperTheory.dot_mulVec_eq, ← UpperTheory.dot_mulVec_eq,
      dotProduct_comm (C *ᵥ x), one_mulVec]
    exact this
  have h4 : Dᵀ * A - Bᵀ * C = 1 := by
    simpa [transpose_sub, transpose_mul] using congrArg transpose h3
  obtain ⟨X, hX, hu⟩ := UpperTheory.symmetric_shift_isUnit A C (fun x hA hC => by
    rw [← one_mulVec x, ← h4, sub_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hA, hC]
    simp) h1
  have key := hinv (A + X * C) (B + X * D) C D hu
    (by simp only [transpose_add, transpose_mul, hX.eq, Matrix.add_mul, Matrix.mul_add, h1,
          Matrix.mul_assoc])
    (by simp only [transpose_add, transpose_mul, hX.eq, Matrix.add_mul, Matrix.mul_add, h2,
          Matrix.mul_assoc])
    (by
      simp only [transpose_add, transpose_mul, hX.eq, Matrix.add_mul, Matrix.mul_add,
        Matrix.mul_assoc, ← h3]
      abel)
  convert hcomp _ _ (hU _ hX.neg) key using 1
  funext w
  simp only [hw, Function.comp, add_mulVec, neg_mulVec, mulVec_add, mulVec_mulVec, Matrix.neg_mul,
    Prod.mk.injEq, and_true]
  abel
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.UpperTriangularMul
section
theorem UpperTheory.Reformulated.B.Qe38.upper_triangular_mul :
    ∀ {K : Type} [inst : Field K] {n : ℕ}
    (U T : Matrix (Fin n) (Fin n) K),
    (∀ (i j : Fin n), j < i → U i j = (0 : K)) →
      (∀ (i j : Fin n), j < i → T i j = (0 : K)) → ∀ (i j : Fin n), j < i → (U * T) i j = (0 : K) := by
  intro K _ n U T hU hT i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge k i with hk | hk
  · rw [hU i k hk, zero_mul]
  · rw [hT k j (lt_of_lt_of_le hij hk), mul_zero]
end

