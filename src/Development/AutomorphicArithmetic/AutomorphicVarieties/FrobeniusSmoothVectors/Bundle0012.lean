import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0003

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.TanFinite
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

section
variable {O : Type} [CommRing O] [IsLocalRing O] {R : Type} [CommRing R] [Algebra O R] [IsCO O R]

private theorem hom_eq_res (g : R →ₐ[O] ResidueField O) (x : R) : g x = res O R x := by
  have hsurj : Function.Surjective g := by
    intro y
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
    exact ⟨algebraMap O R a, by rw [g.commutes, IsLocalRing.ResidueField.algebraMap_eq]⟩
  have hker : RingHom.ker (g : R →+* ResidueField O) = maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hsurj)
  obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) x
  have h1 : g (x - algebraMap O R a) = 0 := by
    have hm : x - algebraMap O R a ∈ RingHom.ker (g : R →+* ResidueField O) := by
      rw [hker]
      exact ha
    exact (RingHom.mem_ker).1 hm
  have h2 : res O R (x - algebraMap O R a) = 0 := (res_eq_zero_iff O R _).2 ha
  rw [map_sub, sub_eq_zero] at h1 h2
  rw [h1, h2, AlgHom.commutes, AlgHom.commutes]

private theorem tan_mul (D : Tan O R) (f g : R) :
    D.1 (f * g) = res O R f * D.1 g + res O R g * D.1 f := D.2 f g

private theorem tan_one (D : Tan O R) : D.1 1 = 0 := by
  simpa using tan_mul D 1 1

private theorem tan_alg (D : Tan O R) (a : O) : D.1 (algebraMap O R a) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, tan_one, smul_zero]

private theorem tan_finite : Module.Finite (ResidueField O) (Tan O R) := by
  classical
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (maximalIdeal R) : (maximalIdeal R).FG)
  let φ : Tan O R →ₗ[ResidueField O] (s → ResidueField O) :=
    { toFun := fun D i => D.1 (i : R)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective φ ((injective_iff_map_eq_zero φ).2 fun D hD => ?_)
  have h0 : ∀ i ∈ s, D.1 i = 0 := fun i hi => congrFun hD ⟨i, hi⟩
  have hm : ∀ y ∈ maximalIdeal R, D.1 y = 0 := by
    intro y hy
    rw [← hs] at hy
    induction hy using Submodule.span_induction with
    | mem z hz => exact h0 z hz
    | zero => exact map_zero _
    | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
    | smul c z hz ih =>
      have hz' : z ∈ maximalIdeal R := by
        rw [← hs]
        exact hz
      rw [smul_eq_mul, tan_mul, ih, (res_eq_zero_iff O R z).2 hz', mul_zero, zero_mul, add_zero]
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) x
  have h := hm _ ha
  rw [map_sub, tan_alg, sub_zero] at h
  exact h

private noncomputable def tanEquiv : (R →ₐ[O] DualNumber (ResidueField O)) ≃ Tan O R where
  toFun f := ⟨{ toFun := fun x => (f x).snd
                map_add' := fun x y => by simp
                map_smul' := fun a x => by simp }, fun x y => by
    have h : ∀ z, (f z).fst = res O R z := fun z =>
      hom_eq_res ((TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).comp f) z
    show (f (x * y)).snd = res O R x • (f y).snd + res O R y • (f x).snd
    rw [map_mul, DualNumber.snd_mul, h, h, smul_eq_mul, smul_eq_mul, mul_comm (f x).snd]⟩
  invFun D :=
    { toFun := fun x => TrivSqZeroExt.inl (res O R x) + TrivSqZeroExt.inr (D.1 x)
      map_one' := by ext <;> simp [tan_one]
      map_mul' := fun x y => by ext <;> simp [tan_mul, mul_comm]
      map_zero' := by ext <;> simp
      map_add' := fun x y => by ext <;> simp
      commutes' := fun a => by
        ext
        · simp [TrivSqZeroExt.algebraMap_eq_inl']
        · simp [tan_alg, TrivSqZeroExt.algebraMap_eq_inl'] }
  left_inv f := by
    have h : ∀ z, (f z).fst = res O R z := fun z =>
      hom_eq_res ((TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).comp f) z
    refine AlgHom.ext fun x => ?_
    ext <;> simp [h]
  right_inv D := Subtype.ext (LinearMap.ext fun x => by simp)

end

theorem UpperTheory.V.Fr.pr_tan :
    ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R], Module.Finite (ResidueField O) (Tan O R) ∧ Nat.card (R →ₐ[O] (DualNumber (ResidueField O))) = Nat.card (Tan O R) := by
  intro O _ _ R _ _ _
  exact ⟨tan_finite, Nat.card_congr tanEquiv⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.TrMap
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

section

variable {K G W W' V : Type} [Field K] [Group G] [TopologicalSpace G] [AddCommGroup W] [Module K W]
  [AddCommGroup W'] [Module K W'] {Gv : V → Type} [∀ v, Group (Gv v)] (loc : ∀ v, Gv v →* G)

private def trE (G V : Type) (e : W ≃ₗ[K] W') : ((G → W) × (V → W)) ≃ₗ[K] ((G → W') × (V → W')) :=
  (LinearEquiv.piCongrRight fun _ => e).prodCongr (LinearEquiv.piCongrRight fun _ => e)

private theorem trZ (e : W ≃ₗ[K] W') (ρ : Representation K G W) (ρ' : Representation K G W')
    (b : V → Submodule K W) (b' : V → Submodule K W') (h : ∀ g x, ρ' g (e x) = e (ρ g x))
    (hb : ∀ v x, e x ∈ b' v ↔ x ∈ b v) (x : (G → W) × (V → W)) :
    trE G V e x ∈ Z1C loc ρ' b' ↔ x ∈ Z1C loc ρ b := by
  have h1 : (trE G V e x).1 = e ∘ x.1 := rfl
  have h2 : (trE G V e x).2 = e ∘ x.2 := rfl
  simp only [Z1C, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
  rw [h1, h2]
  simp only [Function.comp_apply]
  apply and_congr
  · constructor
    · intro hl
      exact IsLocallyConstant.desc _ _ hl e.injective
    · intro hl
      exact hl.comp e
  apply and_congr
  · apply forall_congr'
    intro s
    apply forall_congr'
    intro t
    rw [h, ← map_add]
    exact e.injective.eq_iff
  · apply forall_congr'
    intro v
    apply forall_congr'
    intro s
    rw [h, ← map_sub, ← map_sub]
    exact hb v _

omit [TopologicalSpace G] in
private theorem trB (e : W ≃ₗ[K] W') (ρ : Representation K G W) (ρ' : Representation K G W')
    (b : V → Submodule K W) (b' : V → Submodule K W') (h : ∀ g x, ρ' g (e x) = e (ρ g x))
    (hb : ∀ v x, e x ∈ b' v ↔ x ∈ b v) (x : (G → W) × (V → W)) :
    trE G V e x ∈ continuousCoboundaries1 ρ' b' ↔ x ∈ continuousCoboundaries1 ρ b := by
  have h1 : (trE G V e x).1 = e ∘ x.1 := rfl
  have h2 : (trE G V e x).2 = e ∘ x.2 := rfl
  simp only [continuousCoboundaries1, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
  rw [h1, h2]
  simp only [Function.comp_apply]
  constructor
  · rintro ⟨X, hX1, hX2⟩
    refine ⟨e.symm X, fun s => ?_, fun v => ?_⟩
    · apply e.injective
      rw [map_sub, ← h, e.apply_symm_apply]
      exact hX1 s
    · rw [← hb v, map_sub, e.apply_symm_apply]
      exact hX2 v
  · rintro ⟨X, hX1, hX2⟩
    refine ⟨e X, fun s => ?_, fun v => ?_⟩
    · rw [hX1 s, map_sub, h]
    · rw [← map_sub, hb v]
      exact hX2 v

private theorem trMap (e : W ≃ₗ[K] W') (ρ : Representation K G W) (ρ' : Representation K G W')
    (b : V → Submodule K W) (b' : V → Submodule K W') (h : ∀ g x, ρ' g (e x) = e (ρ g x))
    (hb : ∀ v x, e x ∈ b' v ↔ x ∈ b v) :
    (Z1C loc ρ b).map (trE G V e : _ →ₗ[K] _) = Z1C loc ρ' b' := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (trZ loc e ρ ρ' b b' h hb x).mpr hx
  · intro hy
    refine ⟨(trE G V e).symm y, ?_, ?_⟩
    · exact (trZ loc e ρ ρ' b b' h hb _).mp (by simpa using hy)
    · simp

private theorem trH (e : W ≃ₗ[K] W') (ρ : Representation K G W) (ρ' : Representation K G W')
    (b : V → Submodule K W) (b' : V → Submodule K W') (h : ∀ g x, ρ' g (e x) = e (ρ g x))
    (hb : ∀ v x, e x ∈ b' v ↔ x ∈ b v) :
    Module.rank K (H1C loc ρ' b') = Module.rank K (H1C loc ρ b) := by
  let E : Z1C loc ρ b ≃ₗ[K] Z1C loc ρ' b' :=
    ((trE G V e).submoduleMap (Z1C loc ρ b)).trans (LinearEquiv.ofEq _ _ (trMap loc e ρ ρ' b b' h hb))
  have hE : ∀ z, (E z : (G → W') × (V → W')) = trE G V e z := fun z => rfl
  symm
  refine LinearEquiv.rank_eq (Submodule.Quotient.equiv _ _ E ?_)
  ext y
  rw [Submodule.mem_map_equiv]
  simp only [Submodule.mem_comap, Submodule.subtype_apply]
  rw [← trB e ρ ρ' b b' h hb, ← hE, E.apply_symm_apply]

end

theorem UpperTheory.V.Fr.n4ch :
    ∀ {k K G V : Type} [Field k] [Field K] (f : k →+* K) [Group G] [TopologicalSpace G] [CompactSpace G] {Gv : V → Type} [∀ v, Group (Gv v)] [Finite V] (loc : ∀ v, Gv v →* G) (χ : G →* kˣ) (b : V → Submodule k k) (b' : V → Submodule K K), (∀ v, (b v = ⊥ ∧ b' v = ⊥) ∨ (b v = ⊤ ∧ b' v = ⊤)) → Z1C loc (chRep ((Units.map f.toMonoidHom).comp χ)) b' = Submodule.span K ((fun y : (G → k) × (V → k) => (f ∘ y.1, f ∘ y.2)) '' (Z1C loc (chRep χ) b : Set ((G → k) × (V → k)))) ∧ Module.rank K (H1C loc (chRep ((Units.map f.toMonoidHom).comp χ)) b') = Module.rank k (H1C loc (chRep χ) b) := by
  intro k K G V _ _ f _ _ _ Gv _ _ loc χ b b' hbb
  letI : Algebra k K := f.toAlgebra
  let ρ' : Representation K G (TensorProduct k K k) :=
    { toFun := fun g => ((chRep χ) g).baseChange K
      map_one' := by
        show ((chRep χ) 1).baseChange K = 1
        rw [map_one]
        exact LinearMap.baseChange_one k k
      map_mul' := fun g g' => by
        show ((chRep χ) (g * g')).baseChange K = ((chRep χ) g).baseChange K * ((chRep χ) g').baseChange K
        rw [map_mul]
        exact LinearMap.baseChange_mul _ _ }
  obtain ⟨hZ, hH⟩ := n4 loc (chRep χ) b ρ' (fun g => rfl)
  let e := TensorProduct.AlgebraTensorModule.rid k K K
  have hρ : ∀ g x, (chRep ((Units.map f.toMonoidHom).comp χ)) g (e x) = e (ρ' g x) := by
    intro g x
    show (((Units.map f.toMonoidHom).comp χ) g : K) • e x = e (((chRep χ) g).baseChange K x)
    have hc : (chRep χ) g = ((χ g : kˣ) : k) • LinearMap.id := rfl
    rw [hc, LinearMap.baseChange_smul, LinearMap.baseChange_id, LinearMap.smul_apply, LinearMap.id_apply,
      ← algebraMap_smul K ((χ g : kˣ) : k) x, map_smul]
    simp [RingHom.algebraMap_toAlgebra]
  have hb : ∀ v x, e x ∈ b' v ↔ x ∈ (b v).baseChange K := by
    intro v x
    rcases hbb v with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2, Submodule.baseChange_bot, Submodule.mem_bot, Submodule.mem_bot, LinearEquiv.map_eq_zero_iff]
    · rw [h1, h2, Submodule.baseChange_top]
      simp
  have hM := trMap loc e ρ' (chRep ((Units.map f.toMonoidHom).comp χ)) (fun v => (b v).baseChange K) b' hρ hb
  refine ⟨?_, ?_⟩
  · rw [← hM, hZ, Submodule.map_span, ← Set.image_comp]
    congr 2
    funext y
    refine Prod.ext (funext fun g => ?_) (funext fun v => ?_)
    · show e (1 ⊗ₜ[k] y.1 g) = f (y.1 g)
      simp [e, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
    · show e (1 ⊗ₜ[k] y.2 v) = f (y.2 v)
      simp [e, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  · rw [trH loc e ρ' (chRep ((Units.map f.toMonoidHom).comp χ)) _ b' hρ hb, hH]
end

