import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0011
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0015
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0008
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0006

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsLiftFactorCompactSubalgebra
section
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.HV UpperTheory.V.Base IsLocalRing

private theorem continuous_linear_functional_comp {l : ℕ} [Fact l.Prime] {X V : Type} [TopologicalSpace X] [AddCommGroup V] [Module ℚ_[l] V]
    (φ : V →ₗ[ℚ_[l]] ℚ_[l]) (f : X → V) (hf : QCont l f) : Continuous fun x => φ (f x) := by
  letI : TopologicalSpace V := moduleTopology ℚ_[l] V
  haveI : IsModuleTopology ℚ_[l] V := ⟨rfl⟩
  exact (IsModuleTopology.continuous_of_linearMap φ).comp hf

private theorem continuous_bounded_lattice {l : ℕ} [Fact l.Prime] {X V : Type} [TopologicalSpace X] [CompactSpace X] [AddCommGroup V]
    [Module ℚ_[l] V] [Module.Finite ℚ_[l] V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V]
    (f : X → V) (hf : QCont l f) : ∃ M : Submodule ℤ_[l] V, M.FG ∧ ∀ g, f g ∈ M := by
  let e := Module.finBasis ℚ_[l] V
  have h1 : Continuous fun g => fun i => e.coord i (f g) := continuous_pi fun i => continuous_linear_functional_comp _ f hf
  obtain ⟨C, hC⟩ := (isCompact_range h1).isBounded.exists_norm_le
  obtain ⟨c, hc0, hc⟩ : ∃ c : ℚ_[l], c ≠ 0 ∧ C ≤ ‖c‖ := by
    obtain ⟨c, hc⟩ := NormedField.exists_lt_norm ℚ_[l] (max C 0)
    exact ⟨c, norm_pos_iff.1 (lt_of_le_of_lt (le_max_right _ _) hc), ((le_max_left _ _).trans hc.le)⟩
  refine ⟨Submodule.span ℤ_[l] (Set.range fun i => c • e i), Submodule.fg_span (Set.finite_range _), fun g => ?_⟩
  rw [← e.sum_repr (f g)]
  refine sum_mem fun i _ => ?_
  have h2 : ‖e.repr (f g) i / c‖ ≤ 1 := by
    rw [norm_div, div_le_one (norm_pos_iff.2 hc0)]
    exact ((norm_le_pi_norm (fun i => e.coord i (f g)) i).trans (hC _ ⟨g, rfl⟩)).trans hc
  let z : ℤ_[l] := ⟨_, h2⟩
  have h3 : e.repr (f g) i • e i = z • c • e i := by
    rw [← algebraMap_smul ℚ_[l] z, smul_smul]
    congr 1
    exact (div_mul_cancel₀ _ hc0).symm
  rw [h3]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

private theorem eventually_congruent_mod_l_pow {l : ℕ} [Fact l.Prime] {X V M : Type} [TopologicalSpace X] [AddCommGroup V]
    [Module ℚ_[l] V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] [AddCommGroup M] [Module ℤ_[l] M]
    [Module.Finite ℤ_[l] M] (j : M →ₗ[ℤ_[l]] V) (hj : Function.Injective j)
    (f : X → M) (hf : QCont l fun g => j (f g)) (N : ℕ) (g₀ : X) :
    ∀ᶠ g in nhds g₀, ∃ m : M, f g - f g₀ = (l : ℤ_[l]) ^ N • m := by
  haveI : Module.IsTorsionFree ℤ_[l] V := Module.IsTorsionFree.trans_faithfulSMul ℤ_[l] ℚ_[l] V
  haveI : Module.IsTorsionFree ℤ_[l] M := Function.Injective.moduleIsTorsionFree j hj (map_smul j)
  let b := Module.finBasis ℤ_[l] M
  have h1 : LinearIndependent ℚ_[l] (j ∘ b) :=
    (LinearIndependent.iff_fractionRing ℤ_[l] ℚ_[l]).1 (b.linearIndependent.map' j (LinearMap.ker_eq_bot.2 hj))
  obtain ⟨ψ, hψ⟩ := (Finsupp.linearCombination ℚ_[l] (j ∘ b)).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 h1)
  have h2 : ∀ m i, ψ (j m) i = (b.repr m i : ℚ_[l]) := by
    intro m i
    have h3 : j m = Finsupp.linearCombination ℚ_[l] (j ∘ b)
        ((Finsupp.linearEquivFunOnFinite ℚ_[l] ℚ_[l] _).symm fun i => algebraMap ℤ_[l] ℚ_[l] (b.repr m i)) := by
      rw [Finsupp.linearCombination_eq_fintype_linearCombination_apply, Fintype.linearCombination_apply]
      conv_lhs => rw [← b.sum_repr m, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, algebraMap_smul]
      rfl
    rw [h3, ← LinearMap.comp_apply, hψ]
    rfl
  have h4 : ∀ i, ∀ᶠ g in nhds g₀, ‖b.repr (f g - f g₀) i‖ ≤ (l : ℝ) ^ (-N : ℤ) := by
    intro i
    have h5 : Continuous fun g => ψ (j (f g)) i := continuous_linear_functional_comp ((Finsupp.lapply i).comp ψ) _ hf
    have hp : (0 : ℝ) < (l : ℝ) ^ (-N : ℤ) := zpow_pos (Nat.cast_pos.2 (Fact.out : l.Prime).pos) _
    filter_upwards [Metric.tendsto_nhds.1 (h5.tendsto g₀) _ hp] with g hg
    rw [dist_eq_norm, h2, h2] at hg
    rw [map_sub, Finsupp.sub_apply]
    exact hg.le
  filter_upwards [Filter.eventually_all.2 h4] with g hg
  choose c hc using fun i => Ideal.mem_span_singleton.1 ((PadicInt.norm_le_pow_iff_mem_span_pow _ N).1 (hg i))
  refine ⟨∑ i, c i • b i, ?_⟩
  rw [← b.sum_repr (f g - f g₀), Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [hc, mul_smul]

private theorem isIntegral_of_nilpotent_kernel {O B E : Type} [CommRing O] [CommRing B] [CommRing E] [Algebra O B] [Algebra O E]
    (π : B →ₐ[O] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (a : B) (ha : IsIntegral O (π a)) : IsIntegral O a := by
  obtain ⟨p, hp, hpe⟩ := ha
  rw [← Polynomial.aeval_def, Polynomial.aeval_algHom_apply] at hpe
  obtain ⟨n, hn⟩ := hπ _ hpe
  exact ⟨p ^ n, hp.pow n, by rw [← Polynomial.aeval_def, map_pow, hn]⟩

private theorem isUnit_of_nilpotent_kernel {O C A : Type} [CommRing O] [CommRing C] [CommRing A] [Algebra O C] [Algebra O A]
    [Algebra.IsIntegral O A] (π : C →ₐ[O] A) (hπ : ∀ a, π a = 0 → IsNilpotent a) (a : C) (ha : IsUnit (π a)) :
    IsUnit a := by
  obtain ⟨u, hu⟩ := ha
  obtain ⟨p, hp, hpe⟩ := Algebra.IsIntegral.isIntegral (R := O) ((u⁻¹ : Aˣ) : A)
  letI : Invertible ((u⁻¹ : Aˣ) : A) := Units.invertible _
  have h1 := (Polynomial.eval₂_reverse_eq_zero_iff (algebraMap O A) ((u⁻¹ : Aˣ) : A) p).2 hpe
  rw [invOf_units, inv_inv, hu, ← Polynomial.aeval_def, Polynomial.aeval_algHom_apply] at h1
  have h4 : p.reverse = Polynomial.X * p.reverse.divX + Polynomial.C 1 := by
    conv_lhs => rw [← Polynomial.X_mul_divX_add p.reverse]
    rw [Polynomial.coeff_zero_reverse, hp.leadingCoeff]
  have h5 := (hπ _ h1).isUnit_sub_one
  rw [h4, map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C, map_one, add_sub_cancel_right] at h5
  exact isUnit_of_mul_isUnit_left h5

private theorem complete_of_nilpotent_kernel_finite {O C A : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] [CommRing C] [CommRing A] [Algebra O C] [Algebra O A] [IsCO O A]
    [Algebra.IsIntegral O A] [Module.Finite O C] (π : C →ₐ[O] A) (hπ : ∀ a, π a = 0 → IsNilpotent a) : IsCO O C := by
  haveI : Nontrivial C := π.toRingHom.domain_nontrivial
  haveI : IsLocalRing C := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (π a) with h | h
    · exact Or.inl (isUnit_of_nilpotent_kernel π hπ a h)
    · exact Or.inr (isUnit_of_nilpotent_kernel π hπ _ (by rwa [map_sub, map_one]))
  refine co_finite O O C fun x => ?_
  obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) (π x)
  refine ⟨a, fun h => ha ?_⟩
  have := h.map π
  rwa [map_sub, AlgHom.commutes] at this

theorem UpperTheory.V.Loc.exists_lift_factor_compact_subalgebra :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] {Γ ι : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [Fintype ι] [DecidableEq ι] (rbar : Γ →* Matrix ι ι (ResidueField O)) (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (ρ : Lift O rbar R) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower O E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (x : R →ₐ[O] E) (r : Γ →* Matrix ι ι B), (∀ g a b, π (r g a b) = x (ρ.hom g a b)) → (∀ a b, QCont l fun g => r g a b) → ∃ (C : Subalgebra O B) (_ : IsCO O ↥C) (ρ' : Lift O rbar ↥C), ∀ g a b, (ρ'.hom g a b : B) = r g a b := by
  intro l _ O _ _ _ _ _ _ _ Γ ι _ _ _ _ _ _ rbar R _ _ _ ρ E _ _ _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ x r hr hc
  classical
  have hint : ∀ a, IsIntegral O (x a) := fun a =>
    (((ptCont (l := l) R E x).2 (Field.toIsField E)).1 a).tower_top
  let πO : B →ₐ[O] E := π.restrictScalars O
  let S : Set B := Set.range fun s : Γ × ι × ι => r s.1 s.2.1 s.2.2
  let C : Subalgebra O B := Algebra.adjoin O S
  have hSC : ∀ g a b, r g a b ∈ C := fun g a b => Algebra.subset_adjoin ⟨(g, a, b), rfl⟩
  have hCx : ∀ c ∈ C, πO c ∈ x.range := fun c hc =>
    (Algebra.adjoin_le (S := x.range.comap πO) (by
      rintro _ ⟨⟨g, a, b⟩, rfl⟩
      exact ⟨ρ.hom g a b, (hr g a b).symm⟩)) hc
  haveI hfin : Module.Finite O C := by
    choose M hM hMr using fun p : ι × ι => continuous_bounded_lattice _ (hc p.1 p.2)
    have h1 : (Submodule.span ℤ_[l] S).FG := by
      refine Submodule.FG.of_le (Submodule.fg_iSup M hM) (Submodule.span_le.2 ?_)
      rintro _ ⟨⟨g, a, b⟩, rfl⟩
      exact Submodule.mem_iSup_of_mem (a, b) (hMr (a, b) g)
    obtain ⟨T, hT⟩ := h1
    have h2 : Submodule.span O (T : Set B) = Submodule.span O S := by
      rw [← Submodule.span_span_of_tower ℤ_[l] O (T : Set B), hT, Submodule.span_span_of_tower]
    have h3 : C = Algebra.adjoin O (T : Set B) := by
      rw [← Algebra.adjoin_span (R := O) (s := (T : Set B)), h2, Algebra.adjoin_span]
    have h4 : ∀ t ∈ (T : Set B), IsIntegral O t := fun t ht => by
      obtain ⟨y, hy⟩ := hCx t (h3 ▸ Algebra.subset_adjoin ht)
      exact isIntegral_of_nilpotent_kernel πO hπ t (hy ▸ hint y)
    rw [h3]
    exact Algebra.finite_adjoin_of_finite_of_isIntegral T.finite_toSet h4
  haveI : IsCO O x.range := co_quot O R _ x.rangeRestrict x.rangeRestrict_surjective
  haveI : Algebra.IsIntegral O x.range := ⟨fun z => by
    obtain ⟨a, rfl⟩ := x.rangeRestrict_surjective z
    exact (isIntegral_algHom_iff x.range.val Subtype.val_injective).1 (hint a)⟩
  let p : C →ₐ[O] x.range := (πO.comp C.val).codRestrict _ fun c => hCx c c.2
  haveI hCO : IsCO O C := complete_of_nilpotent_kernel_finite p fun a ha => by
    obtain ⟨n, hn⟩ := hπ a (congrArg Subtype.val ha)
    exact ⟨n, Subtype.ext (by simpa using hn)⟩
  let r' : Γ →* Matrix ι ι C :=
    { toFun := fun g => Matrix.of fun a b => ⟨r g a b, hSC g a b⟩
      map_one' := by
        ext a b
        simp [Matrix.one_apply, apply_ite Subtype.val]
      map_mul' := fun g h => by
        ext a b
        simp [Matrix.mul_apply] }
  refine ⟨C, hCO, ⟨r', fun a b N => ?_, fun g a b => ?_⟩, fun g a b => rfl⟩
  · letI : Algebra ℤ_[l] C := ((algebraMap O C).comp (algebraMap ℤ_[l] O)).toAlgebra
    haveI : IsScalarTower ℤ_[l] O C := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : Module.Finite ℤ_[l] C := Module.Finite.trans O C
    have hl : algebraMap ℤ_[l] C l ∈ maximalIdeal C := by
      haveI := (dvrFacts l O).2.2.1
      rw [IsScalarTower.algebraMap_apply ℤ_[l] O C]
      refine map_nonunit _ _ (map_nonunit _ _ ?_)
      rw [PadicInt.maximalIdeal_eq_span_p]
      exact Ideal.subset_span rfl
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun g₀ => ?_
    filter_upwards [eventually_congruent_mod_l_pow (l := l) (C.val.toLinearMap.restrictScalars ℤ_[l]) Subtype.val_injective
      (fun g => r' g a b) (hc a b) N g₀] with g hg
    obtain ⟨m, hm⟩ := hg
    refine Ideal.Quotient.eq.2 ?_
    rw [hm, Algebra.smul_def, map_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hl N)
  · rw [← res_map p, ← ρ.red, ← res_map x.rangeRestrict]
    congr 1
    exact Subtype.ext (hr g a b)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsSp4RootVectorUniqueOnWeight
section
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.HV UpperTheory.V.Base IsLocalRing

private def rootEnt (a b i j : Fin 4) : ℤ :=
  if i = a ∧ j = b then 1 else if j.rev = a ∧ i.rev = b then -(sgn i * sgn j) else 0

private theorem rootEnt_adj : ∀ a b i j : Fin 4, a ≠ b →
    (sgn i * sgn j) * rootEnt a b j.rev i.rev = -rootEnt a b i j := by decide

private theorem rootEnt_zero : ∀ a b i j : Fin 4, wt i j ≠ wt a b → rootEnt a b i j = 0 := by decide

private theorem rootEnt_cases : ∀ a b i j : Fin 4, a ≠ b → wt i j = wt a b →
    (i = a ∧ j = b) ∨ (j.rev = a ∧ i.rev = b ∧ rootEnt a b i j = -(sgn i * sgn j)) := by decide

theorem UpperTheory.exists_sp4_root_vector_unique_on_weight :
    ∀ (E : Type) [Field E] [CharZero E] (a b : Fin 4), a ≠ b → ∃ X ∈ sp4 E, X a b = 1 ∧ (∀ i j, wt i j ≠ wt a b → X i j = 0) ∧ ∀ Y ∈ sp4 E, ∀ i j, wt i j = wt a b → Y i j = Y a b * X i j := by
  intro E _ _ a b hab
  refine ⟨Matrix.of fun i j => ((rootEnt a b i j : ℤ) : E), ?_, ?_, ?_, ?_⟩
  · show UpperTheory.V.GradeZeroInterpolatingElement.adj _ = -_
    ext i j
    rw [adj_apply, Matrix.neg_apply, Matrix.of_apply, Matrix.of_apply, zsmul_eq_mul, ← Int.cast_mul,
      rootEnt_adj a b i j hab, Int.cast_neg]
  · simp [rootEnt]
  · intro i j h
    simp [rootEnt_zero a b i j h]
  · intro Y hY i j h
    rcases rootEnt_cases a b i j hab h with ⟨rfl, rfl⟩ | ⟨h1, h2, h3⟩
    · simp [rootEnt]
    · have hY' : UpperTheory.V.GradeZeroInterpolatingElement.adj Y = -Y := hY
      have h4 := congrFun (congrFun hY' i) j
      rw [adj_apply, Matrix.neg_apply, h1, h2, zsmul_eq_mul] at h4
      rw [Matrix.of_apply, h3, Int.cast_neg]
      linear_combination h4
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsTorusCoordsOfUnipotent
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

section

variable {B : Type} [CommRing B]

private theorem triM_mul (t s : Fin 3 → Bˣ) (x y z x' y' z' : B) :
    triM t x y z * triM s x' y' z' =
      triM (fun i => t i * s i) (x + ((t 0 / t 1 : Bˣ) : B) * x') (y + ((t 1 / t 2 : Bˣ) : B) * y')
        (z + x * (((t 1 / t 2 : Bˣ) : B) * y') + ((t 0 / t 2 : Bˣ) : B) * z') := by
  have h1 := Units.inv_mul (t 1)
  have h2 := Units.inv_mul (t 2)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [triM, Matrix.mul_apply, Fin.sum_univ_three, div_eq_mul_inv] <;>
    first
    | ring1
    | linear_combination (-((t 0 : B) * x' * (s 1 : B))) * h1
    | linear_combination (-((t 0 : B) * z' * (s 2 : B)) - (s 2 : B) * x * (t 1 : B) * y') * h2
    | linear_combination (-((t 1 : B) * y' * (s 2 : B))) * h2

private theorem triM_inj {t s : Fin 3 → Bˣ} {x y z x' y' z' : B} (h : triM t x y z = triM s x' y' z') :
    t = s ∧ x = x' ∧ y = y' ∧ z = z' := by
  have e : ∀ i j, triM t x y z i j = triM s x' y' z' i j := fun i j => by rw [h]
  have a0 := e 0 0
  have a1 := e 1 1
  have a2 := e 2 2
  have b1 := e 0 1
  have b2 := e 1 2
  have b3 := e 0 2
  simp [triM] at a0 a1 a2 b1 b2 b3
  have ht : t = s := by
    funext i
    fin_cases i
    · exact Units.ext a0
    · exact Units.ext a1
    · exact Units.ext a2
  subst ht
  refine ⟨rfl, ?_, ?_, ?_⟩
  · simpa using congrArg (· * ((t 1)⁻¹ : Bˣ).val) b1
  · simpa using congrArg (· * ((t 2)⁻¹ : Bˣ).val) b2
  · simpa using congrArg (· * ((t 2)⁻¹ : Bˣ).val) b3

private theorem theta_triM {A : GL (Fin 3) B} {t : Fin 3 → Bˣ} {x y z : B}
    (h : (A : Matrix (Fin 3) (Fin 3) B) = triM t x y z) :
    (theta A : Matrix (Fin 3) (Fin 3) B) = triM (fun i => (t i.rev)⁻¹) (-y) (-x) (x * y - z) := by
  have h1 := Units.inv_mul (t 1)
  have h2 := Units.inv_mul (t 2)
  have key : triM (fun i => (t i.rev)⁻¹) (-y) (-x) (x * y - z) * ((theta A)⁻¹ : GL (Fin 3) B) = 1 := by
    rw [theta_inv_val, h]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [triM, Jmat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, Fin.rev] <;>
      first
      | linear_combination y * h2
      | linear_combination z * h2 - x * y * h1
      | linear_combination x * h1
  calc (theta A : Matrix (Fin 3) (Fin 3) B)
      = 1 * (theta A : Matrix (Fin 3) (Fin 3) B) := (one_mul _).symm
    _ = triM (fun i => (t i.rev)⁻¹) (-y) (-x) (x * y - z) * ((theta A)⁻¹ : GL (Fin 3) B) *
          (theta A : Matrix (Fin 3) (Fin 3) B) := by rw [key]
    _ = triM (fun i => (t i.rev)⁻¹) (-y) (-x) (x * y - z) := by
      rw [mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]

private theorem exists_triM (A : GL (Fin 3) B)
    (h : ∀ a b, wt a b < 0 → (A : Matrix (Fin 3) (Fin 3) B) a b = 0) :
    ∃ (t : Fin 3 → Bˣ) (x y z : B), (A : Matrix (Fin 3) (Fin 3) B) = triM t x y z := by
  have z10 := h 1 0 (by decide)
  have z20 := h 2 0 (by decide)
  have z21 := h 2 1 (by decide)
  have hd : IsUnit (A : Matrix (Fin 3) (Fin 3) B).det := Matrix.isUnits_det_units A
  rw [Matrix.det_fin_three, z10, z20, z21] at hd
  simp only [mul_zero, zero_mul, sub_zero, add_zero, zero_sub, neg_zero, IsUnit.mul_iff] at hd
  obtain ⟨⟨h0, h1⟩, h2⟩ := hd
  refine ⟨![h0.unit, h1.unit, h2.unit], (A : Matrix (Fin 3) (Fin 3) B) 0 1 * ↑h1.unit⁻¹,
    (A : Matrix (Fin 3) (Fin 3) B) 1 2 * ↑h2.unit⁻¹, (A : Matrix (Fin 3) (Fin 3) B) 0 2 * ↑h2.unit⁻¹, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [triM, z10, z20, z21, mul_assoc]

end

theorem UpperTheory.exists_torus_coords_of_unipotent :
    ∀ {G B : Type} [Group G] [CommRing B] {η : G →* ℤˣ} (h : B), 2 * h = 1 → ∀ u : G →* GG 3 B, HasMult η u → (∀ g a b, wt a b < 0 → (u g).mat a b = 0) → ∃ (T : Tor η B) (β : G → B × B) (γ : G → B), T.Coord h β γ u ∧ (∀ g g', β (g * g') = β g + T.M1 g (β g')) ∧ T.IsGam h β γ := by
  intro G B _ _ η h h2 u hm hu
  have ex : ∀ g, ∃ (t : Fin 3 → Bˣ) (x y z : B), (u g).mat = triM t x y z :=
    fun g => exists_triM (u g).left (hu g)
  choose t x y z hA using ex
  have step : ∀ g g', ∃ (t' : Fin 3 → Bˣ) (x' y' z' : B),
      (u (g * g')).mat = triM (t g) (x g) (y g) (z g) * triM t' x' y' z' ∧
      ((η g = 1 ∧ t' = t g' ∧ x' = x g' ∧ y' = y g' ∧ z' = z g') ∨
       (η g = -1 ∧ t' = (fun i => (t g' i.rev)⁻¹) ∧ x' = -y g' ∧ y' = -x g' ∧ z' = x g' * y g' - z g')) := by
    intro g g'
    have hmul : (u (g * g')).mat = (u g).mat * (((sgnAct 3 B) (u g).right) (u g').left : Matrix (Fin 3) (Fin 3) B) := by
      rw [map_mul]
      show (((u g * u g').left : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B) = _
      rw [SemidirectProduct.mul_left, Units.val_mul]
      rfl
    rw [hm g] at hmul
    rcases Int.units_eq_one_or (η g) with e | e
    · rw [e, sgnAct_one] at hmul
      exact ⟨_, _, _, _, by rw [hmul, hA g]; exact congrArg _ (hA g'), Or.inl ⟨e, rfl, rfl, rfl, rfl⟩⟩
    · rw [e, sgnAct_neg_one] at hmul
      exact ⟨_, _, _, _, by rw [hmul, hA g]; exact congrArg _ (theta_triM (hA g')), Or.inr ⟨e, rfl, rfl, rfl, rfl⟩⟩
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  have hab : ∀ g, ((t g 0 / t g 1 : Bˣ) : B) * ((t g 1 / t g 2 : Bˣ) : B) = ((t g 0 / t g 2 : Bˣ) : B) := by
    intro g
    rw [← Units.val_mul, div_mul_div_cancel]
  refine ⟨⟨t, ?_⟩, fun g => (x g, y g), fun g => z g - h * x g * y g, ⟨hm, fun g => ?_⟩, ?_, ?_⟩
  · intro g g' i
    obtain ⟨t', x', y', z', he, hc⟩ := step g g'
    rw [triM_mul, hA (g * g')] at he
    obtain ⟨ht, -, -, -⟩ := triM_inj he
    rcases hc with ⟨e, rfl, -, -, -⟩ | ⟨e, rfl, -, -, -⟩
    · rw [ht]
      simp [e]
    · rw [ht]
      simp [e, hne]
  · rw [hA g]
    congr 1
    ring
  · intro g g'
    obtain ⟨t', x', y', z', he, hc⟩ := step g g'
    rw [triM_mul, hA (g * g')] at he
    obtain ⟨-, hx, hy, -⟩ := triM_inj he
    rcases hc with ⟨e, -, rfl, rfl, -⟩ | ⟨e, -, rfl, rfl, -⟩
    · ext <;> simp [Tor.adjointSuperdiagRep_apply, e, hx, hy]
    · ext <;> simp [Tor.adjointSuperdiagRep_apply, e, hne, hx, hy]
  · intro g g'
    obtain ⟨t', x', y', z', he, hc⟩ := step g g'
    rw [triM_mul, hA (g * g')] at he
    obtain ⟨-, hx, hy, hz⟩ := triM_inj he
    have hg := hab g
    simp only [Tor.χ2_apply, Tor.adjointSuperdiagRep_apply, omg]
    rcases hc with ⟨e, -, rfl, rfl, rfl⟩ | ⟨e, -, rfl, rfl, rfl⟩
    · simp only [e, if_true]
      rw [hx, hy, hz]
      push_cast
      linear_combination (-(x g * ((t g 1 / t g 2 : Bˣ) : B) * y g')) * h2 - (h * x g' * y g') * hg
    · simp only [e, hne, if_false]
      rw [hx, hy, hz]
      push_cast
      linear_combination (((t g 1 / t g 2 : Bˣ) : B) * x g * x g' - ((t g 0 / t g 2 : Bˣ) : B) * x g' * y g') * h2 - (h * x g' * y g') * hg
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsUnipotentFromTorusCoords
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

private def triGL {B : Type} [CommRing B] (t : Fin 3 → Bˣ) (x y z : B) : GL (Fin 3) B where
  val := triM t x y z
  inv := !![((t 0)⁻¹ : Bˣ), -x * ((t 0)⁻¹ : Bˣ), (x * y - z) * ((t 0)⁻¹ : Bˣ);
    0, ((t 1)⁻¹ : Bˣ), -y * ((t 1)⁻¹ : Bˣ); 0, 0, ((t 2)⁻¹ : Bˣ)]
  val_inv := by
    have h0 := (t 0).mul_inv
    have h1 := (t 1).mul_inv
    have h2 := (t 2).mul_inv
    ext i j
    fin_cases i <;> fin_cases j <;> simp [triM, Matrix.mul_apply, Fin.sum_univ_three, -Units.mul_inv, -Units.inv_mul] <;>
      first
        | assumption
        | linear_combination (-x) * h0
        | linear_combination (x * y - z) * h0 - x * y * h1
        | linear_combination (-y) * h1
  inv_val := by
    have h0 := (t 0).inv_mul
    have h1 := (t 1).inv_mul
    have h2 := (t 2).inv_mul
    ext i j
    fin_cases i <;> fin_cases j <;> simp [triM, Matrix.mul_apply, Fin.sum_univ_three, -Units.mul_inv, -Units.inv_mul] <;>
      first
        | assumption
        | ring

private theorem triGL_val {B : Type} [CommRing B] (t : Fin 3 → Bˣ) (x y z : B) :
    (triGL t x y z : Matrix (Fin 3) (Fin 3) B) = triM t x y z := rfl

private theorem triGL_congr {B : Type} [CommRing B] {t s : Fin 3 → Bˣ} {x y z x' y' z' : B}
    (ht : t = s) (hx : x = x') (hy : y = y') (hz : z = z') : triGL t x y z = triGL s x' y' z' := by
  subst ht hx hy hz
  rfl

private theorem theta_triGL {B : Type} [CommRing B] (t : Fin 3 → Bˣ) (x y z : B) :
    theta (triGL t x y z) = triGL (fun i => (t i.rev)⁻¹) (-y) (-x) (x * y - z) := by
  apply Units.ext
  rw [theta_val, triGL_val]
  have hinv : ((triGL t x y z)⁻¹ : GL (Fin 3) B).val =
      !![(((t 0)⁻¹ : Bˣ) : B), -x * (((t 0)⁻¹ : Bˣ) : B), (x * y - z) * (((t 0)⁻¹ : Bˣ) : B);
        0, (((t 1)⁻¹ : Bˣ) : B), -y * (((t 1)⁻¹ : Bˣ) : B); 0, 0, (((t 2)⁻¹ : Bˣ) : B)] := rfl
  rw [hinv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Jmat, triM, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, Fin.rev] <;> ring

private theorem triGL_mul {B : Type} [CommRing B] (t s : Fin 3 → Bˣ) (x y z x' y' z' : B) :
    triGL t x y z * triGL s x' y' z' = triGL (fun i => t i * s i)
      (x + ((t 0 / t 1 : Bˣ) : B) * x') (y + ((t 1 / t 2 : Bˣ) : B) * y')
      (z + ((t 0 / t 2 : Bˣ) : B) * z' + x * (((t 1 / t 2 : Bˣ) : B) * y')) := by
  apply Units.ext
  rw [Units.val_mul, triGL_val, triGL_val, triGL_val]
  have h1 := (t 1).inv_mul
  have h2 := (t 2).inv_mul
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, triM, div_eq_mul_inv, -Units.mul_inv, -Units.inv_mul] <;>
    first
      | linear_combination (-((t 0 : B) * x' * s 1)) * h1
      | linear_combination (-((t 1 : B) * y' * s 2)) * h2
      | linear_combination (-((t 0 : B) * z' * s 2 + x * t 1 * y' * s 2)) * h2

theorem UpperTheory.exists_unipotent_from_torus_coords :
    ∀ {G B : Type} [Group G] [CommRing B] {η : G →* ℤˣ} (T : Tor η B) (h : B), 2 * h = 1 → ∀ (β : G → B × B) (γ : G → B), (∀ g g', β (g * g') = β g + T.M1 g (β g')) → T.IsGam h β γ → ∃ u : G →* GG 3 B, T.Coord h β γ u := by
  intro G B _ _ η T h hh β γ hβ hγ
  let F : G → GG 3 B := fun g =>
    ⟨triGL (T.t g) (β g).1 (β g).2 (γ g + h * (β g).1 * (β g).2), η g⟩
  have hmul : ∀ g g' : G, F (g * g') = F g * F g' := by
    intro g g'
    have hab : (((T.t g 0 / T.t g 2 : Bˣ)) : B) =
        ((T.t g 0 / T.t g 1 : Bˣ) : B) * ((T.t g 1 / T.t g 2 : Bˣ) : B) := by
      rw [← Units.val_mul, div_mul_div_cancel]
    have hb := hβ g g'
    have hc := hγ g g'
    apply SemidirectProduct.ext
    · simp only [F, SemidirectProduct.mul_left]
      rcases Int.units_eq_one_or (η g) with he | he
      · rw [he, sgnAct_one, triGL_mul]
        rw [Tor.adjointSuperdiagRep_apply, if_pos he] at hb
        rw [Tor.adjointSuperdiagRep_apply, if_pos he, Tor.χ2_apply, he] at hc
        apply triGL_congr
        · funext i
          rw [T.mul, if_pos he]
        · rw [hb]; rfl
        · rw [hb]; rfl
        · rw [hc, hb, hab]
          simp only [omg, Prod.fst_add, Prod.snd_add, Units.val_one, Int.cast_one, one_mul]
          linear_combination ((β g).1 * ((T.t g 1 / T.t g 2 : Bˣ) : B) * (β g').2) * hh
      · have hne : η g ≠ 1 := by rw [he]; decide
        rw [he, sgnAct_neg_one, theta_triGL, triGL_mul]
        rw [Tor.adjointSuperdiagRep_apply, if_neg hne] at hb
        rw [Tor.adjointSuperdiagRep_apply, if_neg hne, Tor.χ2_apply, he] at hc
        apply triGL_congr
        · funext i
          rw [T.mul, if_neg hne]
        · rw [hb]
          simp only [Prod.fst_add]
          ring
        · rw [hb]
          simp only [Prod.snd_add]
          ring
        · rw [hc, hb, hab]
          simp only [omg, Prod.fst_add, Prod.snd_add, Units.val_neg, Units.val_one, Int.cast_neg,
            Int.cast_one]
          linear_combination (((T.t g 0 / T.t g 1 : Bˣ) : B) * ((T.t g 1 / T.t g 2 : Bˣ) : B) *
            (β g').1 * (β g').2 - ((T.t g 1 / T.t g 2 : Bˣ) : B) * (β g).1 * (β g').1) * hh
    · simp only [F, SemidirectProduct.mul_right, map_mul]
  refine ⟨MonoidHom.mk' F hmul, ?_⟩
  exact Tor.Coord.mk (fun g => rfl) (fun g => rfl)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.MemFiniteCocyclesIffRestrictSubgroupMem
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

theorem UpperTheory.mem_finiteCocycles_iff_restrict_subgroup_mem :
    ∀ {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {η : GQ l →* ℤˣ} {Ψ : GQ l →* Eˣ} {H : Subgroup (GQ l)} {e : ℕ} (hD : TriDat η Ψ H e) {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (T : Tor η B), T.Good π Ψ → ∀ β ∈ Z1 T.M1, (β ∈ UpperTheory.V.Loc.finiteCocycles (MonoidHom.id (GQ l)) T.M1 ↔ (fun g : H => (β g).1) ∈ UpperTheory.V.Loc.finiteCocycles H.subtype (chRep (T.ch H hD.ηH 0 / T.ch H hD.ηH 1)) ∧ (fun g : H => (β g).2) ∈ UpperTheory.V.Loc.finiteCocycles H.subtype (chRep (T.ch H hD.ηH 1 / T.ch H hD.ηH 2))) := by
  intro l _ E _ _ _ _ _ η Ψ H e hD B _ _ _ _ _ _ _ _ _ _ π hπ T hT β hβ
  haveI := hD.normal
  haveI := hD.fin
  have hM : ∀ (g : H) (v : B × B), (T.M1.comp H.subtype : Representation B H (B × B)) g v =
      (chRep (T.ch H hD.ηH 0 / T.ch H hD.ηH 1) g v.1, chRep (T.ch H hD.ηH 1 / T.ch H hD.ηH 2) g v.2) := by
    intro g v
    change T.M1 g v = _
    rw [Tor.adjointSuperdiagRep_apply, if_pos (hD.ηH g g.2)]
    rfl
  rw [z1fDesc (MonoidHom.id (GQ l)) T.M1 H β hβ, MonoidHom.id_comp]
  constructor
  · intro h
    exact ⟨(z1fMap H.subtype _ _).2 (LinearMap.fst ℚ_[l] B B) (fun g x => by rw [hM]; rfl) _ h,
      (z1fMap H.subtype _ _).2 (LinearMap.snd ℚ_[l] B B) (fun g x => by rw [hM]; rfl) _ h⟩
  · rintro ⟨h1, h2⟩
    have k1 := (z1fMap H.subtype _ (T.M1.comp H.subtype : Representation B H (B × B))).2
      (LinearMap.inl ℚ_[l] B B) (fun g x => by rw [hM]; simp) _ h1
    have k2 := (z1fMap H.subtype _ (T.M1.comp H.subtype : Representation B H (B × B))).2
      (LinearMap.inr ℚ_[l] B B) (fun g x => by rw [hM]; simp) _ h2
    have k := add_mem k1 k2
    convert k using 1
    funext g
    simp
end

