import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0047
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0004

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HasUEigenvalueOfLocIsotypic
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.HeckeGal UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem dc_common {G : Type} [Group G] (K K' : Subgroup G) (x : G) :
    ∃ s : Finset (MulAction.orbit K (x : G ⧸ K')), ∀ (M : Type) [AddCommGroup M] [Module ℂ M]
      (ρ : Representation ℂ G M) (v : M), Hi.dc ρ K K' x v = ∑ q ∈ s, ρ (q : G ⧸ K').out v := by
  by_cases h : Finite (MulAction.orbit K (x : G ⧸ K'))
  · letI := Fintype.ofFinite (MulAction.orbit K (x : G ⧸ K'))
    refine ⟨Finset.univ, fun M _ _ ρ v => ?_⟩
    rw [Hi.dc, finsum_eq_sum_of_fintype, LinearMap.sum_apply]
  · refine ⟨∅, fun M _ _ ρ v => ?_⟩
    rcases subsingleton_or_nontrivial M with hM | hM
    · exact Subsingleton.elim _ _
    have hs : (Function.support fun q : MulAction.orbit K (x : G ⧸ K') => ρ (q : G ⧸ K').out) = Set.univ := by
      refine Set.eq_univ_of_forall fun q hq => ?_
      have h1 : ρ ((q : G ⧸ K').out⁻¹ * (q : G ⧸ K').out) = 0 := by rw [map_mul, show ρ (q : G ⧸ K').out = 0 from hq, mul_zero]
      rw [inv_mul_cancel, map_one] at h1
      exact one_ne_zero h1
    rw [Hi.dc, finsum_of_infinite_support, Finset.sum_empty, LinearMap.zero_apply]
    rw [hs]
    exact fun hf => h (Set.finite_univ_iff.1 hf)

private theorem killed_of_mem_iSup {G V U ι J : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G U) (hσ : σ.IsIrreducible) (f : ι → U →ₗ[ℂ] V)
    (hf : ∀ i g u, f i (σ g u) = ρ g (f i u)) (T : J → V →ₗ[ℂ] V) (S : J → U →ₗ[ℂ] U)
    (hTS : ∀ j i u, f i (S j u) = T j (f i u))
    (hT : ∀ W : Submodule ℂ V, (∀ g, ∀ x ∈ W, ρ g x ∈ W) → ∀ j, ∀ x ∈ W, T j x ∈ W)
    (φ : V) (h0 : φ ≠ 0) (hK : ∀ j, T j φ = 0)
    (hφ : φ ∈ ⨆ i, LinearMap.range (f i)) : ∃ v : U, v ≠ 0 ∧ ∀ j, S j v = 0 := by
  classical
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.1 hφ
  have key : ∀ s : Finset ι, ∀ W : Submodule ℂ V, (∀ g, ∀ x ∈ W, ρ g x ∈ W) → φ ∉ W →
      φ ∈ W ⊔ ⨆ i ∈ s, LinearMap.range (f i) → ∃ v : U, v ≠ 0 ∧ ∀ j, S j v = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro W _ h1 h2; exact absurd (by simpa using h2) h1
    | insert i s _ ih =>
      intro W hW h1 h2
      rw [Finset.iSup_insert, ← sup_assoc] at h2
      by_cases h3 : φ ∈ W ⊔ LinearMap.range (f i)
      · obtain ⟨x, hx, _, ⟨v, rfl⟩, e⟩ := Submodule.mem_sup.1 h3
        have hv : f i v ∉ W := fun h => h1 (e ▸ add_mem hx h)
        have hc : W.comap (f i) = ⊥ := by
          refine (((GlobalTheory.CuspRep.isIrreducible_iff σ).1 hσ).2 _ fun g u hu => ?_).resolve_right fun h => hv ?_
          · rw [Submodule.mem_comap, hf]; exact hW g _ hu
          · have : v ∈ W.comap (f i) := h ▸ Submodule.mem_top
            exact this
        refine ⟨v, fun h => hv (by rw [h, map_zero]; exact zero_mem _), fun j => ?_⟩
        have h4 : S j v ∈ W.comap (f i) := by
          have h5 := hK j
          rw [← e, map_add] at h5
          rw [Submodule.mem_comap, hTS, eq_neg_of_add_eq_zero_right h5]
          exact neg_mem (hT W hW j x hx)
        rwa [hc, Submodule.mem_bot] at h4
      · refine ih _ (fun g y hy => ?_) h3 h2
        obtain ⟨x, hx, _, ⟨v, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hy
        rw [map_add, ← hf]
        exact Submodule.add_mem_sup (hW g x hx) ⟨_, rfl⟩
  exact key s ⊥ (fun g x hx => by simp_all) (by simpa using h0) (by simpa using hs)

private theorem dc_eigen_descend {G V U ι : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G U) (hσ : σ.IsIrreducible) (f : ι → U →ₗ[ℂ] V)
    (hf : ∀ i g u, f i (σ g u) = ρ g (f i u)) (K : Subgroup G) (x : G) (lam : ℂ)
    (φ : V) (h0 : φ ≠ 0) (hK : φ ∈ Hi.fixd ρ K) (hl : Hi.dc ρ K K x φ = lam • φ)
    (hφ : φ ∈ ⨆ i, LinearMap.range (f i)) :
    ∃ v : U, v ≠ 0 ∧ v ∈ Hi.fixd σ K ∧ Hi.dc σ K K x v = lam • v := by
  obtain ⟨s, hs⟩ := dc_common K K x
  obtain ⟨v, hv0, hv⟩ := killed_of_mem_iSup ρ σ hσ f hf
    (fun j : Option K => j.elim (Hi.dc ρ K K x - lam • LinearMap.id) fun k => ρ k - LinearMap.id)
    (fun j : Option K => j.elim (Hi.dc σ K K x - lam • LinearMap.id) fun k => σ k - LinearMap.id)
    (by
      rintro (_ | k) i u
      · simp only [Option.elim, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub, map_smul, hs,
          map_sum, hf]
      · simp only [Option.elim, LinearMap.sub_apply, LinearMap.id_apply, map_sub, hf])
    (by
      rintro W hW (_ | k) y hy
      · simp only [Option.elim, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hs]
        exact sub_mem (Submodule.sum_mem _ fun q _ => hW _ _ hy) (W.smul_mem _ hy)
      · simp only [Option.elim, LinearMap.sub_apply, LinearMap.id_apply]
        exact sub_mem (hW _ _ hy) hy)
    φ h0
    (by
      rintro (_ | k)
      · simp only [Option.elim, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hl, sub_self]
      · simp only [Option.elim, LinearMap.sub_apply, LinearMap.id_apply]
        exact sub_eq_zero.2 (hK k k.2))
    hφ
  exact ⟨v, hv0, fun k hk => sub_eq_zero.1 (hv (some ⟨k, hk⟩)), sub_eq_zero.1 (hv none)⟩

theorem UpperTheory.hasUEigenvalue_of_locIsotypic :
    ∀ (F : Type) [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin 2) (Af F)) V) (σ : SmIrr (GL (Fin 2) (w.adicCompletion F))), LocIsotypic ρ w σ → ∀ (c : ℕ) (lam : ℂ), HasU w (ρ.comp (locGL F 2 w)) c lam → HasU w σ.ρ c lam := by
  intro F _ _ w V _ _ ρ σ ⟨_, htop⟩ c lam ⟨φ, h0, hK, hl⟩
  exact dc_eigen_descend (ρ.comp (locGL F 2 w)) σ.ρ σ.irred
    (fun f : {f : σ.V →ₗ[ℂ] V // ∀ g v, f (σ.ρ g v) = ρ (locGL F 2 w g) (f v)} => f.1) (fun f => f.2)
    (K1 w c) _ lam φ h0 hK hl (htop ▸ Submodule.mem_top)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeckeOperatorsCommuteOnAutomorphicForms
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd
open scoped Matrix

section SlopeTestRemainingChoices

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {a : ℕ}

private theorem finite_translation_mul (g h : GL (Fin a) (Af F)) (φ : TR.Sm F a) :
    TR.finRep F a (g * h) φ = TR.finRep F a g (TR.finRep F a h φ) := by
  rw [map_mul]; rfl

private theorem center_algebra_translation_comm (g : GL (Fin a) (Af F)) {z : Module.End ℂ (TR.Sm F a)} (hz : z ∈ TR.Zalg F a) :
    TR.finRep F a g * z = z * TR.finRep F a g := by
  have key : TR.Zalg F a ≤ Subalgebra.centralizer ℂ {TR.finRep F a g} := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨v, u, rfl⟩
    have hE : ∀ i j, TR.Eop v i j ∈ Subalgebra.centralizer ℂ {TR.finRep F a g} := by
      intro i j
      rw [Subalgebra.mem_centralizer_iff]
      rintro _ rfl
      exact (TR.lie_rt_fin _ g).symm
    refine Subalgebra.sum_mem _ fun σ _ => Subalgebra.mul_mem _ (intCast_mem _ _)
      (Subalgebra.list_prod_mem _ fun x hx => ?_)
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
    refine Subalgebra.add_mem _ ?_ (hE _ _)
    split_ifs
    · exact Subalgebra.algebraMap_mem _ _
    · exact Subalgebra.zero_mem _
  exact (Subalgebra.mem_centralizer_iff ℂ).1 (key hz) _ rfl

private theorem compact_finite_translation_comm (g : GL (Fin a) (Af F)) (k : TR.Kinf F a) (φ : TR.Sm F a) :
    TR.cptRep F a k (TR.finRep F a g φ) = TR.finRep F a g (TR.cptRep F a k φ) := by
  refine Subtype.ext (funext fun x => ?_)
  change φ.1 (x * TR.infGL F a (Unitary.toUnits k) * finGL F a g) =
    φ.1 (x * finGL F a g * TR.infGL F a (Unitary.toUnits k))
  rw [mul_assoc, mul_assoc, TR.infGL_comm]

private theorem automorphic_form_translate (φ : TR.Sm F a) (g : GL (Fin a) (Af F)) (h : TR.IsAutForm φ) :
    TR.IsAutForm (TR.finRep F a g φ) := by
  refine ⟨fun γ x => ?_, ?_, ?_, ?_, fun x => ?_⟩
  · change φ.1 (ratGL F a γ * x * finGL F a g) = φ.1 (x * finGL F a g)
    rw [mul_assoc, h.left]
  · have e : {k | TR.finRep F a k (TR.finRep F a g φ) = TR.finRep F a g φ} =
        (fun k => g⁻¹ * k * g) ⁻¹' {k | TR.finRep F a k φ = φ} := by
      ext k
      simp only [Set.mem_setOf_eq, Set.mem_preimage]
      constructor
      · intro hk
        rw [finite_translation_mul, finite_translation_mul, hk, ← finite_translation_mul, inv_mul_cancel, map_one]
        rfl
      · intro hk
        have := congrArg (TR.finRep F a g) hk
        rwa [← finite_translation_mul, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul, finite_translation_mul] at this
    rw [e]
    exact h.level.preimage ((continuous_const.mul continuous_id).mul continuous_const)
  · have := h.kfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := (Submodule.span ℂ (Set.range fun k => TR.cptRep F a k φ)).map (TR.finRep F a g)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨k, rfl⟩, (compact_finite_translation_comm g k φ).symm⟩
  · have := h.zfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := (Submodule.span ℂ ((fun z : Module.End ℂ (TR.Sm F a) => z φ) '' TR.Zalg F a)).map (TR.finRep F a g))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨z, hz, rfl⟩, LinearMap.congr_fun (center_algebra_translation_comm g hz) φ⟩
  · obtain ⟨C, N, hC⟩ := h.growth (x * finGL F a g)
    refine ⟨C, N, fun y => ?_⟩
    change ‖φ.1 (x * TR.infGL F a y * finGL F a g)‖ ≤ _
    rw [mul_assoc, TR.infGL_comm, ← mul_assoc]
    exact hC y

private theorem automorphic_form_linear_combination (φ ψ : TR.Sm F a) (c : ℂ) (h : TR.IsAutForm φ) (h' : TR.IsAutForm ψ) :
    TR.IsAutForm (φ + c • ψ) := by
  refine ⟨fun γ x => ?_, ?_, ?_, ?_, fun x => ?_⟩
  · change φ.1 _ + c * ψ.1 _ = φ.1 _ + c * ψ.1 _
    rw [h.left, h'.left]
  · rw [isOpen_iff_mem_nhds]
    intro k₀ hk₀
    have hO : IsOpen ((fun k => k₀⁻¹ * k) ⁻¹' ({k | TR.finRep F a k φ = φ} ∩ {k | TR.finRep F a k ψ = ψ})) :=
      (h.level.inter h'.level).preimage (continuous_const.mul continuous_id)
    refine Filter.mem_of_superset (hO.mem_nhds ?_) ?_
    · simp
    · rintro k ⟨h1, h2⟩
      have h1' : TR.finRep F a (k₀⁻¹ * k) φ = φ := h1
      have h2' : TR.finRep F a (k₀⁻¹ * k) ψ = ψ := h2
      have h3 : TR.finRep F a (k₀⁻¹ * k) (φ + c • ψ) = φ + c • ψ := by rw [map_add, map_smul, h1', h2']
      have h4 : TR.finRep F a k₀ (φ + c • ψ) = φ + c • ψ := hk₀
      change TR.finRep F a k (φ + c • ψ) = φ + c • ψ
      rw [← mul_inv_cancel_left k₀ k, finite_translation_mul, h3, h4]
  · have := h.kfin
    have := h'.kfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := Submodule.span ℂ (Set.range fun k => TR.cptRep F a k φ) ⊔
        Submodule.span ℂ (Set.range fun k => TR.cptRep F a k ψ)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    simp only [map_add, map_smul]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨k, rfl⟩)
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))
  · have := h.zfin
    have := h'.zfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := Submodule.span ℂ ((fun z : Module.End ℂ (TR.Sm F a) => z φ) '' TR.Zalg F a) ⊔
        Submodule.span ℂ ((fun z : Module.End ℂ (TR.Sm F a) => z ψ) '' TR.Zalg F a)) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    simp only [map_add, map_smul]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨z, hz, rfl⟩)
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨z, hz, rfl⟩))
  · obtain ⟨C, N, hC⟩ := h.growth x
    obtain ⟨D, M, hD⟩ := h'.growth x
    refine ⟨|C| + ‖c‖ * |D|, N + M, fun y => ?_⟩
    have h1 : 1 ≤ TR.height y := by
      unfold TR.height
      have := norm_nonneg (TR.toL y.val)
      have := norm_nonneg (TR.toL (y⁻¹).val)
      linarith
    have bound : ∀ (B : ℝ) (n : ℕ), n ≤ N + M → B * TR.height y ^ n ≤ |B| * TR.height y ^ (N + M) := fun B n hn =>
      mul_le_mul (le_abs_self B) (pow_le_pow_right₀ h1 hn) (pow_nonneg (zero_le_one.trans h1) n) (abs_nonneg B)
    have b1 := (hC y).trans (bound C N (Nat.le_add_right _ _))
    have b2 := (hD y).trans (bound D M (Nat.le_add_left _ _))
    change ‖φ.1 _ + c * ψ.1 _‖ ≤ _
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, add_mul, mul_assoc]
    exact add_le_add b1 (mul_le_mul_of_nonneg_left b2 (norm_nonneg c))

end SlopeTestRemainingChoices

theorem UpperTheory.hecke_operators_commute_on_automorphic_forms :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ), TR.IsAutForm (0 : TR.Sm F a) ∧ (∀ (φ : TR.Sm F a) (g : GL (Fin a) (Af F)), TR.IsAutForm φ → TR.IsAutForm (TR.finRep F a g φ)) ∧ ∀ (φ ψ : TR.Sm F a) (z : ℂ), TR.IsAutForm φ → TR.IsAutForm ψ → TR.IsAutForm (φ + z • ψ) := by
  intro F _ _ _ a
  exact ⟨TR.isAutForm_const (Submodule.zero_mem _), automorphic_form_translate, automorphic_form_linear_combination⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HilbertHolomorphicInvariantIntegralTranslation
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd
open scoped Matrix

private theorem map_aff' {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (x : R) :
    Matrix.GeneralLinearGroup.map f (aff 1 x) = aff 1 (f x) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aff]

private theorem aff_add' {R : Type} [CommRing R] (x y : R) : aff 1 x * aff 1 y = aff 1 (x + y) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aff, Matrix.mul_apply, Fin.sum_univ_succ, add_comm]

private theorem aff_zero' {R : Type} [CommRing R] : aff (1 : Rˣ) (0 : R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aff]

private theorem aff_mirab' {R : Type} [CommRing R] (x : R) : aff (1 : Rˣ) x ∈ mirab R := by
  change _ = _
  simp [funext_iff, Fin.forall_fin_two, Matrix.vecMul, dotProduct, aff]

open UpperTheory.V.Af.GlobalFixedVectors in
theorem UpperTheory.hilbertHolomorphic_invariant_integralTranslation :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (c : Pl F → ℕ) (ω : HChar F) (φ : TR.Sm F 2), IsHol k c ω φ → ∀ o : Af F, (∀ v : Pl F, Valued.v (pLoc F v o) ≤ 1) → TR.finRep F 2 (aff 1 o) φ = φ := by
  classical
  intro F _ _ _ k c ω φ hφ o ho
  have key : ∀ S : Finset (Pl F),
      (∀ x ∈ Ohat F, (∀ w ∈ S, pLoc F w x = 0) → TR.finRep F 2 (aff 1 x) φ = φ) →
      ∀ x ∈ Ohat F, TR.finRep F 2 (aff 1 x) φ = φ := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact fun h x hx => h x hx (by simp)
    | insert w S hw ih =>
      intro h
      refine ih fun x hx hS => ?_
      have e : aff 1 x = aff 1 (x - sLoc F w (pLoc F w x)) * locGL F 2 w (aff 1 (pLoc F w x)) := gl_ext fun u => by
        rw [map_mul, map_aff', map_aff', map_sub]
        by_cases hu : u = w
        · subst hu
          rw [pLoc_locGL, pLoc_sLoc, sub_self, aff_zero', one_mul]
        · rw [pLoc_locGL_of_ne hu, pLoc_sLoc_of_ne hu, sub_zero, mul_one]
      have hK : aff 1 (pLoc F w x) ∈ K1 w (c w) := by
        refine ⟨aff 1 ⟨pLoc F w x, mem_Ohat.1 hx w⟩, ?_, map_aff' _ _⟩
        change Matrix.GeneralLinearGroup.map _ _ ∈ mirab _
        rw [map_aff']
        exact aff_mirab' _
      have h1 : TR.finRep F 2 (locGL F 2 w (aff 1 (pLoc F w x))) φ = φ := hφ.level w _ hK
      rw [e, map_mul, Module.End.mul_apply, h1]
      refine h _ (sub_mem hx (sLoc_mem w hx)) fun u hu => ?_
      rw [map_sub]
      by_cases huw : u = w
      · subst huw
        rw [pLoc_sLoc, sub_self]
      · rw [pLoc_sLoc_of_ne huw, sub_zero]
        exact hS u ((Finset.mem_insert.1 hu).resolve_left huw)
  obtain ⟨S, hS⟩ := exists_KAway_subset (M := 1) (hφ.aut.level.mem_nhds (show (1 : GL (Fin 2) (Af F)) ∈ _ by simp))
  refine key S (fun x hx h0 => hS (mem_KAway.2 ⟨⟨aff 1 ⟨x, hx⟩, ?_, map_aff' _ _⟩, fun w hw => ?_⟩)) o (mem_Ohat.2 ho)
  · haveI : Subsingleton (Ohat F ⧸ Ideal.span {((1 : ℕ) : ↥(Ohat F))}) :=
      Ideal.Quotient.subsingleton_iff.2 (by simp)
    ext i j
    exact Subsingleton.elim _ _
  · rw [map_aff', h0 w hw, aff_zero']
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsSubquotientPrincipalSeriesOfBorelFunctional
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.HeckeGal UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section SlopeTestRemainingChoices
open GlobalTheory.SmGL GlobalTheory.PRep Matrix

private theorem sep_of_irred {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (hρ : ρ.IsIrreducible) (L : V →ₗ[ℂ] ℂ) (hL : L ≠ 0) (v : V) (hv : ∀ g, L (ρ g v) = 0) : v = 0 := by
  let S : Subrepresentation ρ :=
    ⟨{ carrier := {v | ∀ g, L (ρ g v) = 0}
       add_mem' := fun {a b} ha hb g => by simp [ha g, hb g]
       zero_mem' := fun g => by simp
       smul_mem' := fun c a ha g => by simp [ha g] }, fun x a ha g => by
      have := ha (g * x)
      simpa using this⟩
  haveI := hρ
  rcases eq_bot_or_eq_top S with h | h
  · have : v ∈ S.toSubmodule := hv
    rw [h] at this
    exact this
  · exfalso
    apply hL
    ext a
    have : a ∈ S.toSubmodule := by rw [h]; trivial
    simpa using this 1

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem diag_eq (a d : kˣ) :
    diagT k (Fin 2) ![a, d] = GeneralLinearGroup.scalar (Fin 2) d * aff (a / d) 0 := by
  ext i j
  rw [val_diagT]
  fin_cases i <;> fin_cases j <;>
    simp [aff, GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_succ, mul_div_cancel₀]

private theorem cont_diag : Continuous (diagT k (Fin 2)) :=
  (continuous_leviEmb k (points (Fin 2))).comp (continuous_leviTorus k (Fin 2))

private theorem finiteRing_sq_sub_mul_sq_eq_of_card (σ : SmIrr (GL (Fin 2) k)) (μ₁ μ₂ : kˣ →* ℂˣ) (L : σ.V →ₗ[ℂ] ℂ) (hL : L ≠ 0)
    (h : ∀ (a d : kˣ) (x : k) v, L (σ.ρ (GeneralLinearGroup.scalar (Fin 2) d * aff (a / d) x) v) =
      ((μ₁ a * μ₂ d : ℂˣ) : ℂ) * L v) :
    IsSmoothChar μ₁ ∧ IsSmoothChar μ₂ ∧ IsSubquotient σ.ρ (Hi.PS ![μ₁ * absPow k (-1), μ₂]) ∧
      ∀ (z : kˣ) v, σ.ρ (GeneralLinearGroup.scalar (Fin 2) z) v = ((μ₁ z * μ₂ z : ℂˣ) : ℂ) • v := by
  obtain ⟨v₀, hv₀⟩ : ∃ v, L v ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hL (LinearMap.ext hc)
  have hst : ∀ a d : kˣ, σ.ρ (diagT k (Fin 2) ![a, d]) v₀ = v₀ → μ₁ a * μ₂ d = 1 := by
    intro a d had
    have := h a d 0 v₀
    rw [← diag_eq, had] at this
    ext
    exact (mul_eq_right₀ hv₀).1 this.symm
  have hopen : IsOpen {g | σ.ρ g v₀ = v₀} := σ.smooth v₀
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hc : Continuous fun a : kˣ => diagT k (Fin 2) ![a, 1] :=
      cont_diag.comp (continuous_pi fun i => by fin_cases i; exacts [continuous_id, continuous_const])
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset ((hopen.preimage hc).mem_nhds ?_) ?_)
    · have : (![1, 1] : Fin 2 → kˣ) = 1 := by funext i; fin_cases i <;> rfl
      simp [this]
    · intro a ha
      simpa using hst a 1 ha
  · have hc : Continuous fun a : kˣ => diagT k (Fin 2) ![1, a] :=
      cont_diag.comp (continuous_pi fun i => by fin_cases i; exacts [continuous_const, continuous_id])
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset ((hopen.preimage hc).mem_nhds ?_) ?_)
    · have : (![1, 1] : Fin 2 → kˣ) = 1 := by funext i; fin_cases i <;> rfl
      simp [this]
    · intro a ha
      simpa using hst 1 a ha
  · let τ : Representation ℂ (Levi k fun _ : Fin 2 => Unit) ℂ :=
      (ofChar (torusChar fun i => ![μ₁ * absPow k (-1), μ₂] i * absPow k ((((2 : ℕ) : ℂ) - 1) / 2))).comp
        (leviTorus k (Fin 2)).symm.toMonoidHom
    have law : ∀ (p : parab k (points (Fin 2))) (u : σ.V), L (σ.ρ p u) =
        (deltaHalf k (fun _ : Fin 2 => Unit) (leviProj k (points (Fin 2)) p) : ℂ) •
          τ (leviProj k (points (Fin 2)) p) (L u) := by
      intro p u
      set t : Fin 2 → kˣ := (leviTorus k (Fin 2)).symm (leviProj k (points (Fin 2)) p) with ht
      have ht1 : ∀ i, GeneralLinearGroup.det (leviProj k (points (Fin 2)) p i) = t i := fun i => rfl
      have ht2 : ∀ i, (t i : k) = ((p : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) i i := by
        intro i
        rw [← ht1]
        simp
      have h10 : ((p : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) 1 0 = 0 :=
        (mem_borel k).1 p.2 1 0 (by decide)
      have hp : (p : GL (Fin 2) k) = GeneralLinearGroup.scalar (Fin 2) (t 1) *
          aff (t 0 / t 1) (((p : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) 0 1 / t 1) := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [aff, GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_succ, mul_div_cancel₀, ← ht2, h10]
      rw [hp, h]
      show _ = _ • ofChar _ t (L u)
      rw [ofChar_apply, deltaHalf_apply, torusChar_apply, Fin.prod_univ_two, Fin.prod_univ_two, ht1, ht1,
        modExp_fin _ (fun _ => by simp), modExp_fin _ (fun _ => by simp), smul_eq_mul, ← mul_assoc, ← Units.val_mul]
      congr 2
      have e1 : absPow k (-1) = (absPow k (1 / 2))⁻¹ * (absPow k (1 / 2))⁻¹ := by
        rw [← absPow_neg, ← absPow_add]; norm_num
      have e2 : ((((2 : ℕ) : ℤ) - 1 - 2 * ((0 : Fin 2) : ℕ) : ℤ) : ℂ) / 2 = 1 / 2 := by norm_num
      have e3 : ((((2 : ℕ) : ℤ) - 1 - 2 * ((1 : Fin 2) : ℕ) : ℤ) : ℂ) / 2 = -(1 / 2) := by norm_num
      have e4 : (((2 : ℕ) : ℂ) - 1) / 2 = 1 / 2 := by norm_num
      rw [e2, e3, e4, absPow_neg, e1]
      simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
      generalize absPow k (1 / 2) (t 0) = x
      generalize absPow k (1 / 2) (t 1) = y
      ext
      simp only [Units.val_mul, Units.val_inv_eq_inv_val]
      field_simp
    let f : σ.V →ₗ[ℂ] IndSp (points (Fin 2)) τ :=
      { toFun := fun v => ⟨⟨fun g => L (σ.ρ g v), fun p g => by
            refine Eq.trans ?_ (law p (σ.ρ g v))
            show L (σ.ρ (p * g) v) = _
            rw [map_mul, Module.End.mul_apply]⟩,
          mem_smoothPart_of_nhds (Filter.mem_of_superset
            (IsOpen.mem_nhds (σ.smooth v) (by simp)) fun g hg => by
              have hg' : σ.ρ g v = v := hg
              apply Subtype.ext
              funext x
              show L (σ.ρ (x * g) v) = L (σ.ρ x v)
              rw [map_mul, Module.End.mul_apply, hg'])⟩
        map_add' := fun c d => by ext g; simp
        map_smul' := fun c d => by ext g; simp }
    refine IsSubquotient.of_injective (ρ := parInd (points (Fin 2)) τ) ⟨f, fun g => ?_⟩ fun c d hcd => ?_
    · refine LinearMap.ext fun c => Subtype.ext (Subtype.ext (funext fun x => ?_))
      show L (σ.ρ x (σ.ρ g c)) = L (σ.ρ (x * g) c)
      rw [map_mul, Module.End.mul_apply]
    · refine sub_eq_zero.1 (sep_of_irred σ.ρ σ.irred L hL _ fun g => ?_)
      have : L (σ.ρ g c) = L (σ.ρ g d) := congrFun (congrArg (fun φ => φ.1.1) hcd) g
      rw [map_sub, map_sub, this, sub_self]
  · intro z v
    refine sub_eq_zero.1 (sep_of_irred σ.ρ σ.irred L hL _ fun g => ?_)
    have hc : g * GeneralLinearGroup.scalar (Fin 2) z =
        GeneralLinearGroup.scalar (Fin 2) z * aff (z / z) 0 * g := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [aff, GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_succ, mul_comm]
    rw [map_sub, map_sub, ← Module.End.mul_apply, ← map_mul, hc, map_mul, Module.End.mul_apply, h]
    simp

end SlopeTestRemainingChoices

theorem UpperTheory.isSubquotient_principalSeries_of_borel_functional :
    ∀ (F : Type) [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (σ : SmIrr (GL (Fin 2) (w.adicCompletion F))) (μ₁ μ₂ : (w.adicCompletion F)ˣ →* ℂˣ) (L : σ.V →ₗ[ℂ] ℂ), L ≠ 0 → (∀ (a d : (w.adicCompletion F)ˣ) (x : w.adicCompletion F) v, L (σ.ρ (Matrix.GeneralLinearGroup.scalar (Fin 2) d * aff (a / d) x) v) = ((μ₁ a * μ₂ d : ℂˣ) : ℂ) * L v) → GlobalTheory.SmGL.IsSmoothChar μ₁ ∧ GlobalTheory.SmGL.IsSmoothChar μ₂ ∧ GlobalTheory.SmGL.IsSubquotient σ.ρ (Hi.PS ![μ₁ * GlobalTheory.SmGL.absPow (w.adicCompletion F) (-1), μ₂]) ∧ ∀ (z : (w.adicCompletion F)ˣ) v, σ.ρ (Matrix.GeneralLinearGroup.scalar (Fin 2) z) v = ((μ₁ z * μ₂ z : ℂˣ) : ℂ) • v := by
  intro F _ _ w σ μ₁ μ₂ L hL h
  exact finiteRing_sq_sub_mul_sq_eq_of_card σ μ₁ μ₂ L hL h
end

