import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0262
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0347
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Classifies
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0028
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0037
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0036
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0175
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0029
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0027

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ArchimedeanUnitaryLeISupEmbUAndCommute
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.BasicNotions
open scoped TensorProduct

section
open GlobalTheory.DefU Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem infinite_unitary_generated_by_embeddings (s : Finset (InfinitePlace E)) :
    ∀ g ∈ infU E n, (∀ w, w ∉ s → evGL w (cInf g) = 1) → g ∈ ⨆ τ : E →+* ℂ, embU n τ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro g hg h
    have h2 : GeneralLinearGroup.map (pFin E) g.1 = 1 := hg
    have h1 : cInf g = 1 := gl_ext_evGL fun w => by
      rw [h w (Finset.notMem_empty w), map_one]
    have : g = 1 := by
      refine Subtype.ext (ga_ext ?_ ?_)
      · change cInf g = cInf 1
        rw [h1, map_one]
      · rw [h2]
        exact (map_one _).symm
    rw [this]
    exact one_mem _
  | insert v s hv ih =>
    intro g hg h
    have hr : (embRet v.embedding g : UA E n) ∈ embU n v.embedding := (embRet v.embedding g).2
    have hr' : (embRet v.embedding g : UA E n) ∈ ⨆ τ : E →+* ℂ, embU n τ :=
      (le_iSup (fun τ : E →+* ℂ => embU n τ) v.embedding) hr
    have hk : (embRet v.embedding g : UA E n)⁻¹ * g ∈ ⨆ τ : E →+* ℂ, embU n τ := by
      refine ih _ (mul_mem (inv_mem (embU_le_infU _ hr)) hg) fun w hw => ?_
      rw [map_mul, map_inv, cInf_embRet, map_mul, map_inv, InfinitePlace.mk_embedding]
      by_cases e : w = v
      · subst e
        rw [evGL_cutGL_self, inv_mul_cancel]
      · rw [evGL_cutGL_of_ne e, h w (by simp [e, hw]), inv_one, one_mul]
    simpa using mul_mem hr' hk

end

open GlobalTheory.DefU Matrix in
theorem UpperTheory.archimedeanUnitary_le_iSup_embU_and_commute :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), infU E n ≤ (⨆ τ : E →+* ℂ, embU n τ) ∧ ∀ τ τ' : E →+* ℂ, InfinitePlace.mk τ ≠ InfinitePlace.mk τ' → ∀ a ∈ embU (E := E) n τ, ∀ b ∈ embU n τ', a * b = b * a := by
  intro E _ _ _ n
  refine ⟨fun g hg => infinite_unitary_generated_by_embeddings Finset.univ g hg fun w hw => (hw (Finset.mem_univ w)).elim, ?_⟩
  intro τ τ' hne a ha b hb
  have h2 : GeneralLinearGroup.map (pFin E) b.1 = 1 := hb.1
  refine Subtype.ext (ga_ext ?_ ?_)
  · change cInf (a * b) = cInf (b * a)
    rw [map_mul, map_mul]
    refine gl_ext_evGL fun w => ?_
    rw [map_mul, map_mul]
    by_cases h : w = InfinitePlace.mk τ'
    · rw [evGL_cInf_of_mem ha (h ▸ hne.symm), one_mul, mul_one]
    · rw [evGL_cInf_of_mem hb h, one_mul, mul_one]
  · simp only [Subgroup.coe_mul, map_mul, h2, one_mul, mul_one]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusTraceNormNonzeroLogBound
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

theorem UpperTheory.frobenius_trace_norm_nonzero_log_bound :
    ∀ (q e : ℕ), 7 ≤ q → 1 ≤ e → ∀ (D : TrData q e) (Orb : Type) [Fintype Orb] (z : Orb → ℂ), (∀ o, ∃ k : ℕ, 0 < k ∧ z o ^ k = 1) → (∀ σ : ℂ ≃+* ℂ, ∃ u : Orb ≃ Orb, ∀ o, z (u o) = σ (z o)) → ∃ NN : ℤ, NN ≠ 0 ∧ Real.log |(NN : ℝ)| ≤ Fintype.card Orb * Nat.card D.S * (2 * e * Real.log q + 1) ∧ ∀ (l : ℕ) [Fact l.Prime], ¬ l ∣ q → ∀ (ι : Qbar l ≃+* ℂ) (Γ : Type) [Group Γ] (g : Γ) (admitted : (Γ →* GL (Fin 3) (Qbar l)) → Prop), D.Classifies ι g admitted → ∀ X : Orb → Finset (Γ →* GL (Fin 3) (Qbar l)), (∀ o, ∀ ρ ∈ X o, admitted ρ) → (∀ o, ∀ ρ ∈ X o, ∀ ρ' ∈ X o, RepIso ρ ρ' → ρ = ρ') → (∀ o, ∀ ρ ∈ X o, (ρ g : Matrix (Fin 3) (Fin 3) (Qbar l)).trace ≠ ι.symm (eis3 q e (z o))) ∧ ‖((NN : ℤ) : Qbar l)‖ ≤ ∏ o, ∏ ρ ∈ X o, ‖(ρ g : Matrix (Fin 3) (Fin 3) (Qbar l)).trace - ι.symm (eis3 q e (z o))‖ := by
  intro q e hq he D Orb _ z hz hσ
  classical
  have := D.fin
  letI : Fintype D.S := Fintype.ofFinite D.S
  let f : Orb → D.S → ℂ := fun o s => (q : ℂ) ^ e * (D.t s - eis3 q e (z o))
  have key : ∀ o s, D.t s ≠ eis3 q e (z o) ∧ IsIntegral ℤ (f o s) ∧
      Real.log ‖f o s‖ ≤ 2 * e * Real.log q + 1 := by
    intro o s
    obtain ⟨k, hk, hzk⟩ := hz o
    exact UpperTheory.eisenstein_trace_difference_log_bound q e k hq he hk (z o) (D.t s) hzk (D.bd s) (D.int s)
  have hq0 : (q : ℂ) ≠ 0 := by
    have : q ≠ 0 := by omega
    exact_mod_cast this
  have hf0 : ∀ o s, f o s ≠ 0 := fun o s =>
    mul_ne_zero (pow_ne_zero _ hq0) (sub_ne_zero.2 (key o s).1)
  obtain ⟨n, hn⟩ := UpperTheory.exists_int_eq_prod_of_galois_permuted_integral (Orb × D.S) (fun p => f p.1 p.2) (fun p => (key p.1 p.2).2.1) (by
    intro σ
    obtain ⟨u, hu⟩ := hσ σ
    obtain ⟨v, hv⟩ := D.conj σ
    refine ⟨u.prodCongr v, fun p => ?_⟩
    simp [f, eis3, hu, hv])
  refine ⟨n, ?_, ?_, ?_⟩
  · intro h
    rw [h, Int.cast_zero] at hn
    exact Finset.prod_ne_zero_iff.2 (fun p _ => hf0 p.1 p.2) hn.symm
  · have h1 : |(n : ℝ)| = ∏ p : Orb × D.S, ‖f p.1 p.2‖ := by
      rw [← norm_prod, ← hn, Complex.norm_intCast]
    rw [h1, Real.log_prod (fun p _ => norm_ne_zero_iff.2 (hf0 p.1 p.2))]
    refine (Finset.sum_le_sum (fun p _ => (key p.1 p.2).2.2)).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Nat.card_eq_fintype_card, nsmul_eq_mul]
    push_cast
    exact le_rfl
  · intro l _ hl ι Γ _ g admitted hcl X hX hinj
    obtain ⟨cl, hc1, hc2⟩ := hcl
    refine ⟨fun o ρ hρ h => ?_, ?_⟩
    · rw [hc2 ⟨ρ, hX o ρ hρ⟩] at h
      exact (key o _).1 (ι.symm.injective h)
    · have hq1 : ‖(q : Qbar l)‖ = 1 := by
        rw [← map_natCast (algebraMap ℚ_[l] (Qbar l)), norm_algebraMap', Padic.norm_natCast_eq_one_iff]
        exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hl
      have h2 := UpperTheory.adicNorm_prod_le_prod_of_injective_classes l ι Orb D.S _ f (fun o s => (key o s).2.1) X
        (fun o r => cl ⟨r.1, hX o r.1 r.2⟩)
        (fun o r r' h => Subtype.ext (hinj o _ r.2 _ r'.2 (hc1 _ _ h)))
      rw [← Fintype.prod_prod_type', ← hn, map_intCast] at h2
      refine h2.trans (le_of_eq (Finset.prod_congr rfl fun o _ => ?_))
      rw [← Finset.prod_coe_sort (X o)]
      refine Finset.prod_congr rfl fun r _ => ?_
      rw [hc2 ⟨r.1, hX o r.1 r.2⟩]
      simp only [f, map_mul, map_pow, map_natCast, map_sub, norm_mul, norm_pow, hq1, one_pow, one_mul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.JacquetBorelExistsTorusCongruenceFixed
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

theorem UpperTheory.jacquet_borel_exists_torus_congruence_fixed :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (s : Multiset (IrrGL k)) (γ : (ValueGroupWithZero k)ˣ), γ ≤ 1 → HasSupport π s → (∀ y ∈ s, ∃ χ hχ, y = IrrGL.ofChar χ hχ ∧ ∀ u : kˣ, valuation k ((u : k) - 1) < γ → χ u = 1) →
    Nontrivial (Jacquet π (unipB k (Fin N))) →
    ∃ y : Jacquet π (unipB k (Fin N)), y ≠ 0 ∧ ∀ t : Fin N → kˣ, (∀ i, valuation k ((t i : k) - 1) < γ) → jacBU π t y = y := by
  intro hG hZ k _ _ _ _ N V _ _ π s γ hγ hs hχ hnt
  let f := Equiv.sigmaUnique (Fin N) fun _ : Fin N => Fin 1
  have hmono : StrictMono (blk f) := fun a b h => by simpa [blk, f] using h
  have h3 : twKer π (unipRad k f) 1 = twKer π (unipB k (Fin N)) 1 := by
    rw [EmptyBlocks.unipRad_eq k f hmono]
  let E : Jacquet π (unipRad k f) ≃ₗ[ℂ] Jacquet π (unipB k (Fin N)) := Submodule.quotEquivOfEq _ _ h3
  have hE : ∀ v : V, E (Submodule.Quotient.mk v) = Submodule.Quotient.mk v := fun _ => rfl
  obtain ⟨y, hy0, hy⟩ := UpperTheory.jacquet_exists_levi_congruence_fixed_of_char_support hG hZ k N V π s γ hγ hs hχ f E.toEquiv.nontrivial
  refine ⟨E y, E.map_ne_zero_iff.2 hy0, fun t ht => ?_⟩
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have hγ' : (γ : ValueGroupWithZero k) ≤ 1 := hγ
  have h1 := hy (EmptyBlocks.torusToLevi k f t) fun a i j => by
    rw [EmptyBlocks.val_torusToLevi, Subsingleton.elim i j, Matrix.sub_apply, Matrix.diagonal_apply_eq,
      Matrix.one_apply_eq]
    exact ht _
  have hv : ∀ i, valuation k (t i : k) = 1 := fun i => by
    have := Valuation.map_one_add_of_lt (valuation k) ((ht i).trans_le hγ')
    rwa [add_sub_cancel] at this
  have hd : deltaHalf k (fun _ : Fin N => Fin 1) (EmptyBlocks.torusToLevi k f t) = 1 := by
    rw [deltaHalf_apply]
    refine Finset.prod_eq_one fun a _ => isUnram_absPow k _ _ ?_
    have := (EmptyBlocks.det_torusToLevi k f t a).trans (Fin.prod_univ_one _)
    exact (congrArg (fun u : kˣ => valuation k (u : k)) this).trans (hv _)
  rw [jac_mk, hd, inv_one, Units.val_one, one_smul, EmptyBlocks.leviEmb_torusToLevi] at h1
  have h2 := congrArg E h1
  rw [hE, hE] at h2
  rw [hE, jacBU_mk]
  exact h2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.JacquetBorelNontrivialOfCharacterSupport
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

theorem UpperTheory.jacquet_borel_nontrivial_of_character_support :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (s : Multiset (IrrGL k)), HasSupport π s → (∀ y ∈ s, y.1 = 1) → Nontrivial (Jacquet π (unipB k (Fin N))) := by
  intro hG hZ k _ _ _ _ N V _ _ π s hs h1
  have hV : Nontrivial V := by
    obtain ⟨h, x, hx, hirr, hcu, e0, hsub⟩ := hs
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    obtain ⟨a, b, hab⟩ := (hirr.toNontrivial).exists_pair_ne
    apply hab
    obtain ⟨a1, a2⟩ := a
    obtain ⟨b1, b2⟩ := b
    have : a1 = b1 := Subsingleton.elim _ _
    subst this
    rfl
  let S : ∀ {r : ℕ} {d : Fin r → ℕ}, ((a : Fin r) × Fin (d a) ≃ Fin N) → Finset (Fin N × Fin N) :=
    fun e => Finset.univ.filter (fun pq : Fin N × Fin N => ¬ blk e pq.1 < blk e pq.2)
  have key : ∀ m : ℕ, ∀ (r : ℕ) (d : Fin r → ℕ) (e : (a : Fin r) × Fin (d a) ≃ Fin N),
      (S e).card ≤ m → Nontrivial (Jacquet π (unipRad k e)) →
      Nontrivial (Jacquet π (unipB k (Fin N))) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro r d e hm hJ
      by_cases hd : ∀ a, d a ≤ 1
      · exact UpperTheory.jacquet_borel_nontrivial_of_blocks_le_one k N V π r d e hd hJ
      push_neg at hd
      obtain ⟨j, hj⟩ := hd
      obtain ⟨t, c, f, hf, hmono, p, q, hpq, hnpq⟩ :=
        UpperTheory.jacquet_finer_parabolic_of_character_support hG hZ k N V π s hs h1 r d e j (by omega) hJ
      have hlt : (S f).card < (S e).card := by
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset]
        · refine ⟨(p, q), ?_, ?_⟩
          · simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
            exact hnpq
          · simp [S, hpq]
        · intro x hx
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
          exact fun h => hx (hmono _ _ h)
      exact ih _ (lt_of_lt_of_le hlt hm) t c f le_rfl hf
  let e1 : (a : Fin 1) × Fin ((fun _ : Fin 1 => N) a) ≃ Fin N :=
    { toFun := fun p => p.2
      invFun := fun i => ⟨0, i⟩
      left_inv := by
        rintro ⟨a, i⟩
        fin_cases a
        rfl
      right_inv := fun i => rfl }
  have hU : ∀ g ∈ unipRad k e1, g = 1 := by
    intro g hg
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hg
    have h0 := congrFun (MonoidHom.mem_ker.mp hp) 0
    ext i j
    have h2 := congrArg (fun u : GL (Fin N) k => (u : Matrix (Fin N) (Fin N) k) i j) h0
    simpa [leviProj, diagBlock, MonoidHom.pi, e1] using h2
  have hker : twKer π (unipRad k e1) 1 = ⊥ := by
    rw [twKer, Submodule.span_eq_bot]
    rintro w ⟨n, v, rfl⟩
    rw [hU n.1 n.2]
    simp
  apply key _ 1 (fun _ => N) e1 le_rfl
  show Nontrivial (V ⧸ twKer π (unipRad k e1) 1)
  rw [hker, Submodule.Quotient.nontrivial_iff]
  exact bot_ne_top
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.TracesFromEigenvaluesRank2
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

theorem UpperTheory.traces_from_eigenvalues_rank2 :
    ∀ (p h e : ℕ), ∀ D : EigData 2 p ![(e : ℤ), -(e : ℤ)] 0, ∃ (T : TrData (p ^ h) e) (u : D.S ≃ T.S), ∀ s, T.t (u s) = 1 + ((D.β s).map fun b => b⁻¹ ^ h).sum := by
  intro p h e D
  refine ⟨⟨D.S, D.fin, fun s => 1 + ((D.β s).map fun b => b⁻¹ ^ h).sum, ?_, ?_, ?_⟩, Equiv.refl _, fun s => rfl⟩
  · intro σ
    obtain ⟨u, hu⟩ := D.conj σ
    refine ⟨u, fun s => ?_⟩
    rw [hu, map_add, map_one, map_multiset_sum, Multiset.map_map, Multiset.map_map]
    congr 2
    refine Multiset.map_congr rfl fun b _ => ?_
    simp only [Function.comp, map_pow, map_inv₀]
  · intro s
    obtain ⟨x, y, hxy⟩ := Multiset.card_eq_two.1 (D.card s)
    have hx : ‖x‖ = 1 := by simpa using D.pure s x (by rw [hxy]; simp)
    have hy : ‖y‖ = 1 := by simpa using D.pure s y (by rw [hxy]; simp)
    have e1 : ((D.β s).map fun b => b⁻¹ ^ h).sum = x⁻¹ ^ h + y⁻¹ ^ h := by
      rw [hxy]; simp
    have h1 : ‖x⁻¹ ^ h‖ = 1 := by simp [hx]
    have h2 : ‖y⁻¹ ^ h‖ = 1 := by simp [hy]
    rw [e1]
    have h3 := norm_add_le (1 : ℂ) (x⁻¹ ^ h + y⁻¹ ^ h)
    have h4 := norm_add_le (x⁻¹ ^ h) (y⁻¹ ^ h)
    rw [norm_one] at h3
    linarith
  · intro s
    obtain ⟨x, y, hxy⟩ := Multiset.card_eq_two.1 (D.card s)
    have hm : ∀ i, (![(e : ℤ), -(e : ℤ)] : Fin 2 → ℤ) i ≤ (e : ℤ) := by
      intro i
      fin_cases i
      · simp
      · simp
    have hx := D.intInv e hm s x (by rw [hxy]; simp)
    have hy := D.intInv e hm s y (by rw [hxy]; simp)
    rw [zpow_natCast] at hx hy
    have e1 : ((D.β s).map fun b => b⁻¹ ^ h).sum = x⁻¹ ^ h + y⁻¹ ^ h := by
      rw [hxy]; simp
    have e2 : (((p ^ h : ℕ) : ℂ)) ^ e * (1 + (x⁻¹ ^ h + y⁻¹ ^ h)) =
        ((p ^ (h * e) : ℕ) : ℂ) + (((p : ℂ) ^ e * x⁻¹) ^ h + ((p : ℂ) ^ e * y⁻¹) ^ h) := by
      push_cast; ring
    rw [e1, e2]
    refine IsIntegral.add ?_ ((hx.pow h).add (hy.pow h))
    exact_mod_cast (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := ((p ^ (h * e) : ℕ) : ℤ)))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.TracesFromEigenvaluesRank3
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

theorem UpperTheory.traces_from_eigenvalues_rank3 :
    ∀ (q e : ℕ), 1 ≤ q → ∀ D : EigData 3 q ![(e : ℤ) - 1, -1, -(e : ℤ) - 1] (1 - ((3 : ℕ) : ℤ)), ∃ (T : TrData q e) (u : D.S ≃ T.S), ∀ s, T.t (u s) = ((D.β s).map fun b => ((q : ℂ) * b)⁻¹).sum := by
  intro q e hq D
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hqR.ne'
  refine ⟨⟨D.S, D.fin, fun s => ((D.β s).map fun b => ((q : ℂ) * b)⁻¹).sum, ?_, ?_, ?_⟩, Equiv.refl _, fun s => rfl⟩
  · intro σ
    obtain ⟨u, hu⟩ := D.conj σ
    refine ⟨u, fun s => ?_⟩
    rw [hu, map_multiset_sum, Multiset.map_map, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun b _ => ?_
    simp
  · intro s
    refine (norm_multiset_sum_le _).trans ?_
    have h := Multiset.sum_le_card_nsmul (((D.β s).map fun b => ((q : ℂ) * b)⁻¹).map fun x => ‖x‖) (1 : ℝ) (by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hx
      obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.1 hy
      have hp := D.pure s b hb
      have he : (((1 - ((3 : ℕ) : ℤ) : ℤ) : ℝ) / 2) = -1 := by push_cast; norm_num
      rw [he, Real.rpow_neg_one] at hp
      rw [norm_inv, norm_mul, hp, Complex.norm_natCast, mul_inv_cancel₀ hqR.ne', inv_one])
    rw [Multiset.card_map, Multiset.card_map, D.card] at h
    simpa using h
  · intro s
    rw [← Multiset.sum_map_mul_left]
    refine (integralClosure ℤ ℂ).multiset_sum_mem ?_
    intro x hx
    obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.1 hx
    have h := D.intInv ((e : ℤ) - 1) (by
      intro i
      fin_cases i <;> simp <;> omega) s b hb
    have he : (q : ℂ) ^ e * ((q : ℂ) * b)⁻¹ = (q : ℂ) ^ ((e : ℤ) - 1) * b⁻¹ := by
      rw [zpow_sub_one₀ hqC, zpow_natCast, mul_inv, mul_assoc]
    rw [mem_integralClosure_iff, he]
    exact h
end

