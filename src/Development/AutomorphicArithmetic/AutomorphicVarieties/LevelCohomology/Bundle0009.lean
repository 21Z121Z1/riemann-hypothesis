import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.FiniteResidue
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.LemmaK
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0004
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0006
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0006
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0005
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0007
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0008
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ResidueCharMemLevelPrimes
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle0002

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.CobDown
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.X

private theorem cob_up {l : ℕ} [Fact l.Prime] (O : Subalgebra ℤ_[l] (PadicAlgCl l)) {Γ : Type} [Group Γ]
    (θ : Γ →* Oˣ) (z : Γ → O) (D : Subgroup Γ) (h : CobOn θ z D) :
    ∃ m : PadicAlgCl l, ∀ g ∈ D, (z g : PadicAlgCl l) = ((θ g : O) : PadicAlgCl l) * m - m := by
  obtain ⟨a, ha, m, hm⟩ := h
  have ha' : (a : PadicAlgCl l) ≠ 0 := fun h => ha (Subtype.ext h)
  refine ⟨(m : PadicAlgCl l) / a, fun g hg => ?_⟩
  have h1 : (a : PadicAlgCl l) * z g = ((θ g : O) : PadicAlgCl l) * m - m := by
    exact_mod_cast congrArg Subtype.val (hm g hg)
  field_simp
  linear_combination h1

private theorem cob_down {l : ℕ} [Fact l.Prime] (O : Subalgebra ℤ_[l] (PadicAlgCl l)) {Γ : Type} [Group Γ]
    (θ : Γ →* Oˣ) (z : Γ → O) (m : PadicAlgCl l)
    (hm : ∀ g, (z g : PadicAlgCl l) = ((θ g : O) : PadicAlgCl l) * m - m) : CobOn θ z ⊤ := by
  by_cases h : ∃ g₀, (θ g₀ : O) ≠ 1
  · obtain ⟨g₀, hg₀⟩ := h
    refine ⟨θ g₀ - 1, sub_ne_zero.2 hg₀, z g₀, fun g _ => Subtype.ext ?_⟩
    push_cast
    rw [hm g, hm g₀]
    ring
  · push Not at h
    refine cobOn_of_eq_zero θ fun g _ => Subtype.ext ?_
    rw [hm g, h g]
    simp

theorem UpperTheory.V.X.So.soCoc :
    ∀ CK : ℝ, LemmaK CK → GlobalTheory.Published.PoitouTateDuality → LocalFinitenessK → LocalTateDualityK → ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (c : HV.Coef l) (ψ : G k Ω →* c.Oˣ), IsOpen (ψ.ker : Set (G k Ω)) → ∀ e : ℕ, 1 ≤ e → ∀ z : G k Ω → c.O, Coc (Chr.Psi l e ψ)⁻¹ z → Alg.AdicCont (maximalIdeal c.O) z → (∀ A : ValuationSubring Ω, CobOn (Chr.Psi l e ψ)⁻¹ z (Ine (F := k) A)) → (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → CobOn (Chr.Psi l e ψ)⁻¹ z (Dec (F := k) A)) → CobOn (Chr.Psi l e ψ)⁻¹ z ⊤ := by
  intro CK hK hPT hLF hLT k Ω _ _ _ _ _ l _ c ψ hψ e he z hz hc h1 h2
  let ψ' : G k Ω →* (PadicAlgCl l)ˣ := (Units.map c.O.val.toMonoidHom).comp ψ
  have hψ' : IsOpen (ψ'.ker : Set (G k Ω)) := by
    refine Subgroup.isOpen_mono (H₁ := ψ.ker) (fun g hg => ?_) hψ
    have : ψ g = 1 := hg
    show Units.map c.O.val.toMonoidHom (ψ g) = 1
    rw [this, map_one]
  have hcz : Continuous z := ((UpperTheory.V.X.So.adicCont l c).2 _ z).1 hc
  obtain ⟨m, hm⟩ := UpperTheory.V.X.soBar CK hK hPT hLF hLT k Ω l ψ' hψ' e he
    (fun g => (((Chr.Psi l e ψ)⁻¹ g : c.O) : PadicAlgCl l)) (fun g => by
      have h0 : (((Chr.Psi l e ψ)⁻¹ g : c.Oˣ) : c.O) * (ψ g : c.O) * algebraMap ℤ_[l] c.O (cycZ k Ω l g : ℤ_[l]) ^ e = 1 := by
        have e1 : algebraMap ℤ_[l] c.O (cycZ k Ω l g : ℤ_[l]) = (chiO k Ω l c.O g : c.O) := rfl
        rw [e1, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← Units.val_mul, Units.val_eq_one]
        show (chiO k Ω l c.O g ^ (e : ℤ) * ψ g)⁻¹ * ψ g * chiO k Ω l c.O g ^ e = 1
        rw [zpow_natCast, mul_assoc, mul_comm (ψ g), inv_mul_cancel]
      have h3 := congrArg c.O.val h0
      rw [map_mul, map_mul, map_pow, map_one, AlgHom.commutes] at h3
      exact h3)
    (fun g => (z g : PadicAlgCl l)) (continuous_subtype_val.comp hcz)
    (fun g h => by exact_mod_cast congrArg Subtype.val (hz g h))
    (fun A => cob_up c.O _ z _ (h1 A)) (fun A hA => cob_up c.O _ z _ (h2 A hA))
  exact cob_down c.O _ z m hm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.H1cZero
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.X

theorem UpperTheory.V.X.h1cZero :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) {SP : Set (HeightOneSpectrum (𝓞 ℚ))} {T Q : Finset ℕ} (v0 : T) {pl : ℕ → ValuationSubring Ω} {K : Subgroup (G ℚ Ω)}, GalData l SP T Q pl K → K.Normal → ∀ (k : Type) [Field k] (M : Type) [AddCommGroup M] [Module k M] (ρ : Representation k (GS Ω SP) M) (γ : G ℚ Ω →* kˣ), (∀ g m, ρ (toGS Ω SP g) m = (γ g : k) • m) → K ≤ γ.ker → (∀ v ∈ T, ∃ g ∈ Dec (F := ℚ) (pl v), γ g ≠ 1) → Van T pl K γ → (galFrame SP T Q v0 pl K).H1c ρ = ⊥ := by
  intro Ω _ _ _ l SP T Q v0 pl K hD hK k _ M _ _ ρ γ hρ hKγ hT hV
  rw [eq_bot_iff]
  rintro ⟨c, b⟩ ⟨h1, h2, h3, h4, h5⟩
  have h3' : ∀ q : Q, ∀ g ∈ Ine (F := ℚ) (pl q), g ∈ K → c (toGS Ω SP g) = 0 := by
    intro q g hg hgK
    exact h3 q ⟨g, Ine_le_Dec _ hg⟩ (Subgroup.mem_subgroupOf.2 ⟨hg, hgK⟩)
  have h4' : ∀ v : T, ∀ g ∈ Dec (F := ℚ) (pl v), c (toGS Ω SP g) = (γ g : k) • b v - b v := by
    intro v g hg
    rw [← hρ]
    exact h4 v ⟨g, hg⟩
  have h5' : b v0 = 0 := h5
  obtain ⟨S, e, hS, -, hTp, hQ⟩ := galIdx Ω l v0 hD
  have hcont : Continuous (toGS Ω SP) := continuous_quot_mk
  have hc : ∀ g, c (toGS Ω SP g) = 0 := by
    intro g
    refine (Module.forall_dual_apply_eq_zero_iff k _).1 fun f => ?_
    have hz : ∀ g h, f (c (toGS Ω SP (g * h))) = f (c (toGS Ω SP g)) + (γ g : k) * f (c (toGS Ω SP h)) := by
      intro g h
      have := h2 (toGS Ω SP g) (toGS Ω SP h)
      simp only at this
      rw [map_mul, this, hρ, map_add, map_smul, smul_eq_mul]
    have hu := unrOf Ω k γ K hKγ SP T (fun s => f (c s)) hz (by
      intro v hv
      obtain ⟨y, hy⟩ := e.surjective ⟨v, by rw [hS] at hv; exact hv⟩
      have hv' : (e y).1 = v := congrArg Subtype.val hy
      rcases y with t | q
      · have h := hTp t ((t.1 : ℕ) : 𝓞 ℚ)
        have e' : algebraMap ℚ Ω (((t.1 : ℕ) : 𝓞 ℚ) : ℚ) = ((t.1 : ℕ) : Ω) := by simp
        rw [e', hv'] at h
        exact Or.inl ⟨t.1, t.2, h.1 (hD.isOver _ (Or.inl t.2))⟩
      · refine Or.inr ⟨pl q, hv' ▸ hQ q, fun g hg hgK => ?_⟩
        simp only [h3' q g hg hgK, map_zero])
    obtain ⟨m, hm⟩ := hV (fun g => f (c (toGS Ω SP g))) ((h1.comp_continuous hcont).comp f) hz hu (by
      intro v hv
      refine ⟨f (b ⟨v, hv⟩), fun g hg => ?_⟩
      simp only [h4' ⟨v, hv⟩ g hg, map_sub, map_smul, smul_eq_mul])
    obtain ⟨g0, hg0, hne⟩ := hT v0 v0.2
    have h0 := hm g0
    simp only [h4' v0 g0 hg0, h5', smul_zero, sub_zero, map_zero] at h0
    have hm0 : m = 0 := by
      have : ((γ g0 : k) - 1) * m = 0 := by rw [sub_mul, one_mul]; exact h0.symm
      exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 fun h => hne (Units.ext h))
    have := hm g
    simpa [hm0] using this
  refine (Submodule.mem_bot k).2 (Prod.ext (funext fun s => ?_) (funext fun v => ?_))
  · obtain ⟨g, rfl⟩ : ∃ g, toGS Ω SP g = s := QuotientGroup.mk_surjective s
    exact hc g
  · obtain ⟨g0, hg0, hne⟩ := hT v.1 v.2
    have h0 := h4' v g0 hg0
    rw [hc] at h0
    have : ((γ g0 : k) - 1) • b v = 0 := by rw [sub_smul, one_smul]; exact h0.symm
    exact (smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 fun h => hne (Units.ext h))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcGalTail
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.X

theorem UpperTheory.V.X.galTail :
    LocalFiniteness → GlobalFiniteness → GlobalTheory.Published.PoitouTateNormalised → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {SP : Set (HeightOneSpectrum (𝓞 ℚ))} {T Q : Finset ℕ} (v0 : T) {pl : ℕ → ValuationSubring Ω} {K : Subgroup (G ℚ Ω)}, GalData l SP T Q pl K → ∀ (k : Type) [Field k] [Finite k] [CharP k l] (M : Type) [AddCommGroup M] [Module k M] [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k (GS Ω SP) M), ContAction ρ → finrank k (shaF (galFrame SP T Q v0 pl K) ρ) + ∑ v : T, finrank k (H2 (ρ.comp (locHom SP (pl v)))) + ∑ q : Q, finrank k (H2 (ρ.comp (locHom SP (pl q)))) = finrank k (H2 ρ) + finrank k (Loc.H0dual (cycK Ω l k) (ρ.comp (toGS Ω SP))) := by
  intro lf gf pt Ω _ _ _ l _ SP T Q v0 pl K hD k _ _ _ M _ _ _ _ _ ρ hρ
  obtain ⟨S, e, rfl, hl, hT, hQ⟩ := galIdx Ω l v0 hD
  let B : T ⊕ Q → ValuationSubring Ω := Sum.elim (fun v => pl v) (fun q => pl q)
  have hB : ∀ x, IsPlaceOver (B x) (e x).1 := by
    rintro (v | q)
    · exact hT v
    · exact hQ q
  have hA : ∀ v : S, IsPlaceOver (B (e.symm v)) v.1 := fun v => by
    have := hB (e.symm v)
    rwa [e.apply_symm_apply] at this
  have h := ptTail lf gf pt Ω l hD.l_odd S hl (fun v => B (e.symm v)) hA k M ρ hρ
  have hsum : ∑ v : S, finrank k (H2 (ρ.comp (locHom (S : Set (HeightOneSpectrum (𝓞 ℚ))) (B (e.symm v))))) =
      ∑ v : T, finrank k (H2 (ρ.comp (locHom (S : Set (HeightOneSpectrum (𝓞 ℚ))) (pl v)))) +
        ∑ q : Q, finrank k (H2 (ρ.comp (locHom (S : Set (HeightOneSpectrum (𝓞 ℚ))) (pl q)))) := by
    rw [e.symm.sum_comp (fun x => finrank k (H2 (ρ.comp (locHom (S : Set (HeightOneSpectrum (𝓞 ℚ))) (B x))))),
      Fintype.sum_sum_type]
    rfl
  have hsha : Sha2 ρ (fun v => locHom (S : Set (HeightOneSpectrum (𝓞 ℚ))) (B (e.symm v)))
      (fun v => continuous_locHom _ (B (e.symm v))) = shaF (galFrame (S : Set (HeightOneSpectrum (𝓞 ℚ))) T Q v0 pl K) ρ := by
    have h1 := e.symm.iInf_comp (g := fun x => LinearMap.ker (resH2 ρ (locHom (S : Set (HeightOneSpectrum (𝓞 ℚ))) (B x)) (continuous_locHom _ (B x))))
    rw [iInf_sum] at h1
    exact h1
  rw [hsum, hsha, ← add_assoc] at h
  exact h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcSpAct
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Module UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.X

private theorem ps_eq {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c)
    (i : Fin 4) (g : G ℚ Ω) : D.ps i g = D.al g ^ lamW i * D.Psi g ^ muW i := by
  fin_cases i <;> simp [Raw.ps, Raw.th, lamW, muW]

private theorem rbar_eq {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c)
    (g : G ℚ Ω) : D.rbar g = Matrix.diagonal fun i => residue c.O (D.ps i g : c.O) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [Raw.rbar, Raw.r0, mapRep, diagRep]
  · simp [Raw.rbar, Raw.r0, mapRep, diagRep, Matrix.diagonal_apply, h]

theorem UpperTheory.V.X.spAct :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (rb : D.Gam →* M4 (ResidueField c.O)), rb.comp (toGS Ω D.SP) = D.rbar → ∀ (h : (form c.O).Normalises rb) (j : ℤ × ℤ) (g : G ℚ Ω) (Y : (form c.O).gw (ResidueField c.O) j), Alg.FormData.adRep h j (toGS Ω D.SP g) Y = Raw.bar (D.al ^ j.1 * D.Psi ^ j.2) g • Y := by
  intro Ω _ _ _ l _ c D rb hrb h j g Y
  apply Subtype.ext
  show rb (toGS Ω D.SP g) * (Y : Matrix (Fin 4) (Fin 4) (ResidueField c.O)) * rb (toGS Ω D.SP g)⁻¹ = _
  rw [← map_inv, ← MonoidHom.comp_apply rb, ← MonoidHom.comp_apply rb, hrb, rbar_eq, rbar_eq]
  ext a b
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Submodule.coe_smul, Matrix.smul_apply, smul_eq_mul]
  by_cases hab : w4 a - w4 b = j
  · have key : D.ps a g * D.ps b g⁻¹ = (D.al ^ j.1 * D.Psi ^ j.2) g := by
      subst hab
      rw [map_inv, ps_eq, ps_eq, MonoidHom.mul_apply, MonoidHom.zpow_apply, MonoidHom.zpow_apply]
      simp only [w4, Prod.fst_sub, Prod.snd_sub, zpow_sub, div_eq_mul_inv, mul_inv]
      ac_rfl
    rw [Raw.bar, ← key, Units.val_mul, map_mul]
    ring
  · have hz : (Y : Matrix (Fin 4) (Fin 4) (ResidueField c.O)) a b = 0 := (Submodule.mem_inf.1 Y.2).2 a b hab
    simp [hz]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcSpDim
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Module UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.X

section
variable (O : Type) [CommRing O] (k : Type) [Field k] [Algebra O k]

private theorem spDim_JR : (form O).JR k = J4 k := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Alg.FormData.JR, form, J4]

private theorem spDim_mem (j : ℤ × ℤ) (Y : M4 k) : Y ∈ (form O).gw k j ↔
    (Y 3 1 = Y 2 0 ∧ Y 3 2 = -Y 1 0 ∧ Y 3 3 = -Y 0 0 ∧ Y 2 2 = -Y 1 1 ∧ Y 2 3 = -Y 0 1 ∧ Y 1 3 = Y 0 2) ∧
      ∀ a b, wt a b ≠ j → Y a b = 0 := by
  have e : Y ∈ (form O).gw k j ↔ (Y.transpose * (form O).JR k + (form O).JR k * Y = 0 ∧
      ∀ a b, (form O).blk a ≠ (form O).blk b → Y a b = 0) ∧ ∀ a b, wt a b ≠ j → Y a b = 0 := Iff.rfl
  rw [e, spDim_JR]
  refine and_congr_left fun _ => ⟨fun ⟨h, _⟩ => ?_, fun ⟨h1, h2, h3, h4, h5, h6⟩ => ⟨?_, fun a b h => absurd rfl h⟩⟩
  · have h1 := congrFun (congrFun h 0) 1
    have h2 := congrFun (congrFun h 0) 2
    have h3 := congrFun (congrFun h 0) 3
    have h4 := congrFun (congrFun h 1) 2
    have h5 := congrFun (congrFun h 1) 3
    have h6 := congrFun (congrFun h 2) 3
    simp [J4, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_four] at h1 h2 h3 h4 h5 h6
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · linear_combination h1
    · linear_combination h2
    · linear_combination h3
    · linear_combination h4
    · linear_combination h5
    · linear_combination -h6
  · ext a b
    fin_cases a <;> fin_cases b <;> simp [J4, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_four, h1, h2, h3, h4, h5, h6]

private theorem spDim_one (j : ℤ × ℤ) (B : M4 k) (a b : Fin 4) (hB : B ∈ (form O).gw k j) (hab : B a b = 1)
    (h : ∀ Y ∈ (form O).gw k j, Y a b = 0 → Y = 0) : finrank k ((form O).gw k j) = 1 := by
  refine finrank_eq_one (⟨B, hB⟩ : (form O).gw k j) ?_ ?_
  · intro e
    have : B = 0 := congrArg Subtype.val e
    rw [this] at hab
    simp at hab
  · intro Y
    refine ⟨Y.1 a b, Subtype.ext ?_⟩
    have := h (Y.1 a b • B - Y.1) (Submodule.sub_mem _ (Submodule.smul_mem _ _ hB) Y.2) (by simp [hab])
    exact sub_eq_zero.mp this

private theorem spDim_root (j : ℤ × ℤ) (B : M4 k) (a b : Fin 4) (hj : wt a b = j)
    (hB : B ∈ (form O).gw k (wt a b)) (hab : B a b = 1)
    (h : ∀ Y : M4 k, (Y 3 1 = Y 2 0 ∧ Y 3 2 = -Y 1 0 ∧ Y 3 3 = -Y 0 0 ∧ Y 2 2 = -Y 1 1 ∧ Y 2 3 = -Y 0 1 ∧ Y 1 3 = Y 0 2) →
      Y a b = 0 → Y b.rev a.rev = 0)
    (h' : ∀ c d, wt c d = wt a b → (c = a ∧ d = b) ∨ (c = b.rev ∧ d = a.rev)) :
    finrank k ((form O).gw k j) = 1 := by
  subst hj
  refine spDim_one O k _ B a b hB hab fun Y hY h0 => ?_
  obtain ⟨y1, y2⟩ := (spDim_mem O k _ Y).1 hY
  ext c d
  by_cases e : wt c d = wt a b
  · rcases h' c d e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h0
    · exact h Y y1 h0
  · exact y2 c d e

private theorem spDim_zero : finrank k ((form O).gw k 0) = 2 := by
  let f : (form O).gw k 0 →ₗ[k] k × k :=
    { toFun := fun Y => (Y.1 0 0, Y.1 1 1)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hf : Function.Bijective f := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro Y hY
      have h0 : Y.1 0 0 = 0 := congrArg Prod.fst hY
      have h1 : Y.1 1 1 = 0 := congrArg Prod.snd hY
      obtain ⟨⟨-, -, y3, y4, -, -⟩, y2⟩ := (spDim_mem O k _ Y.1).1 Y.2
      ext c d
      by_cases e : c = d
      · subst e
        fin_cases c <;> simp [h0, h1, y3, y4]
      · exact y2 c d fun n => e ((wt_eq_zero c d).1 n)
    · rintro ⟨x, y⟩
      refine ⟨⟨Matrix.diagonal ![x, y, -y, -x], (spDim_mem O k _ _).2 ⟨by simp, fun a b h => ?_⟩⟩, ?_⟩
      · exact Matrix.diagonal_apply_ne _ fun n => h ((wt_eq_zero a b).2 n)
      · rfl
  rw [(LinearEquiv.ofBijective f hf).finrank_eq]
  simp

private theorem spDim_B (a b : Fin 4) (B : M4 k)
    (h : B 3 1 = B 2 0 ∧ B 3 2 = -B 1 0 ∧ B 3 3 = -B 0 0 ∧ B 2 2 = -B 1 1 ∧ B 2 3 = -B 0 1 ∧ B 1 3 = B 0 2)
    (h' : ∀ c d, ¬ (c = a ∧ d = b) → ¬ (c = b.rev ∧ d = a.rev) → B c d = 0) : B ∈ (form O).gw k (wt a b) := by
  refine (spDim_mem O k _ _).2 ⟨h, fun c d e => h' c d ?_ ?_⟩
  · rintro ⟨rfl, rfl⟩; exact e rfl
  · rintro ⟨rfl, rfl⟩; exact e (wt_rev _ _)

end

theorem UpperTheory.V.X.spDim :
    ∀ (O : Type) [CommRing O] (k : Type) [Field k] [Algebra O k] (j : ℤ × ℤ), finrank k ((form O).gw k j) = dimP j := by
  intro O _ k _ _ j
  unfold dimP
  split_ifs with h0 hw
  · subst h0; exact spDim_zero O k
  · have key : ∀ (a b : Fin 4) (B : M4 k), wt a b = j → B a b = 1 →
        (B 3 1 = B 2 0 ∧ B 3 2 = -B 1 0 ∧ B 3 3 = -B 0 0 ∧ B 2 2 = -B 1 1 ∧ B 2 3 = -B 0 1 ∧ B 1 3 = B 0 2) →
        (∀ c d, ¬ (c = a ∧ d = b) → ¬ (c = b.rev ∧ d = a.rev) → B c d = 0) →
        (∀ Y : M4 k, (Y 3 1 = Y 2 0 ∧ Y 3 2 = -Y 1 0 ∧ Y 3 3 = -Y 0 0 ∧ Y 2 2 = -Y 1 1 ∧ Y 2 3 = -Y 0 1 ∧ Y 1 3 = Y 0 2) →
          Y a b = 0 → Y b.rev a.rev = 0) →
        (∀ c d, wt c d = wt a b → (c = a ∧ d = b) ∨ (c = b.rev ∧ d = a.rev)) → finrank k ((form O).gw k j) = 1 :=
      fun a b B e h1 h2 h3 h4 h5 => spDim_root O k j B a b e (spDim_B O k a b B h2 h3) h1 h4 h5
    simp only [wts, oddRoots, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with (rfl | rfl | rfl | rfl | rfl | rfl) | rfl | rfl | rfl
    · refine key 0 1 !![0, 1, 0, 0; 0, 0, 0, 0; 0, 0, 0, -1; 0, 0, 0, 0] (by decide) rfl (by simp) ?_ ?_ (by decide)
      · intro c d h1 h2
        fin_cases c <;> fin_cases d <;> first | rfl | exact absurd ⟨rfl, rfl⟩ h1 | exact absurd ⟨rfl, rfl⟩ h2
      · rintro Y ⟨y1, y2, y3, y4, y5, y6⟩ h
        change Y 2 3 = 0
        simp [*]
    · refine key 1 0 !![0, 0, 0, 0; 1, 0, 0, 0; 0, 0, 0, 0; 0, 0, -1, 0] (by decide) rfl (by simp) ?_ ?_ (by decide)
      · intro c d h1 h2
        fin_cases c <;> fin_cases d <;> first | rfl | exact absurd ⟨rfl, rfl⟩ h1 | exact absurd ⟨rfl, rfl⟩ h2
      · rintro Y ⟨y1, y2, y3, y4, y5, y6⟩ h
        change Y 3 2 = 0
        simp [*]
    · refine key 1 2 !![0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 0; 0, 0, 0, 0] (by decide) rfl (by simp) ?_ ?_ (by decide)
      · intro c d h1 h2
        fin_cases c <;> fin_cases d <;> first | rfl | exact absurd ⟨rfl, rfl⟩ h1 | exact absurd ⟨rfl, rfl⟩ h2
      · rintro Y ⟨y1, y2, y3, y4, y5, y6⟩ h
        change Y 1 2 = 0
        simp [*]
    · refine key 2 1 !![0, 0, 0, 0; 0, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 0] (by decide) rfl (by simp) ?_ ?_ (by decide)
      · intro c d h1 h2
        fin_cases c <;> fin_cases d <;> first | rfl | exact absurd ⟨rfl, rfl⟩ h1 | exact absurd ⟨rfl, rfl⟩ h2
      · rintro Y ⟨y1, y2, y3, y4, y5, y6⟩ h
        change Y 2 1 = 0
        simp [*]
    · refine key 0 3 !![0, 0, 0, 1; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0] (by decide) rfl (by simp) ?_ ?_ (by decide)
      · intro c d h1 h2
        fin_cases c <;> fin_cases d <;> first | rfl | exact absurd ⟨rfl, rfl⟩ h1 | exact absurd ⟨rfl, rfl⟩ h2
      · rintro Y ⟨y1, y2, y3, y4, y5, y6⟩ h
        change Y 0 3 = 0
        simp [*]
    · refine key 3 0 !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 1, 0, 0, 0] (by decide) rfl (by simp) ?_ ?_ (by decide)
      · intro c d h1 h2
        fin_cases c <;> fin_cases d <;> first | rfl | exact absurd ⟨rfl, rfl⟩ h1 | exact absurd ⟨rfl, rfl⟩ h2
      · rintro Y ⟨y1, y2, y3, y4, y5, y6⟩ h
        change Y 3 0 = 0
        simp [*]
    · refine key 0 2 !![0, 0, 1, 0; 0, 0, 0, 1; 0, 0, 0, 0; 0, 0, 0, 0] (by decide) rfl (by simp) ?_ ?_ (by decide)
      · intro c d h1 h2
        fin_cases c <;> fin_cases d <;> first | rfl | exact absurd ⟨rfl, rfl⟩ h1 | exact absurd ⟨rfl, rfl⟩ h2
      · rintro Y ⟨y1, y2, y3, y4, y5, y6⟩ h
        change Y 1 3 = 0
        simp [*]
    · refine key 2 0 !![0, 0, 0, 0; 0, 0, 0, 0; 1, 0, 0, 0; 0, 1, 0, 0] (by decide) rfl (by simp) ?_ ?_ (by decide)
      · intro c d h1 h2
        fin_cases c <;> fin_cases d <;> first | rfl | exact absurd ⟨rfl, rfl⟩ h1 | exact absurd ⟨rfl, rfl⟩ h2
      · rintro Y ⟨y1, y2, y3, y4, y5, y6⟩ h
        change Y 3 1 = 0
        simp [*]
    · exact absurd rfl h0
  · rw [Submodule.finrank_eq_zero, eq_bot_iff]
    intro Y hY
    obtain ⟨-, y2⟩ := (spDim_mem O k _ Y).1 hY
    ext c d
    exact y2 c d fun n => hw (n ▸ wt_mem c d)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcSpKer
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Module UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.X

private theorem not_dvd_index_ker {H k ι : Type} [Group H] [Field k] [Finite k] [Fintype ι] {l : ℕ} [hl : Fact l.Prime]
    (h0 : (l : k) = 0) (φ : H →* (ι → kˣ)) : ¬ l ∣ φ.ker.index := by
  classical
  haveI := Fintype.ofFinite k
  intro hd
  rw [Subgroup.index_ker] at hd
  have h1 : Nat.card φ.range ∣ Nat.card (ι → kˣ) := Subgroup.card_subgroup_dvd_card _
  have h2 : Nat.card (ι → kˣ) = (Fintype.card k - 1) ^ Fintype.card ι := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_units]
  have hc : ringChar k = l := by
    rcases (Nat.dvd_prime hl.out).1 (ringChar.dvd h0) with h | h
    · exact absurd h CharP.ringChar_ne_one
    · exact h
  haveI : CharP k l := by
    rw [← hc]
    exact ringChar.charP k
  obtain ⟨n, -, hn⟩ := FiniteField.card k l
  have hq : l ∣ Fintype.card k := by
    rw [hn]
    exact dvd_pow_self _ (PNat.ne_zero n)
  have hpos : 0 < Fintype.card k := Fintype.card_pos
  have h3 : l ∣ Fintype.card k - 1 := hl.out.dvd_of_dvd_pow (h2 ▸ dvd_trans hd h1)
  have h6 : Fintype.card k - 1 + 1 = Fintype.card k := by omega
  rw [← h6] at hq
  have h4 : l ∣ 1 := (Nat.dvd_add_right h3).1 hq
  exact hl.out.one_lt.ne' (Nat.dvd_one.1 h4)

theorem UpperTheory.V.X.spKer :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.rbar.ker.Normal ∧ ¬ l ∣ D.rbar.ker.index ∧ ∀ (j : ℤ × ℤ), ∀ g ∈ D.rbar.ker, Raw.bar (D.al ^ j.1 * D.Psi ^ j.2) g = 1 := by
  intro Ω _ _ _ l _ c D
  classical
  haveI := c.dvr
  haveI := c.fin
  obtain ⟨-, hfin, hl, -⟩ := abelian₂.dvr_finite l c.O
  have key : ∀ g, D.rbar g = 1 ↔ ∀ i, residue c.O ↑(D.ps i g) = 1 := by
    intro g
    have e : D.rbar g = Matrix.diagonal fun i => residue c.O ↑(D.ps i g) := by
      ext i j
      by_cases h : i = j
      · subst h
        simp [Raw.rbar, Raw.r0, mapRep, diagRep]
      · simp [Raw.rbar, Raw.r0, mapRep, diagRep, Matrix.diagonal_apply, h]
    rw [e, ← Matrix.diagonal_one, Matrix.diagonal_eq_diagonal_iff]
  let φ : G ℚ Ω →* (Fin 4 → (ResidueField c.O)ˣ) :=
    Pi.monoidHom fun i => (Units.map (residue c.O : c.O →* ResidueField c.O)).comp (D.ps i)
  have hφ : ∀ g, φ g = 1 ↔ ∀ i, residue c.O ↑(D.ps i g) = 1 := by
    intro g
    rw [funext_iff]
    refine forall_congr' fun i => ?_
    rw [Pi.one_apply, Units.ext_iff]
    exact Iff.rfl
  have hker : D.rbar.ker = φ.ker := by
    ext g
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, key, hφ]
  have h0 : ((l : ℕ) : ResidueField c.O) = 0 := by
    have h := (IsLocalRing.residue_eq_zero_iff _).2 hl
    simpa using h
  refine ⟨by rw [hker]; infer_instance, by rw [hker]; exact not_dvd_index_ker h0 φ, ?_⟩
  intro j g hg
  have hk := (key g).1 hg
  have a1 : Units.map (residue c.O : c.O →* ResidueField c.O) (D.Psi g) = 1 := by
    ext
    simpa [Raw.ps] using hk 1
  have a2 : Units.map (residue c.O : c.O →* ResidueField c.O) (D.al g) = 1 := by
    ext
    simpa [Raw.ps] using hk 2
  have hu : Units.map (residue c.O : c.O →* ResidueField c.O) ((D.al ^ j.1 * D.Psi ^ j.2) g) = 1 := by
    simp only [MonoidHom.mul_apply, MonoidHom.zpow_apply, map_mul, map_zpow, a1, a2, one_zpow, mul_one]
  exact congrArg Units.val hu
end

