import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeierstrassUniformization.PairIsLat
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.WpOnto
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.Bundle0001

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.MulCore
section
noncomputable section

namespace PI.GalTorsConj.W

open PI.GalTorsConj Formalism.L2.Th1.F

section core

variable {L L' : PeriodPair} {M₁ : IntermediateField ℚ ℂ} {ρ₁ : M₁ →ₐ[ℚ] ℂ}

theorem conj_velu_isogeny (hg2 : L.g₂ ∈ M₁) (hg2' : L'.g₂ = ρ₁ ⟨_, hg2⟩) {S : Finset ℂ} {f : ℂ → ℂ}
    (hf : ∀ P ∈ S, St L L' M₁ ρ₁ P (f P)) (hinj : Set.InjOn f S)
    (hSL : ∀ P ∈ S, P ∉ L.lattice) {z z' : ℂ} (hz : St L L' M₁ ρ₁ z z')
    (hU : z ∈ veluU L S) :
    Cj1 M₁ ρ₁ (veluF L S z) (veluF L' (S.image f) z') ∧
      Cj1 M₁ ρ₁ (veluD L S z) (veluD L' (S.image f) z') := by
  have hzP : ∀ P ∈ S, St L L' M₁ ρ₁ (z + P) (z' + f P) := fun P hP =>
    st_add addLaw dblLaw hg2 hg2' hz (hf P hP)
  have e0 := conj_weierstrassP hz hU.1
  have eP : ∀ P ∈ S, Cj1 M₁ ρ₁ (L.weierstrassP (z + P)) (L'.weierstrassP (z' + f P)) ∧
      Cj1 M₁ ρ₁ (L.derivWeierstrassP (z + P)) (L'.derivWeierstrassP (z' + f P)) :=
    fun P hP => conj_weierstrassP (hzP P hP) (hU.2 P hP)
  have eQ : ∀ P ∈ S, Cj1 M₁ ρ₁ (L.weierstrassP P) (L'.weierstrassP (f P)) :=
    fun P hP => (conj_weierstrassP (hf P hP) (hSL P hP)).1
  unfold veluF veluD
  rw [Finset.sum_image hinj, Finset.sum_image hinj]
  exact ⟨conj_add_alt e0.1 (conj_sum_alt S _ _ fun P hP => conj_sub_alt (eP P hP).1 (eQ P hP)),
    conj_add_alt e0.2 (conj_sum_alt S _ _ fun P hP => (eP P hP).2)⟩

theorem core (hD : IsogD) (hO : IsogODE) (hDn : TorsDense)
    (hg2 : L.g₂ ∈ M₁) (hg3 : L.g₃ ∈ M₁) (hg2' : L'.g₂ = ρ₁ ⟨_, hg2⟩) (hg3' : L'.g₃ = ρ₁ ⟨_, hg3⟩)
    (htors : ∀ (n : ℕ) (t : ℂ), 0 < n → (n : ℂ) * t ∈ L.lattice → t ∉ L.lattice →
      L.weierstrassP t ∈ M₁ ∧ L.derivWeierstrassP t ∈ M₁)
    {c : ℂ} (hc0 : c ≠ 0) (hcL : MulStable L c) (hc : c ∈ M₁) (hρc : ρ₁ ⟨c, hc⟩ = c)
    {t t' : ℂ} (h : St L L' M₁ ρ₁ t t') : St L L' M₁ ρ₁ (c * t) (c * t') := by
  obtain ⟨S, hS⟩ := kerRepsExist L c hc0 hcL
  have hSL : ∀ P ∈ S, P ∉ L.lattice := fun P hP => (hS.1 P hP).2
  have hex : ∀ P ∈ S, ∃ P', St L L' M₁ ρ₁ P P' := by
    intro P hP
    obtain ⟨m, hm, hmP⟩ := tors_of_ker hc0 hcL (hS.1 P hP).1
    exact st_exists pOnto hg2 hg3 hg2' hg3' P (Or.inr (htors m P hm hmP (hSL P hP)))
  choose! f hf using hex
  have hinj : Set.InjOn f S := by
    intro P hP Q hQ e
    have h2 : St L L' M₁ ρ₁ Q (f P) := by rw [e]; exact hf Q hQ
    exact hS.2.1 P hP Q hQ (st_inj (hf P hP) h2)
  have hS'L : ∀ P' ∈ S.image f, P' ∉ L'.lattice := by
    intro P' hP'
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hP'
    exact fun h' => hSL P hP ((st_mem_iff (hf P hP)).2 h')
  have hS'd : ∀ P' ∈ S.image f, ∀ Q' ∈ S.image f, P' - Q' ∈ L'.lattice → P' = Q' := by
    intro P' hP' Q' hQ' hd
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hP'
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.1 hQ'
    have h2 : St L L' M₁ ρ₁ Q (f P) := by
      have := st_add_right (hf Q hQ) hd
      rwa [show f Q + (f P - f Q) = f P by ring] at this
    rw [hS.2.1 P hP Q hQ (st_inj (hf P hP) h2)]
  have cc : Cj1 M₁ ρ₁ c c := ⟨hc, hρc⟩
  have cg2 : Cj1 M₁ ρ₁ L.g₂ L'.g₂ := ⟨hg2, hg2'.symm⟩
  have cg3 : Cj1 M₁ ρ₁ L.g₃ L'.g₃ := ⟨hg3, hg3'.symm⟩

  have hodeT : ∀ z' ∈ veluU L' (S.image f) ∩
      {t : ℂ | ∃ n : ℕ, 0 < n ∧ (n : ℂ) * t ∈ L'.lattice},
      veluD L' (S.image f) z' ^ 2 = 4 * veluF L' (S.image f) z' ^ 3
        - c ^ 4 * L'.g₂ * veluF L' (S.image f) z' - c ^ 6 * L'.g₃ := by
    rintro z' ⟨hU', n, hn, hnz'⟩
    obtain ⟨z, -, hz⟩ := st_onto addLaw dblLaw pOnto hg2 hg3 hg2' hg3' n hn
      (fun t h1 h2 => htors n t hn h1 h2) z' hnz'
    have hzL : z ∉ L.lattice := fun h' => hU'.1 ((st_mem_iff hz).1 h')
    have hzP : ∀ P ∈ S, z + P ∉ L.lattice := fun P hP h' =>
      hU'.2 (f P) (Finset.mem_image_of_mem f hP)
        ((st_mem_iff (st_add addLaw dblLaw hg2 hg2' hz (hf P hP))).1 h')
    have hU : z ∈ veluU L S := ⟨hzL, hzP⟩
    have hcz := mul_notMem hS hzL hzP
    have eF : veluF L S z = c ^ 2 * L.weierstrassP (c * z) := (isogenyP L c S hc0 hcL hS z hcz).symm
    have eD : veluD L S z = c ^ 3 * L.derivWeierstrassP (c * z) := (hD L c S hc0 hcL hS z hcz).symm
    have curve := L.derivWeierstrassP_sq (c * z) hcz
    have ode : veluD L S z ^ 2 =
        4 * veluF L S z ^ 3 - c ^ 4 * L.g₂ * veluF L S z - c ^ 6 * L.g₃ := by
      rw [eF, eD]
      linear_combination c ^ 6 * curve
    obtain ⟨cF, cD⟩ := conj_velu_isogeny hg2 hg2' hf hinj hSL hz hU
    have lhs := conj_pow_alt cD 2
    have rhs := conj_sub_alt (conj_sub_alt (conj_mul_alt (conj_natCast_alt 4) (conj_pow_alt cF 3))
      (conj_mul_alt (conj_mul_alt (conj_pow_alt cc 4) cg2) cF)) (conj_mul_alt (conj_pow_alt cc 6) cg3)
    have e := conj_eq_alt lhs rhs (by rw [ode]; push_cast; ring)
    rw [e]
    push_cast
    ring

  have hode : ∀ z' ∈ veluU L' (S.image f), veluD L' (S.image f) z' ^ 2 =
      4 * veluF L' (S.image f) z' ^ 3 - c ^ 4 * L'.g₂ * veluF L' (S.image f) z' - c ^ 6 * L'.g₃ := by
    have hF := continuousOn_veluF L' (S.image f)
    have hDc := continuousOn_veluD L' (S.image f)
    have hcont1 : ContinuousOn (fun z => veluD L' (S.image f) z ^ 2) (veluU L' (S.image f)) :=
      hDc.pow 2
    have hcont2 : ContinuousOn (fun z => 4 * veluF L' (S.image f) z ^ 3
        - c ^ 4 * L'.g₂ * veluF L' (S.image f) z - c ^ 6 * L'.g₃) (veluU L' (S.image f)) :=
      ((continuousOn_const.mul (hF.pow 3)).sub (continuousOn_const.mul hF)).sub continuousOn_const
    have heq := Set.EqOn.of_subset_closure (fun z hz => hodeT z hz) hcont1 hcont2
      Set.inter_subset_left ((hDn L').open_subset_closure_inter (isOpen_veluU L' (S.image f)))
    exact fun z hz => heq hz
  obtain ⟨hcL', hcS', hU'⟩ := hO L' c (S.image f) hc0 hS'L hS'd hode
  by_cases ht : t ∈ L.lattice
  · exact Or.inl ⟨hcL t ht, hcL' t' ((st_mem_iff h).1 ht)⟩
  by_cases hct : c * t ∈ L.lattice
  · obtain ⟨Q, hQ, htQ⟩ := hS.2.2 t hct ht
    have h2 : St L L' M₁ ρ₁ t (f Q) := by
      have := st_add_left (hf Q hQ) htQ
      rwa [show Q + (t - Q) = t by ring] at this
    have d := st_unique h h2
    refine Or.inl ⟨hct, ?_⟩
    have := L'.lattice.add_mem (hcL' _ d) (hcS' (f Q) (Finset.mem_image_of_mem f hQ))
    rwa [show c * (t' - f Q) + c * f Q = c * t' by ring] at this
  have htP : ∀ P ∈ S, t + P ∉ L.lattice := by
    intro P hP h'
    apply hct
    have := L.lattice.sub_mem (hcL _ h') (hS.1 P hP).1
    rwa [show c * (t + P) - c * P = c * t by ring] at this
  have hU : t ∈ veluU L S := ⟨ht, htP⟩
  have ht' : t' ∉ L'.lattice := fun h' => ht ((st_mem_iff h).2 h')
  have hU'' : t' ∈ veluU L' (S.image f) := by
    refine ⟨ht', fun P' hP' h' => ?_⟩
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hP'
    exact htP P hP ((st_mem_iff (st_add addLaw dblLaw hg2 hg2' h (hf P hP))).2 h')
  obtain ⟨cF, cD⟩ := conj_velu_isogeny hg2 hg2' hf hinj hSL h hU
  obtain ⟨hct', eF', eD'⟩ := hU' t' hU''
  have eF : veluF L S t = c ^ 2 * L.weierstrassP (c * t) := (isogenyP L c S hc0 hcL hS t hct).symm
  have eD : veluD L S t = c ^ 3 * L.derivWeierstrassP (c * t) := (hD L c S hc0 hcL hS t hct).symm
  have cinv : Cj1 M₁ ρ₁ c⁻¹ c⁻¹ := by
    refine ⟨M₁.inv_mem hc, ?_⟩
    have e : ((⟨c, hc⟩ : M₁)⁻¹) = ⟨c⁻¹, M₁.inv_mem hc⟩ := rfl
    rw [← e, map_inv₀, hρc]
  have qX : Cj1 M₁ ρ₁ (L.weierstrassP (c * t)) (L'.weierstrassP (c * t')) := by
    have p := conj_mul_alt (conj_pow_alt cinv 2) cF
    have e1 : c⁻¹ ^ 2 * veluF L S t = L.weierstrassP (c * t) := by rw [eF]; field_simp
    have e2 : c⁻¹ ^ 2 * veluF L' (S.image f) t' = L'.weierstrassP (c * t') := by
      rw [← eF']; field_simp
    rwa [e1, e2] at p
  have qY : Cj1 M₁ ρ₁ (L.derivWeierstrassP (c * t)) (L'.derivWeierstrassP (c * t')) := by
    have p := conj_mul_alt (conj_pow_alt cinv 3) cD
    have e1 : c⁻¹ ^ 3 * veluD L S t = L.derivWeierstrassP (c * t) := by rw [eD]; field_simp
    have e2 : c⁻¹ ^ 3 * veluD L' (S.image f) t' = L'.derivWeierstrassP (c * t') := by
      rw [← eD']; field_simp
    rwa [e1, e2] at p
  obtain ⟨hx, vx⟩ := qX
  obtain ⟨hy, vy⟩ := qY
  exact Or.inr ⟨hct, hct', hx, hy, vx.symm, vy.symm⟩

end core

end PI.GalTorsConj.W

end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.TorsValsFinite
section
noncomputable section

namespace PI.GalTorsConj.W

open Polynomial Formalism.L2.Th1.F

theorem mulStable_nat (L : PeriodPair) (n : ℕ) : MulStable L (n : ℂ) := by
  intro ω hω
  rw [← nsmul_eq_mul]
  exact nsmul_mem hω n

theorem tors_vals_finite (L : PeriodPair) (n : ℕ) (hn : 0 < n) :
    {v : ℂ | ∃ s, (n : ℂ) * s ∈ L.lattice ∧ s ∉ L.lattice ∧ L.weierstrassP s = v}.Finite := by
  have hα : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  obtain ⟨S, hS⟩ := kerRepsExist L (n : ℂ) hα (mulStable_nat L n)
  refine (S.finite_toSet.image L.weierstrassP).subset ?_
  rintro v ⟨s, h1, h2, rfl⟩
  obtain ⟨P, hP, hsP⟩ := hS.2.2 s h1 h2
  refine ⟨P, hP, ?_⟩
  have e : s = P + (s - P) := by ring
  rw [e, wp_add_mem L P hsP]

theorem shift_emb (M : IntermediateField ℚ ℂ) (x : ℂ) (hx : Transcendental M x) (k : ℕ) :
    ∃ σ : IntermediateField.adjoin M {x} →ₐ[M] ℂ,
      σ (IntermediateField.AdjoinSimple.gen M x) = x + k := by
  have hk : Transcendental M (x + k) := by
    intro halg
    apply hx
    have h2 : IsIntegral M (k : ℂ) := by
      simpa using (isIntegral_algebraMap (R := M) (A := ℂ) (x := (k : M)))
    simpa using (halg.isIntegral.sub h2).isAlgebraic
  have hφ : nonZeroDivisors M[X] ≤ (nonZeroDivisors ℂ).comap (aeval (x + k) : M[X] →ₐ[M] ℂ) := by
    intro p hp
    simp only [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero] at hp ⊢
    intro h0
    exact hk ⟨p, hp, h0⟩
  refine ⟨(RatFunc.liftAlgHom (aeval (x + k) : M[X] →ₐ[M] ℂ) hφ).comp
    (RatFunc.algEquivOfTranscendental x hx).symm.toAlgHom, ?_⟩
  rw [AlgHom.comp_apply]
  change RatFunc.liftAlgHom _ hφ ((RatFunc.algEquivOfTranscendental x hx).symm _) = _
  rw [RatFunc.algEquivOfTranscendental_symm_gen]
  have := RatFunc.liftAlgHom_apply_div (aeval (x + k) : M[X] →ₐ[M] ℂ) hφ X 1
  simpa using this

def rsHom (M : IntermediateField ℚ ℂ) (E : IntermediateField M ℂ) (σ : E →ₐ[M] ℂ) :
    E.restrictScalars ℚ →ₐ[ℚ] ℂ :=
  RingHom.toRatAlgHom
    { toFun := fun z => σ ⟨z, z.2⟩
      map_one' := σ.map_one
      map_mul' := fun a b => σ.map_mul ⟨a, a.2⟩ ⟨b, b.2⟩
      map_zero' := σ.map_zero
      map_add' := fun a b => σ.map_add ⟨a, a.2⟩ ⟨b, b.2⟩ }

theorem alg_of_sq {F : Type*} [Field F] [Algebra F ℂ] {x y a b : ℂ}
    (hsq : y ^ 2 = 4 * x ^ 3 - a * x - b)
    (hx : IsAlgebraic F x) (ha : IsAlgebraic F a) (hb : IsAlgebraic F b) : IsAlgebraic F y := by
  have hx' := mem_algebraicClosure_iff.mpr hx
  have ha' := mem_algebraicClosure_iff.mpr ha
  have hb' := mem_algebraicClosure_iff.mpr hb
  have h4 : (4 : ℂ) ∈ algebraicClosure F ℂ := by
    have := natCast_mem (algebraicClosure F ℂ) 4
    exact_mod_cast this
  have hw : 4 * x ^ 3 - a * x - b ∈ algebraicClosure F ℂ :=
    sub_mem (sub_mem (mul_mem h4 (pow_mem hx' 3)) (mul_mem ha' hx')) hb'
  rw [← hsq] at hw
  exact IsAlgebraic.of_pow two_pos (mem_algebraicClosure_iff.mp hw)

theorem wp_isAlgebraic (L : PeriodPair) (M : IntermediateField ℚ ℂ) (hg2 : L.g₂ ∈ M)
    (hg3 : L.g₃ ∈ M) (n : ℕ) (t : ℂ) (hn : 0 < n) (hnt : (n : ℂ) * t ∈ L.lattice)
    (ht : t ∉ L.lattice) : IsAlgebraic M (L.weierstrassP t) := by
  by_contra htr
  apply (tors_vals_finite L n hn).not_infinite
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => L.weierstrassP t + k) ?_ ?_
  · intro a b hab
    simp only at hab
    exact_mod_cast add_left_cancel hab
  intro k
  obtain ⟨σ, hσ⟩ := shift_emb M (L.weierstrassP t) htr k
  let Mx : IntermediateField ℚ ℂ := (IntermediateField.adjoin M {L.weierstrassP t}).restrictScalars ℚ
  have hMx : ∀ z ∈ M, z ∈ Mx := fun z hz =>
    (IntermediateField.adjoin M {L.weierstrassP t}).algebraMap_mem ⟨z, hz⟩
  have hxMx : L.weierstrassP t ∈ Mx := IntermediateField.mem_adjoin_simple_self M _
  let M₂ : IntermediateField ℚ ℂ := (algebraicClosure Mx ℂ).restrictScalars ℚ
  have hle : Mx ≤ M₂ := fun z hz => by
    show z ∈ algebraicClosure Mx ℂ
    exact mem_algebraicClosure_iff.mpr (isAlgebraic_algebraMap (⟨z, hz⟩ : Mx))
  have halg₂ : ∀ z ∈ M₂, IsAlgebraic Mx z := fun z hz => mem_algebraicClosure_iff.mp hz
  obtain ⟨ρ₂, hρ₂⟩ := extRho Mx M₂ hle halg₂ (rsHom M _ σ)
  have hg2₂ : L.g₂ ∈ M₂ := hle (hMx _ hg2)
  have hg3₂ : L.g₃ ∈ M₂ := hle (hMx _ hg3)
  have hx₂ : L.weierstrassP t ∈ M₂ := hle hxMx
  have hy₂ : L.derivWeierstrassP t ∈ M₂ := by
    have hsq : L.derivWeierstrassP t ^ 2
        = 4 * L.weierstrassP t ^ 3 - L.g₂ * L.weierstrassP t - L.g₃ := by
      have e := L.derivWeierstrassP_sq t ht
      linear_combination e
    show L.derivWeierstrassP t ∈ algebraicClosure Mx ℂ
    exact mem_algebraicClosure_iff.mpr (alg_of_sq hsq
      (isAlgebraic_algebraMap (⟨_, hxMx⟩ : Mx))
      (isAlgebraic_algebraMap (⟨_, hMx _ hg2⟩ : Mx))
      (isAlgebraic_algebraMap (⟨_, hMx _ hg3⟩ : Mx)))
  have hfix : ∀ z (hz : z ∈ M) (hz₂ : z ∈ M₂), ρ₂ ⟨z, hz₂⟩ = z := by
    intro z hz hz₂
    have e1 : (⟨z, hz₂⟩ : M₂) = IntermediateField.inclusion hle ⟨z, hMx z hz⟩ := rfl
    rw [e1, hρ₂]
    exact σ.commutes ⟨z, hz⟩
  have hρx : ρ₂ ⟨_, hx₂⟩ = L.weierstrassP t + k := by
    have e1 : (⟨_, hx₂⟩ : M₂) = IntermediateField.inclusion hle ⟨_, hxMx⟩ := rfl
    rw [e1, hρ₂]
    exact hσ
  have hg2' : L.g₂ = ρ₂ ⟨_, hg2₂⟩ := (hfix _ hg2 hg2₂).symm
  have hg3' : L.g₃ = ρ₂ ⟨_, hg3₂⟩ := (hfix _ hg3 hg3₂).symm
  obtain ⟨t₂, hst⟩ := st_exists (L := L) (L' := L) (M := M₂) (ρ := ρ₂) pOnto hg2₂ hg3₂ hg2' hg3' t
    (Or.inr ⟨hx₂, hy₂⟩)
  have hn₂ := (st_mem_iff (st_nsmul addLaw dblLaw hg2₂ hg2' hst n)).mp hnt
  rcases hst with ⟨h1, -⟩ | ⟨-, h2, hx', hy', e1, -⟩
  · exact absurd h1 ht
  · refine ⟨t₂, hn₂, h2, ?_⟩
    rw [e1]
    exact hρx

end PI.GalTorsConj.W

end
end

