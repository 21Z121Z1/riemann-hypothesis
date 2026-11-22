import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.Bundle0001
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.JacquetShalikaBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0641
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0954
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.Bundle0003
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0008
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0259

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.Unlfrob
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.GalN UpperTheory.GalN.V
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private lemma root_inv {K L : Type*} [Field K] [Field L] (e : K ≃+* L) {n : ℕ} (g : GL (Fin n) K) (y : L)
    (h : ((g : Matrix (Fin n) (Fin n) K).charpoly.map e.toRingHom).IsRoot y) :
    y ≠ 0 ∧ (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).charpoly.map e.toRingHom).IsRoot y⁻¹ := by
  obtain ⟨x, rfl⟩ := e.surjective y
  have hx : (g : Matrix (Fin n) (Fin n) K).charpoly.IsRoot x :=
    (Polynomial.isRoot_map_iff (f := e.toRingHom) e.injective).1 h
  have hs : x ∈ spectrum K (g : Matrix (Fin n) (Fin n) K) :=
    Matrix.mem_spectrum_iff_isRoot_charpoly.2 hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact spectrum.zero_notMem K (Units.isUnit g) hs
  have hi : x⁻¹ ∈ spectrum K ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    simpa using (spectrum.inv_mem_iff (r := Units.mk0 x hx0) (a := g)).1 (by simpa using hs)
  refine ⟨by simpa using hx0, ?_⟩
  have := (Polynomial.isRoot_map_iff (f := e.toRingHom) (x := x⁻¹) e.injective).2
    (Matrix.mem_spectrum_iff_isRoot_charpoly.1 hi)
  simpa using this

theorem UpperTheory.GalN.V.L.unlfrob :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)) (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (S : Multiset ℂ), IsPlaceOver A w → FrobEig ι r w S → (∀ α ∈ S, ∀ β ∈ S, ‖α‖ < ((normV w : ℕ) : ℝ) * ‖β‖) → UnlAt ι r w A := by
  intro F Ω _ _ _ _ _ l _ ι n r w A S hA hS hlt
  obtain ⟨s, hs⟩ := exists_isFrob hA
  refine ⟨s, 1, le_rfl, by simpa using hs, ?_⟩
  intro α hα hqα
  have hP := (hS A hA).2 s hs
  have key : ∀ y : ℂ, ((r s : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.map ι.toRingHom).IsRoot y →
      y ≠ 0 ∧ y⁻¹ ∈ S := by
    intro y hy
    obtain ⟨hy0, hr⟩ := root_inv ι (r s) y hy
    refine ⟨hy0, ?_⟩
    have hroots : (((r s⁻¹ : Matrix (Fin n) (Fin n) (Qbar l))).charpoly.map ι.toRingHom).roots = S := by
      rw [hP]; exact Polynomial.roots_multiset_prod_X_sub_C S
    rw [← hroots, Polynomial.mem_roots ((Matrix.charpoly_monic _).map _).ne_zero, map_inv]
    exact hr
  obtain ⟨ha0, ha⟩ := key α hα
  obtain ⟨hb0, hb⟩ := key _ hqα
  have hq0 : (((normV w : ℕ) : ℂ)) ≠ 0 := by
    intro h0
    apply hb0
    simp [h0]
  have hlt' := hlt _ ha _ hb
  have hqr : (0 : ℝ) < ((normV w : ℕ) : ℝ) := by
    have : (normV w : ℕ) ≠ 0 := by exact_mod_cast hq0
    exact_mod_cast Nat.pos_of_ne_zero this
  have heq : ((normV w : ℕ) : ℝ) * ‖((((normV w : ℕ) : ℂ) ^ 1 * α))⁻¹‖ = ‖α⁻¹‖ := by
    rw [pow_one, norm_inv, norm_mul, norm_inv, Complex.norm_natCast, mul_inv]
    field_simp
  exact absurd hlt' (by rw [heq]; exact lt_irrefl _)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.Unliso
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.GalN UpperTheory.GalN.V
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem isRoot_map_equiv {k : Type} [Field k] (ι : k ≃+* ℂ) (p : Polynomial k) (x : k) :
    (p.map ι.toRingHom).IsRoot (ι x) ↔ p.IsRoot x := by
  have h : (p.map ι.toRingHom).eval (ι x) = ι (p.eval x) := by
    rw [Polynomial.eval_map]
    exact Polynomial.eval₂_at_apply ι.toRingHom x
  rw [Polynomial.IsRoot.def, Polynomial.IsRoot.def, h]
  exact map_eq_zero_iff ι ι.injective

private theorem isRoot_charpoly_smul {k : Type} [Field k] {n : ℕ} (c : k) (hc : c ≠ 0)
    (M : Matrix (Fin n) (Fin n) k) (x : k) :
    (c • M).charpoly.IsRoot (c * x) ↔ M.charpoly.IsRoot x := by
  have h : Matrix.scalar (Fin n) (c * x) - c • M = c • (Matrix.scalar (Fin n) x - M) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.scalar_apply, Matrix.diagonal_apply, hij, mul_sub]
  rw [Polynomial.IsRoot.def, Polynomial.IsRoot.def, Matrix.eval_charpoly, Matrix.eval_charpoly, h,
    Matrix.det_smul]
  simp [hc]

private theorem charpoly_gl_conj {k : Type} [Field k] {n : ℕ} (g a : GL (Fin n) k) :
    ((g * a * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).charpoly =
      (a : Matrix (Fin n) (Fin n) k).charpoly := by
  rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]

private theorem ratio_smul {k : Type} [Field k] {n : ℕ} (ι : k ≃+* ℂ) (c : k) (hc0 : c ≠ 0)
    (M : Matrix (Fin n) (Fin n) k) (q : ℂ)
    (h : ∀ α : ℂ, (M.charpoly.map ι.toRingHom).IsRoot α →
      ¬ (M.charpoly.map ι.toRingHom).IsRoot (q * α)) :
    ∀ α : ℂ, ((c • M).charpoly.map ι.toRingHom).IsRoot α →
      ¬ ((c • M).charpoly.map ι.toRingHom).IsRoot (q * α) := by
  have key : ∀ y : ℂ, ((c • M).charpoly.map ι.toRingHom).IsRoot (ι c * y) ↔
      (M.charpoly.map ι.toRingHom).IsRoot y := by
    intro y
    obtain ⟨x, rfl⟩ := ι.surjective y
    rw [← map_mul, isRoot_map_equiv, isRoot_map_equiv, isRoot_charpoly_smul c hc0]
  intro α hα hβ
  have hιc : ι c ≠ 0 := (map_ne_zero_iff ι ι.injective).2 hc0
  have hα' : ι c * ((ι c)⁻¹ * α) = α := by field_simp
  have h1 : (M.charpoly.map ι.toRingHom).IsRoot ((ι c)⁻¹ * α) := by
    rw [← key, hα']
    exact hα
  refine h _ h1 ?_
  rw [← key]
  have h2 : ι c * (q * ((ι c)⁻¹ * α)) = q * α := by
    field_simp
  rw [h2]
  exact hβ

theorem UpperTheory.GalN.V.L.unliso :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)) (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (r' : G F Ω →* GL (Fin n) (Qbar l)) (μ : G F Ω →* (Qbar l)ˣ), UnlAt ι r w A → (RepIso r r' → UnlAt ι r' w A) ∧ UnlAt ι (UpperTheory.V.Af.tw r μ) w A := by
  intro F Ω _ _ _ _ _ l _ ι n r w A r' μ hU
  obtain ⟨s, j, hj, hF, h⟩ := hU
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨s, j, hj, hF, ?_⟩
    rw [hg s, charpoly_gl_conj]
    exact h
  · refine ⟨s, j, hj, hF, ?_⟩
    rw [UpperTheory.V.Af.tw_val]
    exact ratio_smul ι _ (Units.ne_zero _) _ _ h
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.Unlres
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.GalN UpperTheory.GalN.V
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.GalN.V.L.unlres :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)) (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] (v : HeightOneSpectrum (𝓞 K)), IsPlaceOver A w → IsPlaceOver A v → UnlAt ι (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)) v A → UnlAt ι r w A := by
  intro F Ω _ _ _ _ _ l _ ι n r w A K _ _ _ _ _ v hw hv h
  obtain ⟨s, j, hj, ⟨hdec, hres⟩, hroot⟩ := h
  have hu : v.under (𝓞 F) = w := by
    have h1 : IsPlaceOver A (v.under (𝓞 F)) := GlobalTheory.AboveL.SatBC.isPlaceOver_under hv
    refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
    exact (h1 x).symm.trans (hw x)
  have hN : normV v = normV w ^ v.asIdeal.inertiaDeg (𝓞 F) := by
    have := GlobalTheory.AboveL.SatBC.normV_under_pow F K v
    rwa [hu] at this
  have hf : 1 ≤ v.asIdeal.inertiaDeg (𝓞 F) := by
    rcases Nat.eq_zero_or_pos (v.asIdeal.inertiaDeg (𝓞 F)) with h0 | h0
    · exfalso
      rw [h0, pow_zero] at hN
      have hne : v.asIdeal ≠ ⊤ := v.isPrime.ne_top
      exact hne (Ideal.absNorm_eq_one_iff.1 hN)
    · exact h0
  set f := v.asIdeal.inertiaDeg (𝓞 F) with hfdef
  have hpow : normV v ^ j = normV w ^ (f * j) := by rw [hN, pow_mul]
  refine ⟨s.restrictScalars F, f * j, Nat.mul_pos hf hj, ⟨?_, ?_⟩, ?_⟩
  · exact hdec
  · intro x hx
    have := hres x hx
    rw [hpow] at this
    exact this
  · intro α hα hα'
    have e : ((normV v : ℕ) : ℂ) ^ j = ((normV w : ℕ) : ℂ) ^ (f * j) := by exact_mod_cast hpow
    refine hroot α hα ?_
    rw [e]
    exact hα'
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.Unlwd
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.GalN UpperTheory.GalN.V
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.GalN.V.L.unlwd :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)) (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (hl : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal), Continuous r → UnlAt ι r w A → ∃ g : ↥(Weil h), NoRatio (wdOf h hl ι r) g := by
  intro F Ω _ _ _ _ _ l _ ι n r w A h hl hr hu
  obtain ⟨s, j, _, hs, hno⟩ := hu
  have ha : ActsAs A (normV w) s j 0 := by
    have h1 := actsAs_one_iff.mpr hs
    refine ⟨h1.1, fun x hx => ?_⟩
    simpa using h1.2 x hx
  have hc : Continuous fun g => (r g : Matrix (Fin n) (Fin n) (Qbar l)) :=
    Units.continuous_val.comp hr
  have hd : deg (⟨s, j, 0, ha⟩ : Weil h) = j := by
    simpa using deg_eq (σ := (⟨s, j, 0, ha⟩ : Weil h)) ha
  refine ⟨⟨s, j, 0, ha⟩, ?_⟩
  intro α hα hβ
  rw [WD.eig, charPol_wdOf hl ι hc] at hα hβ
  rw [hd, zpow_natCast] at hβ
  exact hno α (isRoot_of_mem_roots hα) (isRoot_of_mem_roots hβ)
end

