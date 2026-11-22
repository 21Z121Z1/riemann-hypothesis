import Formalism.LocalToGlobal.GlobalTheory.GL6.Statement
import Formalism.HarderNarasimhan.ShiftInvariance

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL6.AdelicFunctionRightTranslateDiamond
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}

theorem is_diamond_one (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F))
    (hv : (T : 𝓞 F) ∈ v.asIdeal) : IsDia S v hv 1 1 := by
  refine ⟨fun v' _ => ?_, ?_, ?_⟩
  · simp
  · simp only [OneMemClass.coe_one, map_one]; exact (levelVL σ J v S.Lb).one_mem
  · refine ⟨by simp only [OneMemClass.coe_one, map_one]; exact (stabGL _).one_mem, fun x => ?_⟩
    rw [one_smul]
    congr 1
    apply Subtype.ext
    simp

theorem is_diamond_mul (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F))
    (hv : (T : 𝓞 F) ∈ v.asIdeal) {k k' : ℤ} {δ δ' : UPts σ J (FiniteAdeleRing (𝓞 F) F)}
    (h : IsDia S v hv k δ) (h' : IsDia S v hv k' δ') : IsDia S v hv (k * k') (δ * δ') := by
  obtain ⟨h1, h2, hg, h3⟩ := h
  obtain ⟨h1', h2', hg', h3'⟩ := h'
  refine ⟨fun v' hv' => ?_, ?_, ?_⟩
  · simp [Subgroup.coe_mul, map_mul, h1 v' hv', h1' v' hv']
  · simpa [Subgroup.coe_mul, map_mul] using (levelVL σ J v S.Lb).mul_mem h2 h2'
  · have hgg : bc (prV (E := E) v) (δ * δ').1 ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v)
        (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb))) := by
      simpa [Subgroup.coe_mul, map_mul] using (stabGL _).mul_mem hg hg'
    refine ⟨hgg, fun x => ?_⟩
    have e : (⟨(bc (prV (E := E) v) (δ * δ').1).1 *ᵥ x.1, (hgg x.1).1 x.2⟩ :
        latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb))) =
        ⟨(bc (prV (E := E) v) δ.1).1 *ᵥ ((bc (prV (E := E) v) δ'.1).1 *ᵥ x.1),
          (hg _).1 ((hg' x.1).1 x.2)⟩ := by
      apply Subtype.ext
      simp [Subgroup.coe_mul, map_mul, Matrix.mulVec_mulVec]
    rw [e, mul_comm, mul_smul, h3 ⟨_, (hg' x.1).1 x.2⟩, h3' x]

theorem diamond_conj_mem_level (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F))
    (hv : (T : 𝓞 F) ∈ v.asIdeal) {k : ℤ} {δ : UPts σ J (FiniteAdeleRing (𝓞 F) F)}
    (h : IsDia S v hv k δ) (κ : S.U) : δ.1⁻¹ * κ.1 * δ.1 ∈ S.U := by
  obtain ⟨h1, h2, hg, h3⟩ := h
  have hκ := (S.U_eq κ.1).1 κ.2
  rw [S.U_eq]
  refine ⟨(UPts σ J _).mul_mem ((UPts σ J _).mul_mem ((UPts σ J _).inv_mem δ.2) hκ.1) δ.2, fun v' => ?_⟩
  by_cases hv' : v' = v
  · subst hv'
    have hk := hκ.2 v'
    rw [S.UlocAlt v' hv] at hk ⊢
    obtain ⟨hkL, hkF, hkf⟩ := hk
    simp only [map_mul, map_inv]
    refine ⟨(levelVL σ J v' S.Lb).mul_mem ((levelVL σ J v' S.Lb).mul_mem
      ((levelVL σ J v' S.Lb).inv_mem h2) hkL) h2, ?_⟩
    have hgg : (bc (prV (E := E) v') δ.1)⁻¹ * bc (prV (E := E) v') κ.1 * bc (prV (E := E) v') δ.1 ∈
        stabGL (latS (F := F) (v'.adicCompletion F) (intV E v')
          (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb))) :=
      (stabGL _).mul_mem ((stabGL _).mul_mem ((stabGL _).inv_mem hg) hkF) hg
    refine ⟨hgg, fun x => ?_⟩
    set y : latS (F := F) (v'.adicCompletion F) (intV E v')
        (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)) :=
      ⟨((bc (prV (E := E) v') δ.1)⁻¹ * bc (prV (E := E) v') κ.1 * bc (prV (E := E) v') δ.1).1 *ᵥ x.1,
        (hgg x.1).1 x.2⟩ with hy
    have e1 : (⟨(bc (prV (E := E) v') δ.1).1 *ᵥ y.1, (hg y.1).1 y.2⟩ :
        latS (F := F) (v'.adicCompletion F) (intV E v') (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb))) =
        ⟨(bc (prV (E := E) v') κ.1).1 *ᵥ ((bc (prV (E := E) v') δ.1).1 *ᵥ x.1),
          (hkF _).1 ((hg x.1).1 x.2)⟩ := by
      apply Subtype.ext
      simp only [hy, Matrix.mulVec_mulVec, Units.val_mul, ← Matrix.mul_assoc]
      rw [Units.mul_inv, Matrix.one_mul]
    have A := h3 y
    rw [e1, hkf ⟨_, (hg x.1).1 x.2⟩, h3 x] at A
    exact A.symm
  · have hk := hκ.2 v'
    simpa [map_mul, map_inv, h1 v' hv'] using hk

theorem level_character_conj_diamond (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F))
    (hv : (T : 𝓞 F) ∈ v.asIdeal) (hb : v ∉ bad) {k : ℤ} {δ : UPts σ J (FiniteAdeleRing (𝓞 F) F)}
    (h : IsDia S v hv k δ) (κ : S.U) :
    S.chi ⟨δ.1⁻¹ * κ.1 * δ.1, diamond_conj_mem_level S v hv h κ⟩ = S.chi κ := by
  have h1 := h.1
  have key : S.chi (κ⁻¹ * ⟨δ.1⁻¹ * κ.1 * δ.1, diamond_conj_mem_level S v hv h κ⟩) = 1 := by
    apply S.chi_triv
    intro v'' hv''
    have hne : v'' ≠ v := fun e => hb (e ▸ hv'')
    simp [Subgroup.coe_mul, map_mul, map_inv, h1 v'' hne]
  rw [map_mul, map_inv, inv_mul_eq_one] at key
  exact key.symm

theorem adelic_function_right_translate_diamond {ι : Type} [Fintype ι] (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal) (hb : v ∉ bad) {k : ℤ}
    {δ : UPts σ J (FiniteAdeleRing (𝓞 F) F)} (h : IsDia S v hv k δ)
    {g : UPts σ J (FiniteAdeleRing (𝓞 F) F) → Frames (gramC J emb) → ℂ} (hg : g ∈ AdFun S emb) :
    (fun x => g (x * δ)) ∈ AdFun S emb := by
  intro γ hγ x x' κ hx y y' hy
  have e : (x' * δ).1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (x * δ).1 *
      (⟨δ.1⁻¹ * κ.1 * δ.1, diamond_conj_mem_level S v hv h κ⟩ : S.U).1 := by
    simp only [Subgroup.coe_mul, hx]
    group
  have := hg γ hγ (x * δ) (x' * δ) ⟨δ.1⁻¹ * κ.1 * δ.1, diamond_conj_mem_level S v hv h κ⟩ e y y' hy
  rw [level_character_conj_diamond S v hv hb h κ] at this
  exact this

end Gen

variable {D : D7} {u : D.what₂.Word}

def DiamondElementsExist (Tf : FormsTied D u) : Prop :=
  ∀ i (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ), ∃ k : ℤ, (k : (D.mem u).A.Fv v) = a ∧
    ∃ δ, IsDia (Tf.cls i hi).lev (Tf.atT.eV v).1 (Tf.atT.eV v).2 k δ

theorem diamond_mul_of_elements_prime_to_bad (Tf : FormsTied D u) (hE : DiamondElementsExist Tf) (hb : ∀ v, (Tf.atT.eV v).1 ∉ badG D) :
    Formalism.MainNotions.product_first_zeroth_parts.DiaMul D u := by
  intro i hi v φ hφ
  obtain ⟨g, hg, hgφ⟩ := ((Tf.val i hi).Fi φ).1 hφ
  have hval : ∀ c, φ c = fun z => g ((Tf.cls i hi).y c) ((Tf.val i hi).eY z) := by
    intro c; funext z
    have := congrFun (congrFun hgφ c) ((Tf.val i hi).eY z)
    simp only [Equiv.symm_apply_apply] at this
    exact this.symm
  have hgA : g ∈ AdFun (Tf.cls i hi).lev (embT D) := (Submodule.mem_inf.1 hg).1
  have hdia : ∀ a c, Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a φ c = (D.fm u).dilT i v a c (φ ((D.fm u).dil i v a c)) :=
    fun a c => rfl
  refine ⟨?_, fun a b => ?_⟩
  · funext c
    rw [hdia, hval ((D.fm u).dil i v 1 c),
      (Tf.val i hi).dilT v 1 1 (by simp) c 1 (is_diamond_one _ _ _) g hgA, mul_one, hval c]
  · funext c
    obtain ⟨ka, hka, δa, hδa⟩ := hE i hi v a
    obtain ⟨kb, hkb, δb, hδb⟩ := hE i hi v b
    have hab : ((ka * kb : ℤ) : (D.mem u).A.Fv v) = ((a * b : ((D.mem u).A.Fv v)ˣ) : (D.mem u).A.Fv v) := by
      rw [Int.cast_mul, hka, hkb, Units.val_mul]
    have h1 : Formalism.MainNotions.product_first_zeroth_parts.dia D u i v b φ ((D.fm u).dil i v a c) =
        fun z => g ((Tf.cls i hi).y ((D.fm u).dil i v a c) * δb) ((Tf.val i hi).eY z) := by
      rw [hdia, hval, (Tf.val i hi).dilT v b kb hkb _ δb hδb g hgA]
    have hg' := adelic_function_right_translate_diamond (Tf.cls i hi).lev (embT D) _ _ (hb v) hδb hgA
    have h2 := (Tf.val i hi).dilT v a ka hka c δa hδa _ hg'
    rw [hdia (a * b) c, hval ((D.fm u).dil i v (a * b) c),
      (Tf.val i hi).dilT v (a * b) (ka * kb) hab c (δa * δb) (is_diamond_mul _ _ _ hδa hδb) g hgA,
]
    show _ = (D.fm u).dilT i v a c (Formalism.MainNotions.product_first_zeroth_parts.dia D u i v b φ ((D.fm u).dil i v a c))
    rw [h1, h2]
    funext z
    simp only [mul_assoc]

theorem level_prime_ne_type_prime (A : AtTTied u) (j : Fin 2) : (D.mem u).A.T ≠ D.host.g j := by
  intro hTg
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 A.piU_cong
  have hdiv : D.host.g j ∣ D.host.QS * D.host.q * D.host.d * (D.host.g 0 * D.host.g 1) ^ 2 := by
    apply Dvd.dvd.mul_left
    fin_cases j
    · exact Dvd.dvd.pow (Dvd.intro _ rfl) two_ne_zero
    · exact Dvd.dvd.pow (Dvd.intro_left _ rfl) two_ne_zero
  obtain ⟨M, hM⟩ := hdiv
  set N : ℕ := D.host.QS * D.host.q * D.host.d * (D.host.g 0 * D.host.g 1) ^ 2 with hN
  have hpi : ((A.piU : 𝓞 D.host.E) : D.host.E) = 1 + (r : D.host.E) * (N : D.host.E) := by
    have := congrArg (fun x : 𝓞 D.host.E => (x : D.host.E)) hr
    push_cast at this
    linear_combination -this
  have hcpi : D.host.conj ((A.piU : 𝓞 D.host.E) : D.host.E) =
      1 + D.host.conj (r : D.host.E) * (N : D.host.E) := by
    rw [hpi, map_add, map_one, map_mul, map_natCast]
  have hNM : (N : D.host.E) = (D.host.g j : D.host.E) * (M : D.host.E) := by
    rw [hM]; push_cast; ring
  have h0 := A.piU_norm
  rw [hcpi, hpi, hTg] at h0
  set r' := D.host.conj (r : D.host.E)
  have key : (D.host.g j : D.host.E) * (1 - (M : D.host.E) * ((r : D.host.E) + r' + (r : D.host.E) * r' * N)) = 1 := by
    linear_combination (-1 : D.host.E) * h0 + ((r : D.host.E) + r' + (r : D.host.E) * r' * N) * hNM
  have hr' : IsIntegral ℤ r' := map_isIntegral_int D.host.conj (RingOfIntegers.isIntegral_coe r)
  have hrI : IsIntegral ℤ (r : D.host.E) := RingOfIntegers.isIntegral_coe r
  have hint : IsIntegral ℤ (1 - (M : D.host.E) * ((r : D.host.E) + r' + (r : D.host.E) * r' * N)) := by
    refine isIntegral_one.sub (IsIntegral.mul ?_ ((hrI.add hr').add ((hrI.mul hr').mul ?_)))
    · simpa using (isIntegral_algebraMap (R := ℤ) (A := D.host.E) (x := (M : ℤ)))
    · simpa using (isIntegral_algebraMap (R := ℤ) (A := D.host.E) (x := (N : ℤ)))
  have hg0 : (D.host.g j : D.host.E) ≠ 0 := by
    exact_mod_cast (D.host.g_prime j).ne_zero
  have hinv : (1 - (M : D.host.E) * ((r : D.host.E) + r' + (r : D.host.E) * r' * N)) =
      algebraMap ℚ D.host.E ((D.host.g j : ℚ)⁻¹) := by
    rw [map_inv₀, map_natCast]
    exact (eq_inv_of_mul_eq_one_right key)
  rw [hinv] at hint
  have hq : IsIntegral ℤ ((D.host.g j : ℚ)⁻¹) :=
    (isIntegral_algebraMap_iff (algebraMap ℚ D.host.E).injective).1 hint
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hq
  have hy' : (y : ℚ) * (D.host.g j : ℚ) = 1 := by
    rw [show (y : ℚ) = algebraMap ℤ ℚ y from rfl, hy]
    exact inv_mul_cancel₀ (by exact_mod_cast (D.host.g_prime j).ne_zero)
  have hyz : y * (D.host.g j : ℤ) = 1 := by exact_mod_cast hy'
  have hd : ((D.host.g j : ℕ) : ℤ) ∣ ((1 : ℕ) : ℤ) := ⟨y, by rw [Nat.cast_one, ← hyz, mul_comm]⟩
  exact (D.host.g_prime j).not_dvd_one (Int.natCast_dvd_natCast.1 hd)

theorem level_places_not_bad (A : AtTTied u) (v : (D.mem u).A.vT) : (A.eV v).1 ∉ badG D := by
  have hT := (A.eV v).2
  have hTp := (D.mem u).A.T_prime
  have key : ∀ j : Fin 2, (D.host.g j : 𝓞 D.host.F) ∉ (A.eV v).1.asIdeal := by
    intro j hj
    have hcop : Nat.Coprime (D.mem u).A.T (D.host.g j) :=
      (Nat.coprime_primes hTp (D.host.g_prime j)).2 (level_prime_ne_type_prime A j)
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
    have h1 : ((a * (D.mem u).A.T + b * D.host.g j : ℤ) : 𝓞 D.host.F) ∈ (A.eV v).1.asIdeal := by
      push_cast
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hT) (Ideal.mul_mem_left _ _ hj)
    rw [hab, Int.cast_one] at h1
    exact (A.eV v).1.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  rintro (h | h)
  · exact key 0 h
  · exact key 1 h

theorem diamond_mul_of_diamond_elements (Tf : FormsTied D u) (hE : DiamondElementsExist Tf) : Formalism.MainNotions.product_first_zeroth_parts.DiaMul D u :=
  diamond_mul_of_elements_prime_to_bad Tf hE (level_places_not_bad Tf.atT)

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL6.DiamondPreservesRationalFormZero
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Classical

variable (D : D7) (u : D.what₂.Word)

def t1A : Prop :=
  (∀ i, i ≤ D.R.m → ∀ v, ∀ φ ∈ (D.fm u).Fi i,
    Uop D u i v φ ∈ (D.fm u).Fi i ∧ Dop D u i v φ ∈ (D.fm u).Fi i ∧ ∀ a, dia D u i v a φ ∈ (D.fm u).Fi i) ∧
  (∀ i, i ≤ D.R.m → ∀ v v', v ≠ v' → ∀ φ ∈ (D.fm u).Fi i,
    Uop D u i v (Uop D u i v' φ) = Uop D u i v' (Uop D u i v φ)) ∧
  (∀ i, i ≤ D.R.m → ∀ v, ∀ φ ∈ (D.fm u).Fi i, ∀ ψ ∈ (D.fm u).Fi i,
    (D.fm u).ipC i (Uop D u i v φ) ψ = (D.fm u).ipC i φ (Dop D u i v ψ)) ∧
  (∀ i, i ≤ D.R.m → ∀ w, OverT D u w → (D.fm u).seenP w = true → ∀ v,
    Into D u w (Uop D u i v) ((D.fm u).Bw i w v) ((D.fm u).S i w) ∧
    Into D u w (Dop D u i v) ((D.fm u).S i w) ((D.fm u).Bw i w v)) ∧
  (∀ i, i ≤ D.R.m → ∀ w, ¬ OverT D u w → ∀ v,
    Into D u w (Uop D u i v) ((D.fm u).S i w) ((D.fm u).S i w) ∧ Into D u w (Dop D u i v) ((D.fm u).S i w) ((D.fm u).S i w)) ∧
  (∀ i, i ≤ D.R.m → ∀ v, ∀ φ ∈ (D.fm u).Fi i, Dop D u i v (Uop D u i v φ) =
    ((D.mem u).A.T : ℂ) ^ (D.R.N i - 1) • φ - ((D.mem u).A.T : ℂ) ^ (D.R.N i - 2) • Nm D u i v φ
      + ((D.mem u).A.T : ℂ) ^ (D.R.N i - 2) • trp D u i v φ)

def t1c7 : Prop :=
  ∀ v, ∀ x ∈ (D.fm u).ramSub,
    (∃ y ∈ (D.fm u).ramSub, (D.fm u).emb 0 y = Uop D u 0 v ((D.fm u).emb 0 x)) ∧
    (∃ y ∈ (D.fm u).ramSub, (D.fm u).emb 0 y = Dop D u 0 v ((D.fm u).emb 0 x)) ∧
    ∀ a, ∃ y ∈ (D.fm u).ramSub, (D.fm u).emb 0 y = dia D u 0 v a ((D.fm u).emb 0 x)

def t1c8 : Prop :=
  ∀ w, ¬ OverT D u w → ∀ v,
    Into D u w (Uop D u 0 v) (Sram D u w) (Sram D u w) ∧
    Into D u w (Dop D u 0 v) (Sram D u w) (Sram D u w) ∧
    ∀ a, Into D u w (dia D u 0 v a) (Sram D u w) (Sram D u w)

def t1c9 : Prop :=
  ∀ i, i ≤ D.R.m → ∀ v, ∀ φ ∈ MramI D u i,
    Uop D u i v φ ∈ MramI D u i ∧ Dop D u i v φ ∈ MramI D u i ∧
    (∀ a, dia D u i v a φ ∈ MramI D u i) ∧ trp D u i v φ = 0 ∧
    Dop D u i v (Uop D u i v φ) = ((D.mem u).A.T : ℂ) ^ (D.R.N i - 1) • φ ∧
    Uop D u i v (Dop D u i v φ) = ((D.mem u).A.T : ℂ) ^ (D.R.N i - 1) • φ

def DiamondCommutesHecke : Prop :=
  ∀ i, i ≤ D.R.m → ∀ v v' (a : ((D.mem u).A.Fv v')ˣ), ∀ φ ∈ (D.fm u).Fi i,
    dia D u i v' a (Uop D u i v φ) = Uop D u i v (dia D u i v' a φ) ∧
    dia D u i v' a (Dop D u i v φ) = Dop D u i v (dia D u i v' a φ) ∧
    ∀ b : ((D.mem u).A.Fv v)ˣ, dia D u i v' a (dia D u i v b φ) = dia D u i v b (dia D u i v' a φ)

def TraceDiamondInvariant : Prop :=
  ∀ i, i ≤ D.R.m → ∀ v (a : ((D.mem u).A.Fv v)ˣ), ∀ φ ∈ (D.fm u).Fi i,
    trp D u i v (dia D u i v a φ) = trp D u i v φ

def HeckeRationalLevelZero : Prop :=
  ∀ v x, (∃ y, (D.fm u).emb 0 y = Uop D u 0 v ((D.fm u).emb 0 x)) ∧
    (∃ y, (D.fm u).emb 0 y = Dop D u 0 v ((D.fm u).emb 0 x))

theorem norm_eq_sum_diamond (i : ℕ) (v : (D.mem u).A.vT) (φ : Fn D u i) :
    Nm D u i v φ = ∑ a : ((D.mem u).A.Fv v)ˣ, dia D u i v a φ := by
  unfold Nm; rw [LinearMap.sum_apply]

theorem mem_ramified_forms_iff {i : ℕ} (φ : Fn D u i) :
    φ ∈ MramI D u i ↔ φ ∈ (D.fm u).Fi i ∧ ∀ v, Nm D u i v φ = 0 := by
  unfold MramI
  simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]

theorem U_D_of_D_U_on_finite_dim {V : Type*} [AddCommGroup V] [Module ℂ V] (W : Submodule ℂ V) [FiniteDimensional ℂ W]
    (U Dm : V →ₗ[ℂ] V) (c : ℂ) (hc : c ≠ 0) (hU : ∀ x ∈ W, U x ∈ W)
    (hDU : ∀ x ∈ W, Dm (U x) = c • x) : ∀ x ∈ W, U (Dm x) = c • x := by
  intro x hx
  have hinj : Function.Injective (U.restrict hU) := by
    intro a b hab
    have h1 : U a = U b := congrArg Subtype.val hab
    have h2 : c • (a : V) = c • (b : V) := by rw [← hDU a a.2, ← hDU b b.2, h1]
    exact Subtype.ext (smul_right_injective V hc h2)
  obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.1 hinj) ⟨x, hx⟩
  have hy' : U y = x := congrArg Subtype.val hy
  rw [← hy', hDU y y.2, map_smul]

theorem forms_finite_dimensional (i : ℕ) : FiniteDimensional ℂ ((D.fm u).Fi i) := by
  have h := FiniteDimensional.span_of_finite ℂ
    (Set.finite_range (fun a => (D.fm u).emb i (((D.fm u).lat i).b a)))
  rwa [((D.fm u).emb_basis i).2] at h

theorem ramified_forms_finite_dimensional (i : ℕ) : FiniteDimensional ℂ (MramI D u i) := by
  have := forms_finite_dimensional D u i
  exact Submodule.finiteDimensional_of_le (inf_le_left : MramI D u i ≤ (D.fm u).Fi i)

theorem two_le_rank_of_level (i : ℕ) : 2 ≤ D.R.N i := by
  have := D.R.m_add_three_le_k; unfold Ranks.N; omega

def HeckeRelationsInputs : Prop :=
  ∀ (D : D7) (u : D.what₂.Word), FormsCompatible D u → HidaSetting D u →
    t1A D u ∧ DiamondCommutesHecke D u ∧ TraceDiamondInvariant D u ∧ HeckeRationalLevelZero D u

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL6.FrobeniusIdentitiesNoKernelOfClauses
section
noncomputable section

open Finset

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

theorem sum_units_addChar_mul {k : Type} [Field k] [Fintype k] [DecidableEq k] (ψ : AddChar k ℂ) (hψ : ψ ≠ 1)
    (c : k) (hc : c ≠ 0) : ∑ b : kˣ, ψ (c * (b : k)) = -1 := by
  have h1 : ∑ b : kˣ, ψ (c * (b : k)) = ∑ b : kˣ, ψ (b : k) := by
    exact Fintype.sum_equiv (Equiv.mulLeft (Units.mk0 c hc)) _ _ (fun b => by simp)
  rw [h1]
  have h2 : ∑ x : k, ψ x = 0 := AddChar.sum_eq_zero_of_ne_one hψ
  have h3 : ∑ x : k, ψ x = ψ 0 + ∑ b : kˣ, ψ (b : k) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : k))]
    congr 1
    refine Finset.sum_bij' (fun x hx => Units.mk0 x (Finset.ne_of_mem_erase hx)) (fun b _ => (b : k)) ?_ ?_ ?_ ?_ ?_
    · intros; exact Finset.mem_univ _
    · intro b _; simp
    · intro x hx; simp
    · intro b _; simp
    · intro x hx; simp
  rw [h3, AddChar.map_zero_eq_one] at h2
  linear_combination h2

theorem sum_units_gauss_coeff {k : Type} [Field k] [Fintype k] [DecidableEq k] (ψ : AddChar k ℂ) (hψ : ψ ≠ 1)
    (c : kˣ) : ∑ b : kˣ, ψ ((c : k) * (b : k)) * ψ (-(b : k)) =
      (Fintype.card k : ℂ) * (if c = 1 then 1 else 0) - 1 := by
  have e : ∀ b : kˣ, ψ ((c : k) * (b : k)) * ψ (-(b : k)) = ψ (((c : k) - 1) * (b : k)) := by
    intro b; rw [← AddChar.map_add_eq_mul]; congr 1; ring
  simp only [e]
  by_cases hc : c = 1
  · subst hc
    simp only [Units.val_one, sub_self, zero_mul, AddChar.map_zero_eq_one, Finset.sum_const, Finset.card_univ,
      Fintype.card_units, if_true, mul_one, nsmul_eq_mul]
    have : 1 ≤ Fintype.card k := Fintype.card_pos
    push_cast [Nat.cast_sub this]
    ring
  · have hc' : (c : k) - 1 ≠ 0 := by
      intro h; apply hc; ext; simpa [sub_eq_zero] using h
    rw [sum_units_addChar_mul ψ hψ _ hc', if_neg hc]; ring

variable (D : Formalism.BasicNotions.D7) (u : D.what₂.Word)

theorem gs_gsD_of_diaMul (h : Formalism.MainNotions.product_first_zeroth_parts.DiaMul D u) :
    ∀ i, i ≤ D.R.m → ∀ v, ∀ φ ∈ (D.fm u).Fi i,
      Formalism.MainNotions.product_first_zeroth_parts.Gs D u i v (Formalism.MainNotions.product_first_zeroth_parts.GsD D u i v φ) = ((D.mem u).A.T : ℂ) • φ - Formalism.MainNotions.product_first_zeroth_parts.Nm D u i v φ := by
  intro i hi v φ hφ
  obtain ⟨h1, hm⟩ := h i hi v φ hφ
  set ψ := (D.mem u).A.psiT v with hψdef
  have hψ : ψ ≠ 1 := (D.mem u).A.psiT_ne v
  have step1 : Formalism.MainNotions.product_first_zeroth_parts.Gs D u i v (Formalism.MainNotions.product_first_zeroth_parts.GsD D u i v φ) =
      ∑ a : ((D.mem u).A.Fv v)ˣ, ∑ b : ((D.mem u).A.Fv v)ˣ,
        (ψ (a : (D.mem u).A.Fv v) * ψ (-(b : (D.mem u).A.Fv v))) • Formalism.MainNotions.product_first_zeroth_parts.dia D u i v (a * b⁻¹) φ := by
    simp only [Formalism.MainNotions.product_first_zeroth_parts.Gs, Formalism.MainNotions.product_first_zeroth_parts.GsD, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
      Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    rw [hm a b⁻¹, mul_comm]
  have step2 : ∀ b : ((D.mem u).A.Fv v)ˣ,
      ∑ a : ((D.mem u).A.Fv v)ˣ, (ψ (a : (D.mem u).A.Fv v) * ψ (-(b : (D.mem u).A.Fv v))) •
        Formalism.MainNotions.product_first_zeroth_parts.dia D u i v (a * b⁻¹) φ =
      ∑ c : ((D.mem u).A.Fv v)ˣ, (ψ ((c : (D.mem u).A.Fv v) * (b : (D.mem u).A.Fv v)) *
        ψ (-(b : (D.mem u).A.Fv v))) • Formalism.MainNotions.product_first_zeroth_parts.dia D u i v c φ := by
    intro b
    refine (Fintype.sum_equiv (Equiv.mulRight b) _ _ (fun c => ?_)).symm
    simp [mul_assoc]
  have step3 : ∀ c : ((D.mem u).A.Fv v)ˣ,
      ∑ b : ((D.mem u).A.Fv v)ˣ, (ψ ((c : (D.mem u).A.Fv v) * (b : (D.mem u).A.Fv v)) *
        ψ (-(b : (D.mem u).A.Fv v))) • Formalism.MainNotions.product_first_zeroth_parts.dia D u i v c φ =
      (((Fintype.card ((D.mem u).A.Fv v) : ℂ) * (if c = 1 then 1 else 0)) • Formalism.MainNotions.product_first_zeroth_parts.dia D u i v c φ -
        Formalism.MainNotions.product_first_zeroth_parts.dia D u i v c φ) := by
    intro c
    rw [← Finset.sum_smul, sum_units_gauss_coeff ψ hψ, sub_smul, one_smul]
  rw [step1, Finset.sum_comm, Finset.sum_congr rfl (fun b _ => step2 b), Finset.sum_comm,
    Finset.sum_congr rfl (fun c _ => step3 c), Finset.sum_sub_distrib,
    Fintype.sum_eq_single 1 (fun c hc => by simp [hc])]
  simp only [if_true, mul_one, h1, (D.mem u).A.card_Fv v, Formalism.MainNotions.product_first_zeroth_parts.Nm, LinearMap.sum_apply]

theorem ffAll_iso_of (i : ℕ)
    (hc : ∀ v, ∀ φ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i, Formalism.MainNotions.product_first_zeroth_parts.FFop D u i v φ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i)
    (hd : ∀ v, ∀ φ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i, ∀ ψ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i,
      (D.fm u).ipC i (Formalism.MainNotions.product_first_zeroth_parts.FFop D u i v φ) (Formalism.MainNotions.product_first_zeroth_parts.FFop D u i v ψ) =
        ((D.mem u).A.T : ℂ) ^ D.R.N i * (D.fm u).ipC i φ ψ) :
    ∀ φ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i, ∀ ψ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i,
      (D.fm u).ipC i (Formalism.MainNotions.product_first_zeroth_parts.FFall D u i φ) (Formalism.MainNotions.product_first_zeroth_parts.FFall D u i ψ) =
        ((D.mem u).A.T : ℂ) ^ (D.R.f * D.R.N i) * (D.fm u).ipC i φ ψ := by
  have key : ∀ l : List (D.mem u).A.vT, ∀ φ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i, ∀ ψ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i,
      (l.foldr (fun v g => (Formalism.MainNotions.product_first_zeroth_parts.FFop D u i v).comp g) LinearMap.id) φ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i ∧
      (D.fm u).ipC i ((l.foldr (fun v g => (Formalism.MainNotions.product_first_zeroth_parts.FFop D u i v).comp g) LinearMap.id) φ)
          ((l.foldr (fun v g => (Formalism.MainNotions.product_first_zeroth_parts.FFop D u i v).comp g) LinearMap.id) ψ) =
        ((D.mem u).A.T : ℂ) ^ (l.length * D.R.N i) * (D.fm u).ipC i φ ψ := by
    intro l
    induction l with
    | nil => intro φ hφ ψ _; simp [hφ]
    | cons v l ih =>
      intro φ hφ ψ hψ
      obtain ⟨h1, h2⟩ := ih φ hφ ψ hψ
      obtain ⟨h3, _⟩ := ih ψ hψ ψ hψ
      refine ⟨?_, ?_⟩
      · simp only [List.foldr_cons, LinearMap.comp_apply]; exact hc v _ h1
      · simp only [List.foldr_cons, LinearMap.comp_apply, List.length_cons]
        rw [hd v _ h1 _ h3, h2, ← mul_assoc, ← pow_add]
        congr 2; ring
  intro φ hφ ψ hψ
  have := (key (Finset.univ : Finset (D.mem u).A.vT).toList φ hφ ψ hψ).2
  rw [Finset.length_toList, Finset.card_univ, (D.mem u).A.card_vT] at this
  exact this

theorem frobenius_identities_no_kernel_of_clauses
    (h7a : ∀ i, i ≤ D.R.m → ∀ v, ∀ φ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i,
      Formalism.MainNotions.product_first_zeroth_parts.FFop D u i v φ = Formalism.MainNotions.product_first_zeroth_parts.Dop D u i v (Formalism.MainNotions.product_first_zeroth_parts.Gs D u i v φ))
    (h7c : ∀ i, i ≤ D.R.m → ∀ v, ∀ φ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i, Formalism.MainNotions.product_first_zeroth_parts.FFop D u i v φ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i)
    (h7d : ∀ i, i ≤ D.R.m → ∀ v, ∀ φ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i, ∀ ψ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i,
      (D.fm u).ipC i (Formalism.MainNotions.product_first_zeroth_parts.FFop D u i v φ) (Formalism.MainNotions.product_first_zeroth_parts.FFop D u i v ψ) =
        ((D.mem u).A.T : ℂ) ^ D.R.N i * (D.fm u).ipC i φ ψ)
    (hD : Formalism.MainNotions.product_first_zeroth_parts.DiaMul D u) : FrobeniusOperatorRelations D u :=
  ⟨h7a, gs_gsD_of_diaMul D u hD, h7c, h7d,
    fun i hi => ffAll_iso_of D u i (h7c i hi) (h7d i hi)⟩

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL6.RamifiedMaxSlopeLe
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions

theorem max_slope_mono {R V E : Type} [Ring R] [AddCommGroup V] [Module R V] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (ρ : V →+ E) (L N : Submodule R V)
    (hL : Formalism.HN.IsLat ρ L) (hNL : N ≤ L) (hN : N ≠ ⊥) :
    Formalism.HN.muMax ρ N ≤ Formalism.HN.muMax ρ L := by
  have hLne : L ≠ ⊥ := fun h => hN (le_bot_iff.1 (h ▸ hNL))
  have hzl : (Formalism.HN.zl ρ N : Set E) ⊆ (Formalism.HN.zl ρ L : Set E) := by
    rintro x ⟨y, hy, rfl⟩
    exact ⟨y, hNL hy, rfl⟩
  have hNlat : Formalism.HN.IsLat ρ N := by
    refine ⟨hL.1.mono hNL, ?_⟩
    have := hL.2
    exact DiscreteTopology.of_subset (s := (Formalism.HN.zl ρ L : Set E)) inferInstance hzl
  have cL := (Formalism.HN.slope_characterization R V E ρ L hL hLne).1 (Formalism.HN.muMax ρ L)
  have cN := (Formalism.HN.slope_characterization R V E ρ N hNlat hN).1 (Formalism.HN.muMax ρ L)
  exact cN.2 fun M hM => cL.1 le_rfl M (hM.trans hNL)

theorem ramified_max_slope_le (D : D7) (u : D.what₂.Word) (hne : (D.fm u).ramL ≠ ⊥) :
    (D.fm u).ramLat.muMax ≤ ((D.fm u).lat 0).muMax := by
  have hg := (D.fm u).lat_good 0
  have hlat := (Formalism.HN.place_lattice_structure D.what₂.LL ((D.fm u).lat 0).V ((D.fm u).lat 0).ι ((D.fm u).lat 0).b
    ((D.fm u).lat 0).X hg.1 ((D.fm u).lat 0).L hg.2.1).1
  have hle : (D.fm u).ramL ≤ ((D.fm u).lat 0).L := inf_le_left
  have h := max_slope_mono _ _ _ hlat hle hne
  unfold Formalism.BasicNotions.HLat.muMax Formalism.HN.muMaxDef
  show 2 * Formalism.HN.muMax (Formalism.HermitianLatticesTheory.realize ((D.fm u).lat 0).b ((D.fm u).lat 0).X) (D.fm u).ramL - _ + _ ≤ _
  linarith

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

end
end

