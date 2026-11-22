import Development.WeilBound.ThetaLifts.TowerModels.Bundle0002
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0070
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.Bundle0002
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0063
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.PlaneRemovalConfiguration

-- bundled from Development.WeilBound.ThetaLifts.TowerModels.PlaneCodiff
section
noncomputable section

namespace PositivityTheory.ThKG.Tow.Pln

open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem trace_mixedEmbedding (y : F) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (mixedEmbedding F y) = (Algebra.trace ℚ F y : ℝ) :=
  _root_.UpperTheory.Reformulated.B.DYhb7.main y

theorem psi_fin_rat {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (x : F) :
    ψ (pairA F 0 (algebraMap F (Af F) x)) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F x : ℚ) : ℂ)) := by
  have e : pairA F 0 (algebraMap F (Af F) x) =
      algebraMap F (AF F) x + pairA F (algebraMap F (Ainf F) (-x)) 0 := by
    refine Prod.ext ?_ (add_zero _).symm
    show (0 : Ainf F) = algebraMap F (Ainf F) x + algebraMap F (Ainf F) (-x)
    rw [map_neg, add_neg_cancel]
  have hat : At (evI F) (pairA F (algebraMap F (Ainf F) (-x)) 0) := by
    intro u hu
    have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
    refine Prod.ext ?_ ?_
    · change u.1 * _ = 0
      rw [h1, zero_mul]
    · change u.2 * 0 = 0
      rw [mul_zero]
  rw [e, AddChar.map_add_eq_mul, hψ.2.1, one_mul, hψ.2.2 _ hat]
  have h2 : evI F (pairA F (algebraMap F (Ainf F) (-x)) 0) = mixedEmbedding F (-x) := by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (Ainf F) (-x)) = _
    rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  rw [h2, trace_mixedEmbedding, map_neg]
  congr 1
  push_cast
  ring

theorem psi_int {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (t : F)
    (ht : ∀ a : 𝓞 F, ∃ k : ℤ, Algebra.trace ℚ F ((a : F) * t) = k) (α : Af F) (hα : ∀ v, α v ∈ v.adicCompletionIntegers F) :
    ψ (pairA F 0 (α * algebraMap F (Af F) t)) = 1 := by
  refine GlobalTheory.IntDense.addChar_eq_one_of_integral F ψ hψ.1 t (fun a => ?_) α hα
  obtain ⟨k, hk⟩ := ht a
  rw [psi_fin_rat hψ, hk, Complex.exp_eq_one_iff]
  exact ⟨k, by push_cast; ring⟩

theorem trace_cm (h : IsCMExt F E σ) (x : E) : algebraMap F E (Algebra.trace F E x) = x + σ x := by
  classical
  have h1 := trace_eq_sum_embeddings (K := F) (L := E) (AlgebraicClosure E) (x := x)
  let τ : E →ₐ[F] AlgebraicClosure E := IsScalarTower.toAlgHom F E _
  have h2 : (Finset.univ : Finset (E →ₐ[F] AlgebraicClosure E)) = {τ, τ.comp σ} := by
    ext τ'
    simpa using eq_or_eq_comp_conj h τ τ'
  rw [h2, Finset.sum_pair (comp_conj_ne h τ).symm] at h1
  apply (algebraMap E (AlgebraicClosure E)).injective
  rw [← IsScalarTower.algebraMap_apply, h1, map_add]
  rfl

theorem val_le_one_of_codiff {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {v : Pl F} (hv : PsiUnr ψ v) (a : F)
    (ha : ∀ o : 𝓞 F, IsIntegral ℤ (Algebra.trace ℚ F (o * a))) : Valued.v (algebraMap F (Fv F v) a) ≤ 1 := by
  have h2 := psi_int hψ a fun o => by
    obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.1 (ha o)
    exact ⟨k, hk.symm⟩
  refine (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 ((hv _).1 fun y hy => ?_)
  have h3 := h2 (singleFin v y) fun w => by
    by_cases hw : w = v
    · subst hw
      change evalV _ w (singleFin w y) ∈ _
      rw [evalV_singleFin_self]
      exact hy
    · change evalV _ w (singleFin v y) ∈ _
      rw [evalV_singleFin_ne hw]
      exact zero_mem _
  have e : singleFin v y * algebraMap F (Af F) a = singleFin v (algebraMap F (Fv F v) a * y) := by
    apply af_ext
    intro u
    by_cases hu : u = v
    · subst hu
      rw [map_mul, evalV_singleFin_self, evalV_singleFin_self, mul_comm]
      rfl
    · rw [map_mul, evalV_singleFin_ne hu, evalV_singleFin_ne hu, zero_mul]
  rw [e] at h3
  exact h3

variable (E) in

def codE : Submodule (𝓞 E) E where
  carrier := {c | ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * c))}
  zero_mem' o := by simpa using isIntegral_zero
  add_mem' ha hb o := by rw [mul_add, map_add]; exact (ha o).add (hb o)
  smul_mem' a c hc o := by
    have := hc (o * a)
    change IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * (a : E) * c)) at this
    rwa [mul_assoc] at this

theorem one_mem_codE : (1 : E) ∈ codE E := fun o => by
  rw [mul_one]; exact Algebra.isIntegral_trace o.isIntegral_coe

variable (E) in

def intE : Submodule (𝓞 E) E where
  carrier := {c | IsIntegral ℤ c}
  zero_mem' := isIntegral_zero
  add_mem' ha hb := ha.add hb
  smul_mem' a _ hc := a.isIntegral_coe.mul hc

theorem val_le_one_of_intE {v : Pl F} (τ : E →ₐ[F] Fv F v) (c : E) (hc : c ∈ intE E) : Valued.v (τ c) ≤ 1 :=
  apply_coe_mem τ (⟨c, hc⟩ : 𝓞 E)

theorem val_le_one_of_codE (h : IsCMExt F E σ) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {v : Pl F} (hv : PsiUnr ψ v)
    (τ : E →ₐ[F] Fv F v) (c : E) (hc : c ∈ codE E) : Valued.v (τ c) ≤ 1 := by
  have h1 : ∀ o : 𝓞 E, Valued.v (τ (o * c) + τ (σ (o * c))) ≤ 1 := fun o => by
    rw [← map_add, ← trace_cm h, AlgHom.commutes]
    refine val_le_one_of_codiff hψ hv _ fun a => ?_
    have := hc (algebraMap (𝓞 F) (𝓞 E) a * o)
    rw [← Algebra.trace_trace (S := F)] at this
    convert this using 2
    rw [← smul_eq_mul, ← map_smul, Algebra.smul_def, ← mul_assoc]
    rfl
  have hne : ¬ (splitPrime (τ.comp σ)).asIdeal ≤ (splitPrime τ).asIdeal := fun hle =>
    splitPrime_comp_ne h τ (HeightOneSpectrum.ext
      ((splitPrime (τ.comp σ)).isMaximal.eq_of_le (splitPrime τ).isPrime.ne_top hle))
  obtain ⟨p, hp, hp'⟩ := Set.not_subset.1 hne
  have a1 : Valued.v (τ (σ p)) < 1 := (mem_splitPrime (τ.comp σ) p).1 hp
  have a2 : Valued.v (τ p) = 1 := le_antisymm (apply_coe_mem τ p) (not_lt.1 fun e => hp' ((mem_splitPrime τ p).2 e))
  obtain ⟨k, hk⟩ : ∃ k : ℕ, Valued.v (τ (σ p)) ^ k * Valued.v (τ (σ c)) ≤ 1 := by
    by_cases h0 : Valued.v (τ (σ c)) = 0
    · exact ⟨0, by simp [h0]⟩
    · obtain ⟨k, hk⟩ := exists_pow_lt₀ a1 (Units.mk0 _ h0)⁻¹
      refine ⟨k, ?_⟩
      rw [Units.val_inv_eq_inv_val, Units.val_mk0] at hk
      calc _ ≤ (Valued.v (τ (σ c)))⁻¹ * Valued.v (τ (σ c)) := by gcongr
        _ = 1 := inv_mul_cancel₀ h0
  have b1 := h1 (p ^ k)
  have b2 : Valued.v (τ (σ (((p ^ k : 𝓞 E) : E) * c))) ≤ 1 := by
    push_cast
    simpa only [map_mul, map_pow] using hk
  have b3 := Valuation.map_sub_le _ b1 b2
  rw [add_sub_cancel_right] at b3
  push_cast at b3
  simpa only [map_mul, map_pow, a2, one_pow, one_mul] using b3

end PositivityTheory.ThKG.Tow.Pln

end
end

-- bundled from Development.WeilBound.ThetaLifts.TowerModels.PlaneLat
section
noncomputable section

namespace PositivityTheory.ThKG.Tow.Pln

open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_partner (h : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {ε : E} (hε : ε = 1 ∨ ε = -1)
    (hJ : ∀ i j, σ (J j i) = ε * J i j) (D : Submodule (𝓞 E) E) (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG)
    (hd : ∀ y, y ∈ L ↔ ∀ x ∈ L, form σ J y x ∈ D) (θ : 𝓞 E) (hθ : (θ : E) + σ θ = 1) (x : Fin n → E)
    (hxx : form σ J x x = 0) (z₀ : Fin n → E) (hz₀ : z₀ ∈ L) (hz₀x : form σ J z₀ x ≠ 0) :
    ∃ y, form σ J y y = 0 ∧ form σ J x y = 1 ∧ ∀ z ∈ L, form σ J z x • y ∈ L ∧ form σ J z y • x ∈ L := by
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> simp
  have hσε : σ ε = ε := by rcases hε with rfl | rfl <;> simp
  have hεD : ∀ a ∈ D, ε * a ∈ D := fun a ha => by
    rcases hε with rfl | rfl
    · simpa using ha
    · simpa using ha
  have hεL : ∀ a ∈ L, ε • a ∈ L := fun a ha => by
    rcases hε with rfl | rfl
    · simpa using ha
    · simpa using ha
  have sw : ∀ a b, form σ J b a = ε * σ (form σ J a b) := fun a b => by
    rw [form_swap h hJ, ← mul_assoc, hεε, one_mul]
  let C₀ : Submodule (𝓞 E) E := L.map ((formL (σ := σ) J x).restrictScalars (𝓞 E))
  let C : FractionalIdeal (𝓞 E)⁰ E := ⟨C₀, FractionalIdeal.isFractional_of_fg (hfg.map _)⟩
  have hC : ∀ z ∈ L, form σ J z x ∈ C := fun z hz => ⟨z, hz, rfl⟩
  have hC0 : C ≠ 0 := fun e => hz₀x (by simpa [e] using hC z₀ hz₀)
  have hinv : C * C⁻¹ = 1 := mul_inv_cancel₀ hC0
  have key : ∀ t ∈ C * C⁻¹, ∃ y, form σ J y x = t ∧ ∀ c ∈ C, c • y ∈ L := fun t ht => by
    refine FractionalIdeal.mul_induction_on ht (fun a ha b hb => ?_) ?_
    · obtain ⟨z, hz, rfl⟩ := ha
      refine ⟨b • z, by rw [form_smul_left, mul_comm]; rfl, fun c hc => ?_⟩
      have := FractionalIdeal.mul_mem_mul hc hb
      rw [hinv, FractionalIdeal.mem_one_iff] at this
      obtain ⟨o, ho⟩ := this
      rw [smul_smul, ← ho, algebraMap_smul]
      exact L.smul_mem o hz
    · rintro _ _ ⟨y, rfl, hy⟩ ⟨y', rfl, hy'⟩
      exact ⟨y + y', form_add_left _ _ _ _, fun c hc => by rw [smul_add]; exact L.add_mem (hy c hc) (hy' c hc)⟩
  obtain ⟨y₁, hy₁, hy₁L⟩ := key 1 (by rw [hinv]; exact FractionalIdeal.one_mem_one _)
  obtain ⟨y₀, hy₀x, hy₀L⟩ : ∃ y₀, form σ J y₀ x = ε ∧ ∀ c ∈ C, c • y₀ ∈ L :=
    ⟨ε • y₁, by rw [form_smul_left, hy₁, mul_one], fun c hc => by rw [smul_comm]; exact hεL _ (hy₁L c hc)⟩
  have hxy₀ : form σ J x y₀ = 1 := by rw [sw, hy₀x, hσε, hεε]
  have crit : ∀ y, (∀ c ∈ C, c • y ∈ L) → ∀ z ∈ L, form σ J z y • x ∈ L := fun y hy z hz => by
    refine (hd _).2 fun z' hz' => ?_
    have := hεD _ ((hd z).1 hz _ (hy _ (hC z' hz')))
    rw [form_smul_right] at this
    rw [form_smul_left, sw z' x]
    convert this using 1
    ring
  set q := form σ J y₀ y₀ with hq
  have hqq : ε * σ q = q := (sw y₀ y₀).symm
  have hyL : ∀ c ∈ C, c • (y₀ - ((θ : E) * q) • x) ∈ L := fun c hc => by
    have := L.smul_mem θ (crit y₀ hy₀L _ (hy₀L c hc))
    rw [form_smul_left, ← algebraMap_smul E θ, smul_smul] at this
    rw [smul_sub, smul_smul]
    refine L.sub_mem (hy₀L c hc) ?_
    convert this using 2
    change _ = (θ : E) * _
    ring
  refine ⟨y₀ - ((θ : E) * q) • x, ?_, ?_, fun z hz => ⟨hyL _ (hC z hz), crit _ hyL z hz⟩⟩
  · rw [form_sub_left, form_sub_right, form_sub_right, form_smul_left, form_smul_left, form_smul_right, form_smul_right,
      hxx, hxy₀, hy₀x, ← hq, map_mul]
    linear_combination -q * hθ - σ θ * hqq
  · rw [form_sub_right, form_smul_right, hxx, hxy₀]; ring

theorem exists_max_val {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
    (L : Submodule (𝓞 E) V) (hfg : L.FG) (f : V →ₗ[E] E) (hf : ∃ z ∈ L, f z ≠ 0)
    (S : Finset (HeightOneSpectrum (𝓞 E))) :
    ∃ z₀ ∈ L, f z₀ ≠ 0 ∧ ∀ w ∈ S, ∀ z ∈ L, w.valuation E (f z) ≤ w.valuation E (f z₀) := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | ⟨w₀, hw₀⟩
  · obtain ⟨z, hz, hz0⟩ := hf
    exact ⟨z, hz, hz0, by simp⟩
  have h1 : ∀ w : HeightOneSpectrum (𝓞 E), ∃ c ∈ L, ∀ z ∈ L, w.valuation E (f z) ≤ w.valuation E (f c) := fun w => by
    obtain ⟨G, rfl⟩ := hfg
    obtain ⟨c, hc, hmax⟩ := (insert 0 G).exists_max_image (fun z => w.valuation E (f z)) (by simp)
    refine ⟨c, ?_, fun z hz => ?_⟩
    · rcases Finset.mem_insert.1 hc with rfl | hc
      · exact zero_mem _
      · exact Submodule.subset_span hc
    · induction hz using Submodule.span_induction with
      | mem x hx => exact hmax x (Finset.mem_insert_of_mem hx)
      | zero => simp
      | add x y _ _ hx hy => rw [map_add]; exact (Valuation.map_add _ _ _).trans (max_le hx hy)
      | smul a x _ hx =>
        rw [← algebraMap_smul E a, map_smul, smul_eq_mul, map_mul]
        exact (mul_le_of_le_one_left' (w.valuation_le_one a)).trans hx
  choose c hcL hc using h1
  have hc0 : ∀ w : HeightOneSpectrum (𝓞 E), 0 < w.valuation E (f (c w)) := fun w => by
    obtain ⟨z, hz, hz0⟩ := hf
    exact lt_of_lt_of_le (zero_lt_iff.2 ((map_ne_zero _).2 hz0)) (hc w z hz)
  have h2 : ∀ w w' : HeightOneSpectrum (𝓞 E), ∃ p : 𝓞 E, p ∉ w.asIdeal ∧ (w' ≠ w → p ∈ w'.asIdeal) := fun w w' => by
    by_cases e : w' = w
    · exact ⟨1, (Ideal.ne_top_iff_one _).1 w.isPrime.ne_top, fun h => absurd e h⟩
    · have : ¬ w'.asIdeal ≤ w.asIdeal := fun hle =>
        e (HeightOneSpectrum.ext (w'.isMaximal.eq_of_le w.isPrime.ne_top hle))
      obtain ⟨p, hp, hp'⟩ := Set.not_subset.1 this
      exact ⟨p, hp', fun _ => hp⟩
  choose p hp hp' using h2
  let e : HeightOneSpectrum (𝓞 E) → 𝓞 E := fun w => ∏ w' ∈ S, p w w'
  have he : ∀ w : HeightOneSpectrum (𝓞 E), w.valuation E (algebraMap _ E (e w)) = 1 := fun w => by
    simp only [e, map_prod]
    exact Finset.prod_eq_one fun w' _ => (w.valuation_eq_one_iff_notMem (K := E)).2 (hp w w')
  have he' : ∀ w, ∀ w' ∈ S, w' ≠ w → w'.valuation E (algebraMap _ E (e w)) < 1 := fun w w' hw' hne =>
    (w'.valuation_lt_one_iff_mem (K := E) _).2 (Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem _ hw') (hp' w w' hne))
  have hval : ∀ w ∈ S, w.valuation E (f (∑ w' ∈ S, e w' • c w')) = w.valuation E (f (c w)) := fun w hw => by
    have t : ∀ w', f (e w' • c w') = algebraMap _ E (e w') * f (c w') := fun w' => by
      rw [← algebraMap_smul E (e w'), map_smul, smul_eq_mul]
    rw [← Finset.add_sum_erase S _ hw, map_add, map_sum]
    have a1 : w.valuation E (f (e w • c w)) = w.valuation E (f (c w)) := by rw [t, map_mul, he, one_mul]
    rw [Valuation.map_add_eq_of_lt_left, a1]
    rw [a1]
    refine Valuation.map_sum_lt _ (hc0 w).ne' fun w' hw' => ?_
    rw [t, map_mul]
    calc _ ≤ w.valuation E (algebraMap _ E (e w')) * w.valuation E (f (c w)) := by
          gcongr; exact hc w _ (hcL w')
      _ < _ := mul_lt_of_lt_one_left (hc0 w) (he' w' w hw (Finset.ne_of_mem_erase hw').symm)
  refine ⟨∑ w' ∈ S, e w' • c w', L.sum_mem fun w _ => L.smul_mem _ (hcL w), fun h0 => ?_, fun w hw z hz => ?_⟩
  · have := hval w₀ hw₀
    rw [h0, map_zero] at this
    exact (hc0 w₀).ne this
  · rw [hval w hw]; exact hc w z hz

theorem exists_denom (C : Submodule (𝓞 E) E) (hfg : C.FG) (w : HeightOneSpectrum (𝓞 E))
    (hC : ∀ c ∈ C, w.valuation E c ≤ 1) : ∃ d : 𝓞 E, d ∉ w.asIdeal ∧ ∀ c ∈ C, ∃ o : 𝓞 E, (d : E) * c = o := by
  classical
  obtain ⟨G, rfl⟩ := hfg
  have h1 : ∀ c : E, ∃ d : 𝓞 E, d ∉ w.asIdeal ∧ (w.valuation E c ≤ 1 → ∃ o : 𝓞 E, (d : E) * c = o) := fun c => by
    by_cases hc : w.valuation E c ≤ 1
    · obtain ⟨o, ⟨d, hd⟩, e⟩ := w.exists_primeCompl_mul_eq_of_integer c hc
      exact ⟨d, hd, fun _ => ⟨o, by rw [mul_comm]; exact e⟩⟩
    · exact ⟨1, (Ideal.ne_top_iff_one _).1 w.isPrime.ne_top, fun h => absurd h hc⟩
  choose d hd hd' using h1
  refine ⟨∏ c ∈ G, d c, fun hm => ?_, fun c hc => ?_⟩
  · obtain ⟨c, -, hc⟩ := (Ideal.IsPrime.prod_mem_iff (hp := w.isPrime)).1 hm
    exact hd c hc
  · induction hc using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨o, ho⟩ := hd' x (hC x (Submodule.subset_span hx))
      obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem d hx
      refine ⟨k * o, ?_⟩
      rw [hk]; push_cast; linear_combination (k : E) * ho
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by push_cast; rw [mul_add]; push_cast at ha hb; rw [ha, hb]⟩
    | smul a x _ hx =>
      obtain ⟨b, hb⟩ := hx
      refine ⟨a * b, ?_⟩
      change _ * ((a : E) * x) = (a : E) * (b : E)
      rw [← hb]
      ring

end PositivityTheory.ThKG.Tow.Pln

end
end

-- bundled from Development.WeilBound.ThetaLifts.TowerModels.TowerCodimensionTwoOf
section
noncomputable section

namespace PositivityTheory.ThKG.Tow

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem resEtaPow_of_add_two {R E : Type} [CommRing R] [CommRing E] [Algebra R E] {K : Subgroup Rˣ}
    {χ : Eˣ →* Circle} {n : ℕ} (h : ResEtaPow K χ (n + 2)) : ResEtaPow K χ n := by
  intro a
  rw [h a]
  simp [pow_add]

theorem resEtaPow_div {R E : Type} [CommRing R] [CommRing E] [Algebra R E] {K : Subgroup Rˣ}
    {χ χ' : Eˣ →* Circle} {n m : ℕ} (h : ResEtaPow K χ n) (h' : ResEtaPow K χ' m) :
    ResEtaPow K (χ / χ') (n + m) := by
  intro a
  rw [MonoidHom.div_apply, Circle.coe_div, h a, h' a]
  split_ifs
  · simp
  · rw [div_eq_mul_inv, ← inv_pow, inv_neg, inv_one, ← pow_add]

theorem isHecke_div {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    {χ χ' : Chr F E} (h : IsHecke F E χ) (h' : IsHecke F E χ') : IsHecke F E (χ / χ') := by
  refine ⟨h.1.div' h'.1, fun x => ?_⟩
  simp only [MonoidHom.div_apply, h.2 x, h'.2 x, div_one]

theorem towerB_of (hP : PlaneEx) (hM : ModelEx) (hW : WeilEx) : TowerB := by
  intro F E _ _ _ _ _ σ B a b G X om om' hT hq
  have g := hT.geo
  have c := hT.chars
  have hb := g.aBig
  have hl := g.lt
  obtain ⟨Y', V₁, H, hY', hV₁, hH⟩ := hP.1 F E σ B hT.base (b + 2) b rfl (by omega) G.V' G.q (b + 2 - G.q)
    hq (by omega) g.hV' 0 (b + 1) (by omega) (by omega)
  obtain ⟨W', W₁, H', hW', hW₁, hH'⟩ := hP.2 F E σ B hT.base (a + (b + 2)) (a + b) (by omega) (by omega) G.W
    (a + (b + 2) - (G.p + G.q)) (G.p + G.q) (by omega) (by omega) g.hW a (a + b + 1) (by omega) (by omega)
  have hV0 : (reS G.V G.V).IsHerm σ B (a - G.p) G.p := g.hV
  obtain ⟨M₁, hM₁⟩ := hM F E σ B hT.base a (a + b) (reS G.V G.V) W₁ _ _ _ _ hV0 hW₁
  obtain ⟨M₁', hM₁'⟩ := hM F E σ B hT.base b (a + b) V₁ W₁ _ _ _ _ hV₁ hW₁
  have rα : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range X.α b := resEtaPow_of_add_two c.resα
  obtain ⟨om₁, hom₁⟩ := hW F E σ B hT.base a (a + b) (reS G.V G.V) W₁ _ _ _ _ hV0 hW₁ M₁ hM₁ X.β (X.β / X.α)
    c.heckeβ (isHecke_div c.heckeβ c.heckeα) c.resβ (resEtaPow_div c.resβ rα)
  obtain ⟨om₁', hom₁'⟩ := hW F E σ B hT.base b (a + b) V₁ W₁ _ _ _ _ hV₁ hW₁ M₁' hM₁' X.α (X.α / X.β)
    c.heckeα (isHecke_div c.heckeα c.heckeβ) rα (by rw [Nat.add_comm]; exact resEtaPow_div rα c.resβ)
  refine ⟨G.V, Y', W', ⟨hT.base, ⟨g.lt, g.even, g.kappa, g.eBig, g.aBig, hV0, hY', hW', ⟨g.hM.rat, g.hM.vac, g.hM.std, g.hM.haar, g.hM.dom⟩,
      ⟨g.hM'.rat, g.hM'.vac, g.hM'.std, g.hM'.haar, g.hM'.dom⟩⟩, c, hT.weil, hT.weil'⟩,
    ⟨G.p, G.q - 1, reS G.V G.V, V₁, W₁, M₁, M₁'⟩, H, H', ⟨rfl, rfl, ?_, hH, hH'⟩, om₁, om₁', ⟨hT.base, ?_, ?_, hom₁, hom₁'⟩⟩
  · show G.q - 1 + 1 = G.q
    omega
  · have he := g.eBig
    refine ⟨by omega, ?_, fun w => ?_, ?_, ?_, hV0, ?_, ?_, hM₁, hM₁'⟩
    · obtain ⟨k, hk⟩ := g.even
      exact ⟨k - 1, by omega⟩
    · have := g.kappa w
      push_cast at this ⊢
      omega
    · show 2 * (G.p + (G.q - 1)) + 1 < (a - b) / 2
      omega
    · show 2 * (G.p + (G.q - 1)) + 1 < b
      omega
    · show V₁.IsHerm σ B (G.q - 1) (b - (G.q - 1))
      rw [show b - (G.q - 1) = b + 2 - G.q - 1 by omega]
      exact hV₁
    · show W₁.IsSkew σ B (a + b - (G.p + (G.q - 1))) (G.p + (G.q - 1))
      rw [show a + b - (G.p + (G.q - 1)) = a + (b + 2) - (G.p + G.q) - 1 by omega,
        show G.p + (G.q - 1) = G.p + G.q - 1 by omega]
      exact hW₁
  · exact ⟨c.heckeα, c.heckeβ, rα, c.resβ, c.expα, c.expβ, c.disj, c.sub, c.ram, c.unrα, c.unrβ, c.good⟩

theorem towerA_of (hP : PlaneEx) (hM : ModelEx) (hW : WeilEx) : TowerA := by
  intro F E _ _ _ _ _ σ B b a' G X om om' hT hq0 hp
  have g := hT.geo
  have c := hT.chars
  have hb := g.aBig
  have hl := g.lt
  have he := g.eBig
  rw [hq0] at hb he
  obtain ⟨Y', V₁, H, hY', hV₁, hH⟩ := hP.1 F E σ B hT.base (b + 2) b rfl (by omega) G.V (b + 2 - G.p) G.p
    (by omega) hp g.hV 0 (b + 1) (by omega) (by omega)
  have hW0 := g.hW
  rw [hq0] at hW0
  obtain ⟨W', W₁, H', hW', hW₁, hH'⟩ := hP.2 F E σ B hT.base (b + 2 + a') (b + a') (by omega) (by omega) G.W
    (b + 2 + a' - (G.p + 0)) (G.p + 0) (by omega) (by omega) hW0 0 (b + 1) (by omega) (by omega)
  have hV0' : (reS G.V' G.V').IsHerm σ B 0 (a' - 0) := by
    have := g.hV'
    rw [hq0] at this
    exact this
  obtain ⟨M₁, hM₁⟩ := hM F E σ B hT.base b (b + a') V₁ W₁ _ _ _ _ hV₁ hW₁
  obtain ⟨M₁', hM₁'⟩ := hM F E σ B hT.base a' (b + a') (reS G.V' G.V') W₁ _ _ _ _ hV0' hW₁
  have rβ : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range X.β b := resEtaPow_of_add_two c.resβ
  obtain ⟨om₁, hom₁⟩ := hW F E σ B hT.base b (b + a') V₁ W₁ _ _ _ _ hV₁ hW₁ M₁ hM₁ X.β (X.β / X.α)
    c.heckeβ (isHecke_div c.heckeβ c.heckeα) rβ (resEtaPow_div rβ c.resα)
  obtain ⟨om₁', hom₁'⟩ := hW F E σ B hT.base a' (b + a') (reS G.V' G.V') W₁ _ _ _ _ hV0' hW₁ M₁' hM₁' X.α (X.α / X.β)
    c.heckeα (isHecke_div c.heckeα c.heckeβ) c.resα (by rw [Nat.add_comm]; exact resEtaPow_div c.resα rβ)
  refine ⟨Y', G.V', W', ⟨hT.base, ⟨g.lt, g.even, g.kappa, g.eBig, g.aBig, hY', g.hV',
      (by show (reS G.W W').IsSkew σ B (b + 2 + a' - (G.p + G.q)) (G.p + G.q); rw [hq0]; exact hW'),
      ⟨g.hM.rat, g.hM.vac, g.hM.std, g.hM.haar, g.hM.dom⟩, ⟨g.hM'.rat, g.hM'.vac, g.hM'.std, g.hM'.haar, g.hM'.dom⟩⟩,
      c, hT.weil, hT.weil'⟩,
    ⟨G.p - 1, 0, V₁, reS G.V' G.V', W₁, M₁, M₁'⟩, H, H', ⟨rfl, hq0, rfl, ?_, hH, hH'⟩, om₁, om₁', ⟨hT.base, ?_, ?_, hom₁, hom₁'⟩⟩
  · show G.p - 1 + 1 = G.p
    omega
  · refine ⟨?_, ?_, fun w => ?_, ?_, ?_, ?_, hV0', ?_, hM₁, hM₁'⟩
    · show a' < b
      omega
    · obtain ⟨k, hk⟩ := g.even
      exact ⟨k - 1, by omega⟩
    · have := g.kappa w
      push_cast at this ⊢
      omega
    · show 2 * (G.p - 1 + 0) + 1 < (b - a') / 2
      omega
    · show 2 * (G.p - 1 + 0) + 1 < a'
      omega
    · show V₁.IsHerm σ B (b - (G.p - 1)) (G.p - 1)
      rw [show b - (G.p - 1) = b + 2 - G.p - 1 by omega]
      exact hV₁
    · show W₁.IsSkew σ B (b + a' - (G.p - 1 + 0)) (G.p - 1 + 0)
      rw [show b + a' - (G.p - 1 + 0) = b + 2 + a' - (G.p + 0) - 1 by omega,
        show G.p - 1 + 0 = G.p + 0 - 1 by omega]
      exact hW₁
  · exact ⟨c.heckeα, c.heckeβ, c.resα, rβ, c.expα, c.expβ, c.disj, c.sub, c.ram, c.unrα, c.unrβ, c.good⟩

theorem towerCodimensionTwo_of (hP : PlaneEx) (hM : ModelEx) (hW : WeilEx) : PositivityTheory.ThKEnd.TowerCodimensionTwo := by
  intro F E _ _ _ _ _ σ B b a' G X om om' hT hp
  have g := hT.geo
  have c := hT.chars
  have hb := g.aBig
  have hl := g.lt
  have he := g.eBig
  obtain ⟨Y', V₁, H, hY', hV₁, hH⟩ := hP.1 F E σ B hT.base (b + 2) b rfl (by omega) G.V (b + 2 - G.p) G.p
    (by omega) hp g.hV 0 (b + 1) (by omega) (by omega)
  obtain ⟨W', W₁, H', hW', hW₁, hH'⟩ := hP.2 F E σ B hT.base (b + 2 + a') (b + a') (by omega) (by omega) G.W
    (b + 2 + a' - (G.p + G.q)) (G.p + G.q) (by omega) (by omega) g.hW 0 (b + 1) (by omega) (by omega)
  have hV0' : (reS G.V' G.V').IsHerm σ B G.q (a' - G.q) := g.hV'
  obtain ⟨M₁, hM₁⟩ := hM F E σ B hT.base b (b + a') V₁ W₁ _ _ _ _ hV₁ hW₁
  obtain ⟨M₁', hM₁'⟩ := hM F E σ B hT.base a' (b + a') (reS G.V' G.V') W₁ _ _ _ _ hV0' hW₁
  have rβ : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range X.β b := resEtaPow_of_add_two c.resβ
  obtain ⟨om₁, hom₁⟩ := hW F E σ B hT.base b (b + a') V₁ W₁ _ _ _ _ hV₁ hW₁ M₁ hM₁ X.β (X.β / X.α)
    c.heckeβ (isHecke_div c.heckeβ c.heckeα) rβ (resEtaPow_div rβ c.resα)
  obtain ⟨om₁', hom₁'⟩ := hW F E σ B hT.base a' (b + a') (reS G.V' G.V') W₁ _ _ _ _ hV0' hW₁ M₁' hM₁' X.α (X.α / X.β)
    c.heckeα (isHecke_div c.heckeα c.heckeβ) c.resα (by rw [Nat.add_comm]; exact resEtaPow_div c.resα rβ)
  refine ⟨Y', G.V', W', ⟨hT.base, ⟨g.lt, g.even, g.kappa, g.eBig, g.aBig, hY', g.hV', hW',
      ⟨g.hM.rat, g.hM.vac, g.hM.std, g.hM.haar, g.hM.dom⟩, ⟨g.hM'.rat, g.hM'.vac, g.hM'.std, g.hM'.haar, g.hM'.dom⟩⟩,
      c, hT.weil, hT.weil'⟩,
    ⟨G.p - 1, G.q, V₁, reS G.V' G.V', W₁, M₁, M₁'⟩, H, H', ⟨rfl, rfl, ?_, hH, hH'⟩, om₁, om₁', ⟨hT.base, ?_, ?_, hom₁, hom₁'⟩⟩
  · show G.p - 1 + 1 = G.p
    omega
  · refine ⟨?_, ?_, fun w => ?_, ?_, ?_, ?_, hV0', ?_, hM₁, hM₁'⟩
    · show a' < b
      omega
    · obtain ⟨k, hk⟩ := g.even
      exact ⟨k - 1, by omega⟩
    · have := g.kappa w
      push_cast at this ⊢
      omega
    · show 2 * (G.p - 1 + G.q) + 1 < (b - a') / 2
      omega
    · show 2 * (G.p - 1 + G.q) + 1 < a'
      omega
    · show V₁.IsHerm σ B (b - (G.p - 1)) (G.p - 1)
      rw [show b - (G.p - 1) = b + 2 - G.p - 1 by omega]
      exact hV₁
    · show W₁.IsSkew σ B (b + a' - (G.p - 1 + G.q)) (G.p - 1 + G.q)
      rw [show b + a' - (G.p - 1 + G.q) = b + 2 + a' - (G.p + G.q) - 1 by omega,
        show G.p - 1 + G.q = G.p + G.q - 1 by omega]
      exact hW₁
  · exact ⟨c.heckeα, c.heckeβ, c.resα, rβ, c.expα, c.expβ, c.disj, c.sub, c.ram, c.unrα, c.unrβ, c.good⟩

end PositivityTheory.ThKG.Tow

end
end

