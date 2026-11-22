import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0114
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
import Formalism.LocalToGlobal.HermitianForms.Bundle0002
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0008
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeInfIsotropicEqSumFractionalIdealSmul
section
noncomputable section

open NumberField

namespace GlobalTheory.RowLatAssembly

open Formalism.MainNotions.S

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ} {T : E}

lemma Xa_le_X (F : FlagG S r T) (j : ℕ) : F.Xa j ≤ F.X := by
  unfold FlagG.Xa FlagG.X
  exact Submodule.span_mono (Set.image_subset_range _ _)

lemma X_eq_Xa (F : FlagG S r T) : F.X = F.Xa r := by
  unfold FlagG.Xa FlagG.X
  congr 1
  ext v
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, i.isLt, rfl⟩
  · rintro ⟨i, -, rfl⟩
    exact ⟨i, rfl⟩

lemma e_mem (F : FlagG S r T) (a : Fin r) : F.e a ∈ F.Xa (a.val + 1) := by
  unfold FlagG.Xa
  exact Submodule.subset_span ⟨a, Nat.lt_succ_self _, rfl⟩

private lemma coefX_linearCombination_eq (F : FlagG S r T) (l : Fin r →₀ E) (a : Fin r) :
    F.coefX (Finsupp.linearCombination E F.e l) a = l a := by
  have hmem : Finsupp.linearCombination E F.e l ∈ Submodule.span E (Set.range F.e) := by
    rw [← Finsupp.range_linearCombination]
    exact LinearMap.mem_range_self _ l
  unfold FlagG.coefX
  rw [dif_pos hmem, F.e_indep.repr_eq (l := l) rfl]

private lemma exists_linearCombination_eq_of_mem_flagX (F : FlagG S r T) {y : S.V} (hy : y ∈ F.X) :
    ∃ l : Fin r →₀ E, Finsupp.linearCombination E F.e l = y := by
  unfold FlagG.X at hy
  rw [← Finsupp.range_linearCombination] at hy
  exact LinearMap.mem_range.mp hy

lemma coefX_add (F : FlagG S r T) (a : Fin r) {x y : S.V} (hx : x ∈ F.X) (hy : y ∈ F.X) :
    F.coefX (x + y) a = F.coefX x a + F.coefX y a := by
  obtain ⟨l, rfl⟩ := exists_linearCombination_eq_of_mem_flagX F hx
  obtain ⟨m, rfl⟩ := exists_linearCombination_eq_of_mem_flagX F hy
  rw [← map_add, coefX_linearCombination_eq, coefX_linearCombination_eq, coefX_linearCombination_eq, Finsupp.add_apply]

lemma coefX_smul (F : FlagG S r T) (a : Fin r) (c : E) {x : S.V} (hx : x ∈ F.X) :
    F.coefX (c • x) a = c * F.coefX x a := by
  obtain ⟨l, rfl⟩ := exists_linearCombination_eq_of_mem_flagX F hx
  rw [← map_smul, coefX_linearCombination_eq, coefX_linearCombination_eq, Finsupp.smul_apply, smul_eq_mul]

lemma coefX_e (F : FlagG S r T) (i a : Fin r) :
    F.coefX (F.e i) a = if i = a then 1 else 0 := by
  have h : F.e i = Finsupp.linearCombination E F.e (Finsupp.single i 1) := by simp
  rw [h, coefX_linearCombination_eq, Finsupp.single_apply]

lemma mem_Xa_of_coefX_eq_zero (F : FlagG S r T) (a : Fin r) {y : S.V} (hy : y ∈ F.Xa (a.val + 1))
    (h0 : F.coefX y a = 0) : y ∈ F.Xa a.val := by
  unfold FlagG.Xa at hy ⊢
  obtain ⟨l, hl, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination (R := E)).mp hy
  rw [coefX_linearCombination_eq] at h0
  refine (Finsupp.mem_span_image_iff_linearCombination (R := E)).mpr ⟨l, ?_, rfl⟩
  rw [Finsupp.mem_supported'] at hl ⊢
  intro i hi
  simp only [Set.mem_ofPred_eq, not_lt] at hi
  rcases lt_or_eq_of_le hi with h | h
  · exact hl i (by simp only [Set.mem_ofPred_eq]; omega)
  · have hia : i = a := Fin.ext h.symm
    rw [hia]
    exact h0

lemma sub_smul_mem (F : FlagG S r T) (a : Fin r) {y w : S.V} (hy : y ∈ F.Xa (a.val + 1))
    (hw : w ∈ F.Xa (a.val + 1)) (hw1 : F.coefX w a = 1) :
    y - F.coefX y a • w ∈ F.Xa a.val := by
  have hyX := Xa_le_X F _ hy
  have hwX := Xa_le_X F _ hw
  apply mem_Xa_of_coefX_eq_zero F a (Submodule.sub_mem _ hy (Submodule.smul_mem _ _ hw))
  rw [sub_eq_add_neg, ← neg_smul, coefX_add F a hyX (Submodule.smul_mem _ _ hwX),
    coefX_smul F a _ hwX, hw1]
  ring

lemma exists_section (F : FlagG S r T) (Λ : Submodule (𝓞 E) S.V)
    (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hJ : J ≠ 0) (a : Fin r)
    (h3 : ∀ t : E, t ∈ J → ∃ x ∈ Λ, x ∈ F.Xa (a.val + 1) ∧ F.coefX x a = t) :
    ∃ w ∈ F.Xa (a.val + 1), F.coefX w a = 1 ∧ ∀ t ∈ J, t • w ∈ Λ := by

  have key : ∀ s ∈ J * J⁻¹, ∃ w ∈ F.Xa (a.val + 1), F.coefX w a = s ∧ ∀ t ∈ J, t • w ∈ Λ := by
    intro s hs
    refine FractionalIdeal.mul_induction_on hs ?_ ?_
    · intro i hi j hj
      obtain ⟨x, hxΛ, hxX, hxc⟩ := h3 i hi
      refine ⟨j • x, Submodule.smul_mem _ j hxX, ?_, ?_⟩
      · rw [coefX_smul F a j (Xa_le_X F _ hxX), hxc, mul_comm]
      · intro t ht
        have htj : t * j ∈ J * J⁻¹ := FractionalIdeal.mul_mem_mul ht hj
        rw [mul_inv_cancel₀ hJ, FractionalIdeal.mem_one_iff] at htj
        obtain ⟨o, ho⟩ := htj
        rw [smul_smul, ← ho, algebraMap_smul]
        exact Λ.smul_mem o hxΛ
    · rintro s₁ s₂ ⟨w₁, hw₁, hc₁, hΛ₁⟩ ⟨w₂, hw₂, hc₂, hΛ₂⟩
      refine ⟨w₁ + w₂, Submodule.add_mem _ hw₁ hw₂, ?_, ?_⟩
      · rw [coefX_add F a (Xa_le_X F _ hw₁) (Xa_le_X F _ hw₂), hc₁, hc₂]
      · intro t ht
        rw [smul_add]
        exact Λ.add_mem (hΛ₁ t ht) (hΛ₂ t ht)
  have h1 : (1 : E) ∈ J * J⁻¹ := by
    rw [mul_inv_cancel₀ hJ, FractionalIdeal.mem_one_iff]
    exact ⟨1, map_one _⟩
  exact key 1 h1

theorem xLam_eq_span : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) (r : ℕ) (T : E) (G : Formalism.MainNotions.S.Lat.LFlag S r T) (Λ : Submodule (𝓞 E) S.V) (J : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E), (∀ a, J a ≠ 0) → (∀ (a : Fin r) (x : S.V), x ∈ Λ → x ∈ G.fl.Xa (a.val + 1) → G.fl.coefX x a ∈ J a) → (∀ (a : Fin r) (t : E), t ∈ J a → ∃ x ∈ Λ, x ∈ G.fl.Xa (a.val + 1) ∧ G.fl.coefX x a = t) → ∃ e' : Fin r → S.V, (∀ a, e' a - G.fl.e a ∈ G.fl.Xa a.val) ∧ Formalism.MainNotions.S.Lat.XLam Λ G = Submodule.span (𝓞 E) {y | ∃ (a : Fin r) (x : E), x ∈ J a ∧ y = x • e' a} := by
  intro E _ _ _ S r T G Λ J hJ h2 h3
  have hsec : ∀ a : Fin r, ∃ w ∈ G.fl.Xa (a.val + 1), G.fl.coefX w a = 1 ∧ ∀ t ∈ J a, t • w ∈ Λ :=
    fun a => exists_section G.fl Λ (J a) (hJ a) a (h3 a)
  choose e' he'X he'c he'Λ using hsec
  refine ⟨e', fun a => ?_, ?_⟩
  · have hea : G.fl.coefX (G.fl.e a) a = 1 := by rw [coefX_e, if_pos rfl]
    have h := sub_smul_mem G.fl a (he'X a) (e_mem G.fl a) hea
    rwa [he'c a, one_smul] at h
  · apply le_antisymm
    ·
      have step : ∀ j : ℕ, j ≤ r → ∀ v ∈ Λ, v ∈ G.fl.Xa j →
          v ∈ Submodule.span (𝓞 E) {y | ∃ (a : Fin r) (x : E), x ∈ J a ∧ y = x • e' a} := by
        intro j
        induction j with
        | zero =>
          intro _ v _ hv
          have hv0 : v = 0 := by
            unfold Formalism.MainNotions.S.FlagG.Xa at hv
            simpa using hv
          rw [hv0]
          exact Submodule.zero_mem _
        | succ j ih =>
          intro hj v hvΛ hv
          obtain ⟨a, rfl⟩ : ∃ a : Fin r, a.val = j := ⟨⟨j, hj⟩, rfl⟩
          have hc : G.fl.coefX v a ∈ J a := h2 a v hvΛ hv
          have hrest : v - G.fl.coefX v a • e' a ∈ G.fl.Xa a.val :=
            sub_smul_mem G.fl a hv (he'X a) (he'c a)
          have hrestΛ : v - G.fl.coefX v a • e' a ∈ Λ := Λ.sub_mem hvΛ (he'Λ a _ hc)
          have hlow := ih (Nat.le_of_succ_le hj) _ hrestΛ hrest
          have htop : G.fl.coefX v a • e' a ∈
              Submodule.span (𝓞 E) {y | ∃ (a : Fin r) (x : E), x ∈ J a ∧ y = x • e' a} :=
            Submodule.subset_span ⟨a, _, hc, rfl⟩
          have hsum := Submodule.add_mem _ hlow htop
          rwa [sub_add_cancel] at hsum
      intro v hv
      obtain ⟨hvΛ, hvX⟩ : v ∈ Λ ∧ v ∈ G.fl.X := hv
      rw [X_eq_Xa] at hvX
      exact step r le_rfl v hvΛ hvX
    · rw [Submodule.span_le]
      rintro y ⟨a, x, hx, rfl⟩
      show x • e' a ∈ Λ ⊓ Formalism.MainNotions.S.Lat.toO S (Formalism.MainNotions.S.Lat.Xsp G)
      exact Submodule.mem_inf.mpr ⟨he'Λ a x hx, (G.fl.X).smul_mem x (Xa_le_X G.fl _ (he'X a))⟩

end GlobalTheory.RowLatAssembly
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalFrameIdempotentFactorCases
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem not_forall_loc_eq_natCast_smul (v : HeightOneSpectrum (𝓞 F))
    (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
    (hdiag : ∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a))
    (g : ℕ) (hg : (g : 𝓞 F) ∈ v.asIdeal) (L : Submodule (𝓞 E) (Fin n → E)) (hL : IsLat L) (hn : 0 < n) :
    ¬ ∀ y ∈ loc v L, ∃ z ∈ loc v L, y = (g : E ⊗[F] v.adicCompletion F) • z := by
  classical
  intro h
  have hs := split_integral_local F E v sp hdiag
  have hint : ∀ r ∈ intV E v, (sp r).1 ∈ v.adicCompletionIntegers F := fun r hr => ((hs r).1 hr).1
  have hOE : ∀ c : 𝓞 E, inclE (F := F) (v.adicCompletion F) (c : E) ∈ intV E v := by
    intro c
    have hc : ((c : E) ⊗ₜ[F] (1 : v.adicCompletion F)) ∈ PI.SplitIntLoc.tensInt (v.adicCompletion F)
        (PI.SplitIntLoc.intOE E) (v.adicCompletionIntegers F).toSubring :=
      Subring.subset_closure (Or.inl ⟨⟨(c : E), c, rfl⟩, rfl⟩)
    exact hc
  have hv : Valued.v ((g : v.adicCompletion F)) < 1 := by
    have h1 : v.intValuation (g : 𝓞 F) < 1 := (v.intValuation_lt_one_iff_mem _).2 hg
    have h2 : ((g : v.adicCompletion F)) = algebraMap (𝓞 F) (v.adicCompletion F) (g : 𝓞 F) :=
      (map_natCast _ g).symm
    rw [h2]
    refine lt_of_eq_of_lt (v.valuedAdicCompletion_eq_valuation (g : 𝓞 F)) ?_
    rw [v.valuation_of_algebraMap]
    exact h1
  obtain ⟨hfin, hspan⟩ := hL
  obtain ⟨G, hG⟩ := Module.Finite.iff_fg.1 hfin
  have hgen : ∀ x ∈ L, (fun i => inclE (F := F) (v.adicCompletion F) (x i)) ∈ loc v L :=
    fun x hx => Submodule.subset_span ⟨x, hx, rfl⟩
  set M : Submodule (v.adicCompletionIntegers F) (v.adicCompletion F) := Submodule.span _
    (Set.range fun p : G × Fin n => (sp (inclE (F := F) (v.adicCompletion F) ((p.1 : Fin n → E) p.2))).1) with hMdef
  have hMx : ∀ x ∈ L, ∀ i, (sp (inclE (F := F) (v.adicCompletion F) (x i))).1 ∈ M := by
    intro x hx i
    rw [← hG] at hx
    induction hx using Submodule.span_induction with
    | mem s hsG => exact Submodule.subset_span ⟨(⟨s, hsG⟩, i), rfl⟩
    | zero => simp
    | add a b _ _ ha hb => simpa using M.add_mem ha hb
    | smul c a _ ha =>
      have hc := hint _ (hOE c)
      have e : (sp (inclE (F := F) (v.adicCompletion F) ((c • a) i))).1 =
          (⟨_, hc⟩ : v.adicCompletionIntegers F) • (sp (inclE (F := F) (v.adicCompletion F) (a i))).1 := by
        rw [Pi.smul_apply, Algebra.smul_def, map_mul, map_mul, Prod.fst_mul, Algebra.smul_def]
        rfl
      rw [e]
      exact M.smul_mem _ ha
  have hM : ∀ y ∈ loc v L, ∀ i, (sp (y i)).1 ∈ M := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x, hxL, rfl⟩ := hx
      exact hMx x hxL
    | zero => intro i; simp
    | add a b _ _ ha hb => intro i; simpa using M.add_mem (ha i) (hb i)
    | smul r a _ ha =>
      intro i
      have hr := hint _ r.2
      have e : (sp ((r • a) i)).1 = (⟨_, hr⟩ : v.adicCompletionIntegers F) • (sp (a i)).1 := by
        rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, map_mul, Prod.fst_mul, Algebra.smul_def]
        rfl
      rw [e]
      exact M.smul_mem _ (ha i)
  have hle : M ≤ Ideal.span {((g : v.adicCompletionIntegers F))} • M := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨⟨s, hsG⟩, i⟩, rfl⟩
    have hsL : s ∈ L := hG ▸ Submodule.subset_span hsG
    obtain ⟨z, hz, hyz⟩ := h _ (hgen s hsL)
    have e : (sp (inclE (F := F) (v.adicCompletion F) (s i))).1 =
        (g : v.adicCompletionIntegers F) • (sp (z i)).1 := by
      have hi : inclE (F := F) (v.adicCompletion F) (s i) = ((g : E ⊗[F] v.adicCompletion F) • z) i :=
        congrFun hyz i
      rw [hi, Pi.smul_apply, smul_eq_mul, map_mul, map_natCast, Prod.fst_mul, Algebra.smul_def]
      simp
    change (sp (inclE (F := F) (v.adicCompletion F) (s i))).1 ∈
      ((Ideal.span {((g : v.adicCompletionIntegers F))} • M : Submodule _ _) : Set (v.adicCompletion F))
    rw [SetLike.mem_coe, e]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) (hM z hz i)
  have hjac : Ideal.span {((g : v.adicCompletionIntegers F))} ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, Ideal.span_le, Set.singleton_subset_iff,
      SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hunit
    obtain ⟨b, hb⟩ := hunit.exists_left_inv
    have hb' : (b : v.adicCompletion F) * (g : v.adicCompletion F) = 1 := by
      have := congrArg Subtype.val hb
      simpa using this
    have hbv : Valued.v (b : v.adicCompletion F) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 F) (K := F) (v := v)).1 b.2
    have hlt : Valued.v ((b : v.adicCompletion F) * (g : v.adicCompletion F)) < 1 := by
      rw [map_mul]
      exact (mul_le_of_le_one_left' hbv).trans_lt hv
    rw [hb', map_one] at hlt
    exact lt_irrefl _ hlt
  have hne : ∃ s ∈ G, ∃ i, s i ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_and, ne_eq, not_not] at hcon
    have hL0 : L = ⊥ := by
      rw [← hG, Submodule.span_eq_bot]
      intro s hs
      funext i
      exact hcon s hs i
    have h1 : (fun _ : Fin n => (1 : E)) ∈ Submodule.span E (L : Set (Fin n → E)) := hspan ▸ Submodule.mem_top
    rw [hL0, Submodule.bot_coe, Submodule.span_zero_singleton, Submodule.mem_bot] at h1
    exact one_ne_zero (congrFun h1 ⟨0, hn⟩)
  obtain ⟨s, hsG, i, hsi⟩ := hne
  have hu : IsUnit (sp (inclE (F := F) (v.adicCompletion F) (s i))) :=
    ((isUnit_iff_ne_zero.2 hsi).map (inclE (F := F) (v.adicCompletion F))).map sp
  have ha : (sp (inclE (F := F) (v.adicCompletion F) (s i))).1 ≠ 0 :=
    (hu.map (RingHom.fst (v.adicCompletion F) (v.adicCompletion F))).ne_zero
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ M (Submodule.fg_span (Set.finite_range _)) hle hjac
  have hmem : (sp (inclE (F := F) (v.adicCompletion F) (s i))).1 ∈ M := Submodule.subset_span ⟨(⟨s, hsG⟩, i), rfl⟩
  rw [hbot, Submodule.mem_bot] at hmem
  exact ha hmem

end

theorem local_idempotent_cases :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (v : HeightOneSpectrum (𝓞 F)) (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, sp (sigR σ (v.adicCompletion F) x) = swapR _ (sp x)) → (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) → ∀ (g : ℕ), (g : 𝓞 F) ∈ v.asIdeal → ∀ (L : Submodule (𝓞 E) (Fin n → E)), IsLat L → 0 < n → ∀ e : E ⊗[F] v.adicCompletion F, e * e = e → e * sigR σ (v.adicCompletion F) e = 0 → (∀ y ∈ loc v L, ∃ z ∈ loc v L, (1 - e - sigR σ (v.adicCompletion F) e) • y = (g : E ⊗[F] v.adicCompletion F) • z) → sp e = (1, 0) ∨ sp e = (0, 1) := by
  intro F E _ _ _ _ _ σ n v sp hsw hdiag g hg L hL hn e he heo hfull
  have hse : sp (sigR σ (v.adicCompletion F) e) = ((sp e).2, (sp e).1) := by
    rw [hsw]
    rfl
  have hidem : sp e * sp e = sp e := by rw [← map_mul, he]
  have horth : sp e * ((sp e).2, (sp e).1) = 0 := by rw [← hse, ← map_mul, heo, map_zero]
  have ha : (sp e).1 * (sp e).1 = (sp e).1 := congrArg Prod.fst hidem
  have hb : (sp e).2 * (sp e).2 = (sp e).2 := congrArg Prod.snd hidem
  have hab : (sp e).1 * (sp e).2 = 0 := congrArg Prod.fst horth
  have ha' : (sp e).1 = 0 ∨ (sp e).1 = 1 := by
    have h0 : (sp e).1 * ((sp e).1 - 1) = 0 := by rw [mul_sub, mul_one, ha, sub_self]
    rcases mul_eq_zero.1 h0 with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.1 h)
  have hb' : (sp e).2 = 0 ∨ (sp e).2 = 1 := by
    have h0 : (sp e).2 * ((sp e).2 - 1) = 0 := by rw [mul_sub, mul_one, hb, sub_self]
    rcases mul_eq_zero.1 h0 with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.1 h)
  rcases ha' with ha0 | ha1 <;> rcases hb' with hb0 | hb1
  · exfalso
    have he0 : e = 0 := sp.injective (by rw [map_zero]; exact Prod.ext ha0 hb0)
    apply not_forall_loc_eq_natCast_smul v sp hdiag g hg L hL hn
    intro y hy
    obtain ⟨z, hz, hyz⟩ := hfull y hy
    refine ⟨z, hz, ?_⟩
    rw [he0, map_zero, sub_zero, sub_zero, one_smul] at hyz
    exact hyz
  · exact Or.inr (Prod.ext ha0 hb1)
  · exact Or.inl (Prod.ext ha1 hb0)
  · exfalso
    rw [ha1, hb1, one_mul] at hab
    exact one_ne_zero hab

end GlobalTheory.St.G
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalSpanOfLatticeAtPlaceEqForAlmostAllPlaces
section
noncomputable section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G

section Global

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem exists_zsmul_mem_of_span (M : Submodule (𝓞 E) (Fin n → E))
    (hM : Submodule.span E (M : Set (Fin n → E)) = ⊤) (x : Fin n → E) :
    ∃ c : ℤ, c ≠ 0 ∧ c • x ∈ M := by
  first
  | exact @_root_.GlobalTheory.IntSmulIsIntegral.exists_int_smul_mem
  | exact _root_.GlobalTheory.IntSmulIsIntegral.exists_int_smul_mem
  | (apply _root_.GlobalTheory.IntSmulIsIntegral.exists_int_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntSmulIsIntegral.exists_int_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntSmulIsIntegral.exists_int_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntSmulIsIntegral.exists_int_smul_mem ..)

theorem exists_zsmul_le (L M : Submodule (𝓞 E) (Fin n → E)) (hL : Module.Finite (𝓞 E) L)
    (hM : Submodule.span E (M : Set (Fin n → E)) = ⊤) :
    ∃ c : ℤ, c ≠ 0 ∧ ∀ x ∈ L, c • x ∈ M := by
  obtain ⟨S, hS⟩ : L.FG := Module.Finite.iff_fg.mp hL
  have hfin : ∀ T : Finset (Fin n → E), ∃ c : ℤ, c ≠ 0 ∧ ∀ x ∈ T, c • x ∈ M := by
    classical
    intro T
    induction T using Finset.induction_on with
    | empty => exact ⟨1, one_ne_zero, by simp⟩
    | insert a T _ ih =>
      obtain ⟨c, hc, hcT⟩ := ih
      obtain ⟨d, hd, hda⟩ := exists_zsmul_mem_of_span M hM a
      refine ⟨d * c, mul_ne_zero hd hc, fun x hx => ?_⟩
      rcases Finset.mem_insert.mp hx with rfl | hx
      · rw [mul_comm, mul_smul]
        exact zsmul_mem hda c
      · rw [mul_smul]
        exact zsmul_mem (hcT x hx) d
  obtain ⟨c, hc, hcS⟩ := hfin S
  refine ⟨c, hc, fun x hx => ?_⟩
  rw [← hS] at hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact hcS x hx
  | zero => simp
  | add a b _ _ ha hb =>
    rw [smul_add]
    exact M.add_mem ha hb
  | smul a y _ hy =>
    rw [smul_comm]
    exact M.smul_mem a hy

end Global

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem int_inv_mem_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 F)) (c : ℤ)
    (hv : (c : 𝓞 F) ∉ v.asIdeal) :
    (algebraMap F (v.adicCompletion F) (c : F))⁻¹ ∈ v.adicCompletionIntegers F := by
  have h1 : Valued.v (algebraMap F (v.adicCompletion F) (c : F)) = 1 := by
    have h2 : (c : F) = algebraMap (𝓞 F) F (c : 𝓞 F) := by simp
    have h3 : Valued.v (algebraMap F (v.adicCompletion F) (c : F)) = v.valuation F (c : F) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (c : F)
    rw [h3, h2, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.mpr hv
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h1, inv_one]

theorem loc_le_of_zsmul (v : HeightOneSpectrum (𝓞 F)) (L M : Submodule (𝓞 E) (Fin n → E)) (c : ℤ)
    (hc : c ≠ 0) (hv : (c : 𝓞 F) ∉ v.asIdeal) (h : ∀ x ∈ L, c • x ∈ M) : loc v L ≤ loc v M := by
  have hu := int_inv_mem_adicCompletionIntegers v c hv
  set u : v.adicCompletion F := (algebraMap F (v.adicCompletion F) (c : F))⁻¹ with hudef
  have hne : algebraMap F (v.adicCompletion F) (c : F) ≠ 0 := by
    rw [Ne, map_eq_zero]
    exact_mod_cast hc
  have hs : (1 : E) ⊗ₜ[F] u ∈ intV E v :=
    Subring.subset_closure (Or.inr ⟨⟨u, hu⟩, rfl⟩)
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨x, hx, rfl⟩
  have hgen : (fun i => inclE (F := F) (v.adicCompletion F) ((c • x) i)) ∈ loc (F := F) v M :=
    Submodule.subset_span ⟨c • x, h x hx, rfl⟩
  have hm := (loc (F := F) v M).smul_mem ⟨_, hs⟩ hgen
  suffices heq : (fun i => inclE (F := F) (v.adicCompletion F) (x i)) =
      (⟨(1 : E) ⊗ₜ[F] u, hs⟩ : intV E v) • (fun i => inclE (F := F) (v.adicCompletion F) ((c • x) i)) by
    show (fun i => inclE (F := F) (v.adicCompletion F) (x i)) ∈ loc (F := F) v M
    rw [heq]
    exact hm
  funext i
  have hci : (c • x) i = (c : F) • x i := by
    simp [Int.cast_smul_eq_zsmul]
  have hone : (c : F) • u = 1 := by
    rw [Algebra.smul_def, hudef, mul_inv_cancel₀ hne]
  show (x i) ⊗ₜ[F] (1 : v.adicCompletion F) = ((1 : E) ⊗ₜ[F] u) * ((c • x) i ⊗ₜ[F] (1 : v.adicCompletion F))
  rw [Algebra.TensorProduct.tmul_mul_tmul, hci, one_mul, mul_one, TensorProduct.smul_tmul, hone]

end Local

theorem loc_eq_almost_all : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n : ℕ) (L M : Submodule (𝓞 E) (Fin n → E)), IsLat L → IsLat M →
    {v : HeightOneSpectrum (𝓞 F) | loc v L ≠ loc v M}.Finite := by
  intro F E _ _ _ _ _ n L M hL hM
  obtain ⟨c, hc, hcLM⟩ := exists_zsmul_le L M hL.1 hM.2
  obtain ⟨d, hd, hdML⟩ := exists_zsmul_le M L hM.1 hL.2
  have hcd : (((c * d : ℤ) : 𝓞 F)) ≠ 0 := by
    exact_mod_cast mul_ne_zero hc hd
  have hI : Ideal.span {(((c * d : ℤ) : 𝓞 F))} ≠ 0 := by
    simpa [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using hcd
  refine (Ideal.finite_factors hI).subset fun v hv => ?_
  show v.asIdeal ∣ _
  rw [Ideal.dvd_span_singleton]
  by_contra hn
  have hcv : (c : 𝓞 F) ∉ v.asIdeal := fun h => hn (by
    rw [Int.cast_mul]
    exact Ideal.mul_mem_right _ _ h)
  have hdv : (d : 𝓞 F) ∉ v.asIdeal := fun h => hn (by
    rw [Int.cast_mul]
    exact Ideal.mul_mem_left _ _ h)
  exact hv (le_antisymm (loc_le_of_zsmul v L M c hc hcv hcLM) (loc_le_of_zsmul v M L d hd hdv hdML))

end GlobalTheory.St.G

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StepLevelTLat
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in

theorem _root_.GlobalTheory.St.G.stepLevel_tLat : ∀ (F E : Type) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] (n : ℕ) (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)
    (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : _root_.Formalism.L2.Forms.StepLevel F E σ J T f bad),
    _root_.GlobalTheory.St.G.TLat σ J T f S.Lb := by
  intro F E _ _ _ _ _ n σ J T f bad S
  refine ⟨⟨S.Lb_fin, S.Lb_span⟩, S.Lb_int, S.Lb_dual, S.Lb_index, fun v hv => ?_⟩
  obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp (S.fT_ne v hv)
  exact ⟨x, x.2, fun hmem => hx (S.fT_L v hv x hmem)⟩

end GlobalTheory.St.G
end

