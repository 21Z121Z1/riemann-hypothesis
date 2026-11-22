import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0026
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ConclusionAbsPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0119

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsTotallyRealPrimitiveElementPadicFiniteExt
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W

section
open Polynomial IntermediateField Filter Topology

private theorem totally_real_of_sign_changes (n : ℕ) (g : ℚ[X]) (hg : g.Monic) (hd : g.natDegree = n)
    (hs : ∀ j < n, aeval ((j : ℝ) - 1 / 2) g * aeval ((j : ℝ) + 1 / 2) g < 0) :
    ∀ z : ℂ, aeval z g = 0 → z.im = 0 := by
  have hroot : ∀ j : Fin n, ∃ r : ℝ, ((j : ℕ) : ℝ) - 1 / 2 < r ∧ r < ((j : ℕ) : ℝ) + 1 / 2 ∧
      aeval r g = 0 := by
    intro j
    have hc : ContinuousOn (fun x : ℝ => aeval x g)
        (Set.Icc (((j : ℕ) : ℝ) - 1 / 2) (((j : ℕ) : ℝ) + 1 / 2)) :=
      (Polynomial.continuous_aeval g).continuousOn
    have hle : ((j : ℕ) : ℝ) - 1 / 2 ≤ ((j : ℕ) : ℝ) + 1 / 2 := by linarith
    rcases mul_neg_iff.1 (hs j j.2) with h | h
    · obtain ⟨r, hr, hr0⟩ := intermediate_value_Ioo' hle hc ⟨h.2, h.1⟩
      exact ⟨r, hr.1, hr.2, hr0⟩
    · obtain ⟨r, hr, hr0⟩ := intermediate_value_Ioo hle hc ⟨h.1, h.2⟩
      exact ⟨r, hr.1, hr.2, hr0⟩
  choose r hr1 hr2 hr0 using hroot
  have hinj : Function.Injective fun j : Fin n => ((r j : ℝ) : ℂ) := by
    intro i j hij
    have hij' : r i = r j := Complex.ofReal_injective hij
    have h1 : ((i : ℕ) : ℝ) < (j : ℕ) + 1 := by linarith [hr1 i, hr2 j]
    have h2 : ((j : ℕ) : ℝ) < (i : ℕ) + 1 := by linarith [hr1 j, hr2 i]
    have h1' : (i : ℕ) < (j : ℕ) + 1 := by exact_mod_cast h1
    have h2' : (j : ℕ) < (i : ℕ) + 1 := by exact_mod_cast h2
    exact Fin.ext (by omega)
  intro z hz
  by_contra hzim
  classical
  have hne : g.map (algebraMap ℚ ℂ) ≠ 0 := (hg.map _).ne_zero
  have hnot : z ∉ (Finset.univ : Finset (Fin n)).image fun j : Fin n => ((r j : ℝ) : ℂ) := by
    intro hmem
    obtain ⟨j, -, hj⟩ := Finset.mem_image.1 hmem
    exact hzim (by rw [← hj]; simp)
  have hcard := Polynomial.card_le_degree_of_subset_roots (p := g.map (algebraMap ℚ ℂ))
    (Z := insert z ((Finset.univ : Finset (Fin n)).image fun j : Fin n => ((r j : ℝ) : ℂ))) (by
      intro x hx
      rw [Polynomial.mem_roots hne, Polynomial.IsRoot.def, Polynomial.eval_map_algebraMap]
      rcases Finset.mem_insert.1 (Finset.mem_def.2 hx) with rfl | hx
      · exact hz
      · obtain ⟨j, -, hj⟩ := Finset.mem_image.1 hx
        rw [← hj]
        have := Polynomial.aeval_algebraMap_apply ℂ (r j) g
        rw [hr0 j, map_zero] at this
        exact this)
  rw [Finset.card_insert_of_notMem hnot, Finset.card_image_of_injective _ hinj,
    Polynomial.natDegree_map, hd] at hcard
  simp at hcard

private theorem sign_change_between_integers (n j : ℕ) (hj : j < n) :
    aeval ((j : ℝ) - 1 / 2) (∏ i ∈ Finset.range n, (X - C (i : ℚ)) : ℚ[X]) *
      aeval ((j : ℝ) + 1 / 2) (∏ i ∈ Finset.range n, (X - C (i : ℚ)) : ℚ[X]) < 0 := by
  rw [map_prod, map_prod, ← Finset.prod_mul_distrib,
    ← Finset.mul_prod_erase _ _ (Finset.mem_range.2 hj)]
  refine mul_neg_of_neg_of_pos ?_ (Finset.prod_pos fun i hi => ?_)
  · simp
  · have hij : i ≠ j := (Finset.mem_erase.1 hi).1
    simp only [map_sub, aeval_X, aeval_C, eq_ratCast, Rat.cast_natCast]
    rcases lt_or_gt_of_ne hij with h | h
    · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
      apply mul_pos <;> linarith
    · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
      apply mul_pos_of_neg_of_neg <;> linarith

private theorem approx_monic_totally_real_rational (l : ℕ) [Fact l.Prime] (f : ℚ_[l][X]) (hf : f.Monic)
    (ε : ℝ) (hε : ε > 0) :
    ∃ g : ℚ[X], g.Monic ∧ f.natDegree = g.natDegree ∧
      (∀ i, ‖(g.map (algebraMap ℚ ℚ_[l])).coeff i - f.coeff i‖ < ε) ∧
      ∀ z : ℂ, aeval z g = 0 → z.im = 0 := by
  obtain ⟨g₀, gmon, gdeg, gcoeff⟩ :=
    exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt
      (Padic.denseRange_ratCast l) hf hε
  set n := g₀.natDegree with hn
  set h : ℚ[X] := ∏ i ∈ Finset.range n, (X - C (i : ℚ)) with hh
  have hmon : h.Monic := monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _
  have hdeg : h.natDegree = n := by
    rw [hh, natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C _]
    simp only [natDegree_X_sub_C]
    simp
  have hdlt : (g₀ - h).degree < h.degree := by
    have e : g₀.degree = h.degree := by
      rw [degree_eq_natDegree gmon.ne_zero, degree_eq_natDegree hmon.ne_zero, hdeg]
    rw [← e]
    exact degree_sub_lt e gmon.ne_zero (by rw [gmon.leadingCoeff, hmon.leadingCoeff])
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  let u : ℕ → ℚ := fun N => (1 + (l : ℚ) ^ N)⁻¹
  have huR : Tendsto (fun N => ((u N : ℚ) : ℝ)) atTop (𝓝 0) := by
    have : Tendsto (fun N : ℕ => 1 + (l : ℝ) ^ N) atTop atTop :=
      tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop_atTop_of_one_lt hl)
    have := this.inv_tendsto_atTop
    refine this.congr fun N => ?_
    simp [u]
  have huP : Tendsto (fun N => ((u N : ℚ) : ℚ_[l])) atTop (𝓝 1) := by
    have h1 : Tendsto (fun N : ℕ => (l : ℚ_[l]) ^ N) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one Padic.norm_p_lt_one
    have h2 := ((tendsto_const_nhds (x := (1 : ℚ_[l]))).add h1).inv₀ (by simp)
    simp only [add_zero, inv_one] at h2
    refine h2.congr fun N => ?_
    simp [u]
  have hG : ∀ N, (h + C (u N) * (g₀ - h)).Monic ∧ (h + C (u N) * (g₀ - h)).natDegree = n := by
    intro N
    have hlt : (C (u N) * (g₀ - h)).degree < h.degree := by
      rw [← smul_eq_C_mul]
      exact (degree_smul_le _ _).trans_lt hdlt
    exact ⟨hmon.add_of_left hlt, by rw [natDegree_add_eq_left_of_degree_lt hlt, hdeg]⟩
  have e1 : ∀ᶠ N in atTop, ∀ j ∈ Finset.range n,
      aeval ((j : ℝ) - 1 / 2) (h + C (u N) * (g₀ - h)) *
        aeval ((j : ℝ) + 1 / 2) (h + C (u N) * (g₀ - h)) < 0 := by
    rw [Filter.eventually_all_finset]
    intro j hj
    have hev : ∀ x : ℝ, Tendsto (fun N => aeval x (h + C (u N) * (g₀ - h))) atTop
        (𝓝 (aeval x h)) := by
      intro x
      have := (tendsto_const_nhds (x := aeval x h)).add (huR.mul_const (aeval x (g₀ - h)))
      simp only [zero_mul, add_zero] at this
      refine this.congr fun N => ?_
      simp only [map_add, map_mul, aeval_C, eq_ratCast]
    exact ((hev _).mul (hev _)).eventually
      (gt_mem_nhds (sign_change_between_integers n j (Finset.mem_range.1 hj)))
  have e2 : ∀ᶠ N in atTop, ∀ i ∈ Finset.range (n + 1),
      ‖((h + C (u N) * (g₀ - h)).map (algebraMap ℚ ℚ_[l])).coeff i - f.coeff i‖ < ε := by
    rw [Filter.eventually_all_finset]
    intro i _
    have hev : Tendsto (fun N => ((h + C (u N) * (g₀ - h)).map (algebraMap ℚ ℚ_[l])).coeff i)
        atTop (𝓝 ((g₀.map (algebraMap ℚ ℚ_[l])).coeff i)) := by
      have := (tendsto_const_nhds (x := ((h.coeff i : ℚ) : ℚ_[l]))).add
        (huP.mul_const (((g₀.coeff i : ℚ) : ℚ_[l]) - ((h.coeff i : ℚ) : ℚ_[l])))
      simp only [one_mul, add_sub_cancel] at this
      simp only [coeff_map, coeff_add, coeff_C_mul, coeff_sub, eq_ratCast]
      refine this.congr fun N => ?_
      push_cast
      ring
    exact ((hev.sub_const _).norm).eventually (gt_mem_nhds (gcoeff i))
  obtain ⟨N, hN1, hN2⟩ := (e1.and e2).exists
  refine ⟨h + C (u N) * (g₀ - h), (hG N).1, by rw [(hG N).2, gdeg], fun i => ?_,
    totally_real_of_sign_changes n _ (hG N).1 (hG N).2 fun j hj => hN1 j (Finset.mem_range.2 hj)⟩
  by_cases hi : i < n + 1
  · exact hN2 i (Finset.mem_range.2 hi)
  · rw [coeff_eq_zero_of_natDegree_lt (by rw [natDegree_map, (hG N).2]; omega),
      coeff_eq_zero_of_natDegree_lt (by rw [gdeg]; omega)]
    simpa using hε

private theorem krasner_totally_real_generator (l : ℕ) [Fact l.Prime] (α : PadicAlgCl l) :
    ∃ β : PadicAlgCl l, ∃ g : ℚ[X], g.Monic ∧ g.natDegree = (minpoly ℚ_[l] α).natDegree ∧
      aeval β g = 0 ∧ (∀ z : ℂ, aeval z g = 0 → z.im = 0) ∧ α ∈ ℚ_[l]⟮β⟯ := by
  have hint : ∀ z : PadicAlgCl l, IsIntegral ℚ_[l] z := fun z =>
    (Algebra.IsAlgebraic.isAlgebraic z).isIntegral
  have fmon : (minpoly ℚ_[l] α).Monic := minpoly.monic (hint α)
  have fa0 : (minpoly ℚ_[l] α).aeval α = 0 := minpoly.aeval _ _
  have hfin : ({x' | IsConjRoot ℚ_[l] α x' ∧ α ≠ x'} : Set (PadicAlgCl l)).Finite := by
    refine ((minpoly ℚ_[l] α).rootSet_finite (PadicAlgCl l)).subset fun x' hx' => ?_
    exact (isConjRoot_iff_mem_minpoly_rootSet (hint α)).1 hx'.1
  have hop : IsOpen (⋂ x' ∈ ({x' | IsConjRoot ℚ_[l] α x' ∧ α ≠ x'} : Set (PadicAlgCl l)),
      {y : PadicAlgCl l | ‖α - y‖ < ‖α - x'‖}) :=
    hfin.isOpen_biInter fun x' _ => isOpen_lt (by fun_prop) continuous_const
  have hmem : α ∈ (⋂ x' ∈ ({x' | IsConjRoot ℚ_[l] α x' ∧ α ≠ x'} : Set (PadicAlgCl l)),
      {y : PadicAlgCl l | ‖α - y‖ < ‖α - x'‖}) := by
    simp only [Set.mem_iInter, Set.mem_setOf_eq, sub_self, norm_zero, norm_pos_iff, sub_ne_zero]
    exact fun x' h => h.2
  obtain ⟨δ, δpos, hball⟩ := Metric.isOpen_iff.1 hop α hmem
  have hn : (minpoly ℚ_[l] α).natDegree ≠ 0 := (minpoly.natDegree_pos (hint α)).ne'
  have hε : (δ / (max ‖α‖ 1)) ^ (minpoly ℚ_[l] α).natDegree /
      ((minpoly ℚ_[l] α).natDegree + 1) > 0 := by positivity
  obtain ⟨g, gmon, gdeg, gcoeff, greal⟩ := approx_monic_totally_real_rational l _ fmon _ hε
  obtain ⟨β, hb, hab⟩ := exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt (L := PadicAlgCl l)
      hε fa0 fmon (gmon.map _) (gdeg ▸ (g.natDegree_map _)) gcoeff (IsAlgClosed.splits _)
  have hab : ‖α - β‖ < δ := by
    rw [← Real.rpow_natCast, ← mul_comm_div, div_self, one_mul,
        ← Real.rpow_mul (div_pos δpos (by positivity)).le, mul_inv_cancel₀] at hab
    · simpa [mul_assoc, div_mul_cancel₀ _ (by positivity : (max ‖α‖ 1) > 0).ne'] using hab
    · simp [hn]
    · positivity
  have hβU := hball
    (show β ∈ Metric.ball α δ by rw [Metric.mem_ball, dist_comm, dist_eq_norm]; exact hab)
  have hgβ : aeval β g = 0 := by
    rw [Polynomial.mem_aroots] at hb
    simpa [Polynomial.aeval_map_algebraMap] using hb.2
  refine ⟨β, g, gmon, gdeg.symm, hgβ, greal, ?_⟩
  refine IsKrasner.krasner (minpoly.irreducible (hint α)).separable (IsAlgClosed.splits _)
    (hint β) fun x' h1 h2 => ?_
  simp only [Set.mem_iInter, Set.mem_setOf_eq] at hβU
  exact hβU x' ⟨h1, h2⟩

private theorem exists_totally_real_generator (l : ℕ) [Fact l.Prime]
    (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K] :
    ∃ (β : PadicAlgCl l) (g : ℚ[X]), g.Monic ∧ aeval β g = 0 ∧
      (∀ z : ℂ, aeval z g = 0 → z.im = 0) ∧ ℚ_[l]⟮β⟯ = K := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ_[l] K
  have hKα : K = ℚ_[l]⟮(α : PadicAlgCl l)⟯ := by
    rw [← IntermediateField.lift_adjoin_simple, hα, IntermediateField.lift_top]
  obtain ⟨β, g, gmon, gdeg, hgβ, greal, hαβ⟩ := krasner_totally_real_generator l (α : PadicAlgCl l)
  refine ⟨β, g, gmon, hgβ, greal, ?_⟩
  have hint : ∀ z : PadicAlgCl l, IsIntegral ℚ_[l] z := fun z =>
    (Algebra.IsAlgebraic.isAlgebraic z).isIntegral
  rw [hKα]
  symm
  haveI : FiniteDimensional ℚ_[l] ℚ_[l]⟮β⟯ := IntermediateField.adjoin.finiteDimensional (hint β)
  refine IntermediateField.eq_of_le_of_finrank_le
    (IntermediateField.adjoin_simple_le_iff.2 hαβ) ?_
  rw [IntermediateField.adjoin.finrank (hint β), IntermediateField.adjoin.finrank (hint _), ← gdeg]
  have hg0 : g.map (algebraMap ℚ ℚ_[l]) ≠ 0 := (gmon.map _).ne_zero
  have hdvd : minpoly ℚ_[l] β ∣ g.map (algebraMap ℚ ℚ_[l]) :=
    minpoly.dvd _ _ (by rw [Polynomial.aeval_map_algebraMap]; exact hgβ)
  calc (minpoly ℚ_[l] β).natDegree ≤ (g.map (algebraMap ℚ ℚ_[l])).natDegree :=
        Polynomial.natDegree_le_of_dvd hdvd hg0
    _ = g.natDegree := g.natDegree_map _

end

theorem UpperTheory.exists_totally_real_primitive_element_padic_finite_ext :
    ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l), ∃ (β : Om l) (g : Polynomial ℚ), g.Monic ∧ Polynomial.aeval β g = 0 ∧ (∀ z : ℂ, Polynomial.aeval z g = 0 → z.im = 0) ∧ IntermediateField.adjoin ℚ_[l] {β} = K.1 := by
  intro l _ K
  haveI := K.2
  exact exists_totally_real_generator l K.1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteEmb
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W

private theorem finite_emb {F : Type} [Field F] [NumberField F] (l : ℕ) [Fact l.Prime] (w : Plc F) :
    Finite (Emb l w) := by
  refine Finite.of_injective
    (fun j : Emb l w => (j.1.comp (algebraMap F (w.adicCompletion F)) : F →+* Qbar l)) fun j j' hjj => ?_
  refine Subtype.ext (DFunLike.coe_injective ?_)
  refine (HeightOneSpectrum.denseRange_algebraMap (K := F) (v := w)).equalizer j.2 j'.2 ?_
  funext x
  exact DFunLike.congr_fun hjj x

private theorem wt_one {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ}
    [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w)
    (κ : ↥(Dec (F := F) A) →* (Qbar l)ˣ) (ph : ↥(Ine (F := F) A) →* (Qbar l)ˣ)
    (ho : IsOpen (ph.ker : Set ↥(Ine (F := F) A)))
    (H : ∀ σ : ↥(Ine (F := F) A), κ (Subgroup.inclusion (Weil_le_Dec h) (ineIncl h σ)) * ph σ = 1) :
    IsWtPart h κ 0 ph :=
  ⟨ho, fun a _ σ => by rw [H]; simp⟩

private theorem wt_mul {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ}
    [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F} {h : IsPlaceOver A w}
    {κ κ' : ↥(Dec (F := F) A) →* (Qbar l)ˣ} {wt wt' : Emb l w → ℤ} {ph ph' : ↥(Ine (F := F) A) →* (Qbar l)ˣ}
    (H : IsWtPart h κ wt ph) (H' : IsWtPart h κ' wt' ph') : IsWtPart h (κ * κ') (wt + wt') (ph * ph') := by
  haveI := finite_emb l w
  haveI := Fintype.ofFinite (Emb l w)
  refine ⟨?_, fun a ha σ => ?_⟩
  · refine Subgroup.isOpen_mono (H₁ := ph.ker ⊓ ph'.ker) (fun x hx => ?_) (H.1.inter H'.1)
    have h1 : ph x = 1 := hx.1
    have h2 : ph' x = 1 := hx.2
    simp [MonoidHom.mem_ker, h1, h2]
  · have h1 := H.2 a ha σ
    have h2 := H'.2 a ha σ
    rw [finprod_eq_prod_of_fintype] at h1 h2 ⊢
    rw [MonoidHom.mul_apply, MonoidHom.mul_apply, mul_mul_mul_comm, Units.val_mul, h1, h2, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [Pi.add_apply, neg_add, zpow_add₀ ((map_ne_zero τ.1).2 (Units.ne_zero _))]

private theorem wt_zpow {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ}
    [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F} {h : IsPlaceOver A w}
    {κ : ↥(Dec (F := F) A) →* (Qbar l)ˣ} {wt : Emb l w → ℤ} {ph : ↥(Ine (F := F) A) →* (Qbar l)ˣ}
    (H : IsWtPart h κ wt ph) (m : ℤ) : IsWtPart h (κ ^ m) (m • wt) (ph ^ m) := by
  haveI := finite_emb l w
  haveI := Fintype.ofFinite (Emb l w)
  refine ⟨?_, fun a ha σ => ?_⟩
  · refine Subgroup.isOpen_mono (H₁ := ph.ker) (fun x hx => ?_) H.1
    have h1 : ph x = 1 := hx
    rw [MonoidHom.mem_ker, MonoidHom.zpow_apply, h1, one_zpow]
  · have h1 := H.2 a ha σ
    rw [finprod_eq_prod_of_fintype] at h1 ⊢
    rw [MonoidHom.zpow_apply, MonoidHom.zpow_apply, ← mul_zpow, Units.val_zpow_eq_zpow_val, h1, ← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← zpow_mul, Pi.smul_apply, smul_eq_mul, neg_mul, mul_comm]

theorem UpperTheory.V.Loc.laMul :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w), (∀ (κ κ' : ↥(Dec (F := F) A) →* (Qbar l)ˣ) (wt wt' : Emb l w → ℤ) (ph ph' : ↥(Ine (F := F) A) →* (Qbar l)ˣ), IsWtPart h κ wt ph → IsWtPart h κ' wt' ph' → IsWtPart h (κ * κ') (wt + wt') (ph * ph') ∧ IsWtPart h κ⁻¹ (-wt) ph⁻¹) ∧ (∀ (κ : ↥(Dec (F := F) A) →* (Qbar l)ˣ) (wt : Emb l w → ℤ) (ph : ↥(Ine (F := F) A) →* (Qbar l)ˣ) (m : ℤ), IsWtPart h κ wt ph → IsWtPart h (κ ^ m) (m • wt) (ph ^ m)) ∧ ∀ (κ : ↥(Dec (F := F) A) →* (Qbar l)ˣ) (ph : ↥(Ine (F := F) A) →* (Qbar l)ˣ), IsOpen (ph.ker : Set ↥(Ine (F := F) A)) → (∀ σ : ↥(Ine (F := F) A), κ (Subgroup.inclusion (Weil_le_Dec h) (ineIncl h σ)) * ph σ = 1) → IsWtPart h κ 0 ph := by
  intro F Ω _ _ _ _ _ l _ A w h
  refine ⟨fun κ κ' wt wt' ph ph' H H' => ⟨wt_mul H H', ?_⟩, fun κ wt ph m H => wt_zpow H m, wt_one h⟩
  simpa only [zpow_neg_one, neg_smul, one_smul] using wt_zpow H (-1)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaCyc
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in
theorem UpperTheory.V.Loc.laCyc :
    GlobalArtinReciprocity → ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → IsWtPart h ((cycBar F Ω l).comp (Dec (F := F) A).subtype) (fun _ => -1) 1 := by
  intro H F Ω _ _ _ _ _ l _ A w h _
  refine ⟨by simp, fun a ha σ => ?_⟩
  obtain ⟨art, hart⟩ := H F Ω
  obtain ⟨ι⟩ : Nonempty (Qbar l ≃+* ℂ) := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex l
  obtain ⟨μ, hμ, hL⟩ := hart.exists_isLAdicOf ι (CharAboveModel.absPow_isAlgPos F 1)
  have e : μ = cycBar F Ω l ^ 1 := CharAboveModel.eq_cyc_pow hart hμ hL
  rw [pow_one] at e
  subst e
  have h1 := hL.loc (a (ineIncl h σ)) _ (ha.glob art hart (ineIncl h σ))
  have hu : Formalism.L2.Host.IsUnitAt w (a (ineIncl h σ)) := by
    have h2 := ha.ord_eq (ineIncl h σ)
    rw [deg_ineIncl, neg_zero] at h2
    haveI : (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
      Valuation.Compatible.ofValuation _
    exact (ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion F))
      (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ)))).eq_one_iff_eq_one.1
      (GlobalTheory.SmGL.ord_eq_zero_iff.1 h2)
  rw [(Model.absPow_isAbsPow F (1 : ℕ)).1 w _ hu] at h1
  simp only [Units.val_one, map_one, one_mul, locPow] at h1
  simpa using h1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaExists
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W
open Topology Pointwise

private theorem ext_dense {W D B : Type} [Group W] [Group D] [TopologicalSpace D] [IsTopologicalGroup D]
    [CompactSpace D] [T2Space D] [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [T2Space B]
    (i : W →* D) (hi : DenseRange i) (χ : W →* B) (C : Set B) (hC : IsCompact C) (hχ : ∀ σ, χ σ ∈ C)
    (h1 : ∀ V ∈ 𝓝 (1 : B), ∃ U ∈ 𝓝 (1 : D), ∀ σ, i σ ∈ U → χ σ ∈ V) :
    ∃! κ : D →* B, Continuous κ ∧ ∀ σ, κ (i σ) = χ σ := by
  let Γ : Subgroup (D × B) := (i.prod χ).range.topologicalClosure
  have hΓ : IsCompact (Γ : Set (D × B)) := by
    refine (isCompact_univ.prod hC).of_isClosed_subset (Subgroup.isClosed_topologicalClosure _) ?_
    refine closure_minimal ?_ (isCompact_univ.prod hC).isClosed
    rintro _ ⟨σ, rfl⟩
    exact ⟨trivial, hχ σ⟩
  haveI : CompactSpace Γ := isCompact_iff_compactSpace.1 hΓ
  let p : Γ →* D := (MonoidHom.fst D B).comp Γ.subtype
  have hp : Continuous p := continuous_fst.comp continuous_subtype_val
  have hmem : ∀ σ, (i σ, χ σ) ∈ Γ := fun σ => Subgroup.le_topologicalClosure _ ⟨σ, rfl⟩
  have hinj : Function.Injective p := by
    rw [injective_iff_map_eq_one]
    rintro ⟨⟨d, k⟩, hk⟩ hd
    obtain rfl : d = 1 := hd
    by_contra hne
    have hk1 : (1 : B) ≠ k := by
      rintro rfl
      exact hne rfl
    obtain ⟨V, V', hV, hV', hVV⟩ := t2_separation_nhds hk1
    obtain ⟨U, hU, H⟩ := h1 V hV
    obtain ⟨_, ⟨h2, h3⟩, σ, rfl⟩ := mem_closure_iff_nhds.1 hk _ (prod_mem_nhds hU hV')
    exact Set.disjoint_left.1 hVV (H σ h2) h3
  have hsurj : Function.Surjective p := by
    have h2 : IsClosed (Set.range p) := (isCompact_range hp).isClosed
    have h3 : Set.range i ⊆ Set.range p := by
      rintro _ ⟨σ, rfl⟩
      exact ⟨⟨_, hmem σ⟩, rfl⟩
    intro d
    exact closure_minimal h3 h2 (hi d)
  let e : Γ ≃* D := MulEquiv.ofBijective p ⟨hinj, hsurj⟩
  have he : Continuous e.symm := Continuous.continuous_symm_of_equiv_compact_to_t2 (f := e.toEquiv) hp
  refine ⟨((MonoidHom.snd D B).comp Γ.subtype).comp e.symm.toMonoidHom,
    ⟨continuous_snd.comp (continuous_subtype_val.comp he), fun σ => ?_⟩, ?_⟩
  · have : e.symm (i σ) = ⟨_, hmem σ⟩ := e.symm_apply_eq.2 rfl
    show (e.symm (i σ)).1.2 = _
    rw [this]
  · rintro κ ⟨hκ, H⟩
    refine DFunLike.coe_injective (hi.equalizer hκ (continuous_snd.comp (continuous_subtype_val.comp he)) ?_)
    funext σ
    have : e.symm (i σ) = ⟨_, hmem σ⟩ := e.symm_apply_eq.2 rfl
    show κ (i σ) = (e.symm (i σ)).1.2
    rw [this, H]

private def ballSub (l : ℕ) [Fact l.Prime] (ε : ℝ) (hε : 0 < ε) : Subgroup (Qbar l)ˣ where
  carrier := {x | ‖(x : Qbar l)‖ = 1 ∧ ‖(x : Qbar l) - 1‖ < ε}
  one_mem' := by simpa using hε
  mul_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨by simp [hx, hy], ?_⟩
    have e : ((x * y : (Qbar l)ˣ) : Qbar l) - 1 = x * (y - 1) + (x - 1) := by push_cast; ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ hx')
    rwa [norm_mul, hx, one_mul]
  inv_mem' := by
    rintro x ⟨hx, hx'⟩
    refine ⟨by simp [hx], ?_⟩
    have e : ((x⁻¹ : (Qbar l)ˣ) : Qbar l) - 1 = -((x : Qbar l)⁻¹ * (x - 1)) := by
      have := x.ne_zero
      push_cast; field_simp; ring
    rwa [e, norm_neg, norm_mul, norm_inv, hx, inv_one, one_mul]

private theorem exists_compact {l : ℕ} [Fact l.Prime] (u : (Qbar l)ˣ) (hu : ‖(u : Qbar l)‖ = 1) :
    ∃ C : Subgroup (Qbar l)ˣ, IsCompact (C : Set (Qbar l)ˣ) ∧ u ∈ C ∧ ∀ x ∈ C, ‖(x : Qbar l)‖ = 1 := by
  let L : IntermediateField ℚ_[l] (Qbar l) := IntermediateField.adjoin ℚ_[l] {(u : Qbar l)}
  haveI : FiniteDimensional ℚ_[l] L := IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)
  let C : Subgroup (Qbar l)ˣ :=
    { carrier := {x | (x : Qbar l) ∈ L ∧ ‖(x : Qbar l)‖ = 1}
      one_mem' := ⟨by simpa using L.one_mem, by simp⟩
      mul_mem' := fun hx hy => ⟨L.mul_mem hx.1 hy.1, by simp [hx.2, hy.2]⟩
      inv_mem' := fun hx => ⟨by simpa using L.inv_mem hx.1, by simp [hx.2]⟩ }
  refine ⟨C, ?_, ⟨IntermediateField.mem_adjoin_simple_self _ _, hu⟩, fun x hx => hx.2⟩
  rw [Units.isEmbedding_val₀.isCompact_iff]
  haveI : FiniteDimensional ℚ_[l] L.toSubmodule := inferInstanceAs (FiniteDimensional ℚ_[l] L)
  haveI : ProperSpace L.toSubmodule := FiniteDimensional.proper ℚ_[l] _
  convert (isCompact_sphere (0 : L.toSubmodule) 1).image continuous_subtype_val using 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy.1⟩, by simpa using hy.2, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    have hy' : ‖(y : Qbar l)‖ = 1 := by simpa using hy
    have h0 : (y : Qbar l) ≠ 0 := fun h => by simp [h] at hy'
    exact ⟨Units.mk0 _ h0, ⟨y.2, hy'⟩, rfl⟩

theorem UpperTheory.V.Loc.laExists :
    GlobalArtinReciprocity → ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion F)ˣ), IsLocalArtin h a → ∀ ξ : (w.adicCompletion F)ˣ →* (Qbar l)ˣ, Continuous ξ → (∀ x, ‖(ξ x : Qbar l)‖ = 1) → ∃! κ : ↥(Dec (F := F) A) →* (Qbar l)ˣ, Continuous κ ∧ ∀ σ : Weil h, κ (Subgroup.inclusion (Weil_le_Dec h) σ) = ξ (a σ) := by
  intro _ F Ω _ _ _ _ _ l _ A w h a ha ξ hξ hn
  haveI : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  haveI : CompactSpace (Dec (F := F) A) := isCompact_iff_compactSpace.1 (isClosed_Dec A).isCompact
  haveI := compactSpace_Ine (E := F) A
  let χ := ξ.comp a
  have hI : Continuous fun τ : Ine (F := F) A => χ (ineIncl h τ) := hξ.comp ha.cont
  obtain ⟨C, hC, huC, hC1⟩ := exists_compact (χ (frob h)) (hn _)
  refine ext_dense (Subgroup.inclusion (Weil_le_Dec h)) ?_ χ
    ((C : Set (Qbar l)ˣ) * Set.range fun τ : Ine (F := F) A => χ (ineIncl h τ))
    (hC.mul (isCompact_range hI)) (fun σ => ?_) fun V hV => ?_
  · have h1 := GlobalTheory.TameQuot.closure_frob_sup_Ine F Ω A w h
      (Subgroup.inclusion (Weil_le_Dec h) (frob h)) (isFrob_frob (h := h))
    have h2 : Subgroup.zpowers (Subgroup.inclusion (Weil_le_Dec h) (frob h)) ⊔
        (Ine (F := F) A).subgroupOf (Dec (F := F) A) ≤ (Subgroup.inclusion (Weil_le_Dec h)).range := by
      refine sup_le ?_ fun σ hσ => ⟨⟨σ, Ine_le_Weil h hσ⟩, rfl⟩
      rw [Subgroup.zpowers_le]
      exact ⟨_, rfl⟩
    intro d
    have h3 : d ∈ (⊤ : Subgroup (Dec (F := F) A)) := trivial
    rw [← h1] at h3
    exact closure_mono h2 h3
  · obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul deg_frob σ
    refine ⟨χ (frob h) ^ deg σ, C.zpow_mem huC _, _, ⟨τ, rfl⟩, ?_⟩
    conv_rhs => rw [hτ, map_mul, map_zpow]
  · rw [Units.isEmbedding_val₀.nhds_eq_comap, Filter.mem_comap] at hV
    obtain ⟨V', hV', hVV⟩ := hV
    obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.1 hV'
    let H := ballSub l ε hε
    have hH : ∀ x ∈ H, x ∈ V := fun x hx => hVV (hεV (by simpa [dist_eq_norm] using hx.2))
    have hop : IsOpen {x : (Qbar l)ˣ | ‖(x : Qbar l) - 1‖ < ε} :=
      isOpen_lt ((Units.continuous_val.sub continuous_const).norm) continuous_const
    haveI : CompactSpace C := isCompact_iff_compactSpace.1 hC
    have hHC : IsOpen ((H.subgroupOf C : Subgroup C) : Set C) := by
      convert hop.preimage (continuous_subtype_val (p := (· ∈ C))) using 1
      ext x
      exact ⟨fun hx => hx.2, fun hx => ⟨hC1 _ x.2, hx⟩⟩
    haveI := (H.subgroupOf C).quotient_finite_of_isOpen hHC
    obtain ⟨N, hN, -, hNH⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
      (Subgroup.index_ne_zero_of_finite (H := H.subgroupOf C)) ⟨_, huC⟩
    have hNH' : χ (frob h) ^ N ∈ H := hNH
    have hM := (hop.preimage hI).mem_nhds (x := 1) (by simpa using hε)
    rw [nhds_subtype_eq_comap, Filter.mem_comap] at hM
    obtain ⟨U, hU, hUM⟩ := hM
    obtain ⟨E, hE, hEU⟩ := (krullTopology_mem_nhds_one_iff F Ω U).1 hU
    have hEo : IsOpen (E.fixingSubgroup : Set (G F Ω)) := E.fixingSubgroup_isOpen
    haveI := E.fixingSubgroup.quotient_finite_of_isOpen hEo
    obtain ⟨m, hm, -, hmE⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
      (Subgroup.index_ne_zero_of_finite (H := E.fixingSubgroup)) (frob h : G F Ω)
    obtain ⟨ζ, hζ⟩ := GlobalTheory.exists_fixed_dvd_deg F Ω A w h (m * N) (Nat.mul_pos hm hN)
    have hζo : IsOpen (MulAction.stabilizer (G F Ω) ζ : Set (G F Ω)) := stabilizer_isOpen_of_isIntegral ζ
    refine ⟨_, continuous_subtype_val.continuousAt.preimage_mem_nhds
      ((hEo.inter hζo).mem_nhds ⟨E.fixingSubgroup.one_mem, (MulAction.stabilizer (G F Ω) ζ).one_mem⟩), fun σ hσ => hH _ ?_⟩
    obtain ⟨k, hk⟩ := hζ σ hσ.2
    obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul deg_frob σ
    have h1 : ((frob h ^ deg σ : Weil h) : G F Ω) ∈ E.fixingSubgroup := by
      rw [hk, Subgroup.coe_zpow, Nat.cast_mul, mul_assoc, zpow_mul, zpow_natCast]
      exact E.fixingSubgroup.zpow_mem hmE _
    have h2 : (τ : G F Ω) ∈ E.fixingSubgroup := by
      have h3 : (σ : G F Ω) ∈ E.fixingSubgroup := hσ.1
      rw [hτ, Subgroup.coe_mul] at h3
      exact (E.fixingSubgroup.mul_mem_cancel_left h1).1 h3
    rw [hτ, map_mul, map_zpow]
    refine H.mul_mem ?_ ⟨hn _, hUM (hEU h2)⟩
    rw [hk, Nat.cast_mul, mul_comm (m : ℤ), mul_assoc, zpow_mul, zpow_natCast]
    exact H.zpow_mem hNH' _
end

