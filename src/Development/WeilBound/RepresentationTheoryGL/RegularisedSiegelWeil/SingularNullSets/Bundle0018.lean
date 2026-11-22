import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LApproxIdS
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0007
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0746
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0747
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0744
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0009
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0684
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0382
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.LeftInvOfIsSection
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0015

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.CharSum
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LApproxId

theorem transfer {H K ι : Type} [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H] [MeasurableSpace H]
    [BorelSpace H] [AddCommGroup K] [TopologicalSpace K] [IsTopologicalAddGroup K] [LocallyCompactSpace K]
    [SecondCountableTopology K] [T2Space K] [MeasurableSpace K] [BorelSpace K] [Fintype ι]
    (Θ : H ≃ₜ+ (ι → K)) (lam : Measure H) [lam.IsAddHaarMeasure] (ν : Measure K) [ν.IsAddHaarMeasure] :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ f : ι → K → ℂ, (∫ x, ∏ i, f i (Θ x i) ∂lam = (c : ℂ) * ∏ i, ∫ y, f i y ∂ν) ∧
      ((∀ i, Integrable (f i) ν) → Integrable (fun x => ∏ i, f i (Θ x i)) lam) := by
  have : (Measure.pi fun _ : ι => ν).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  obtain ⟨c, hc, hmap⟩ := haar_map_eq Θ lam (Measure.pi fun _ : ι => ν)
  have hemb : MeasurableEmbedding Θ := Θ.toHomeomorph.measurableEmbedding
  refine ⟨c, hc, fun f => ⟨?_, fun hf => ?_⟩⟩
  · have h1 := hemb.integral_map (μ := lam) (fun v : ι → K => ∏ i, f i (v i))
    rw [← h1, hmap, integral_smul_nnreal_measure, integral_fintype_prod_eq_prod, NNReal.smul_def, Complex.real_smul]
  · have h2 : Integrable (fun v : ι → K => ∏ i, f i (v i)) (lam.map Θ) := by
      rw [hmap]
      exact (Integrable.fintype_prod (μ := fun _ => ν) hf).smul_measure ENNReal.coe_ne_top
    exact hemb.integrable_map_iff.mp h2

open GlobalTheory.CompanionTheory.SiegelND.Coef.TestN in

theorem hCo_smul {F E R : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)
    {d n : ℕ} (b : Module.Basis (Fin d) F E) (r : R) (X X' : HermR R σ n)
    (h : X'.1 = algebraMap R (R ⊗[F] E) r • X.1) (i : Idx n d) : hCo R σ b X' i = r * hCo R σ b X i := by
  rcases i with i | q
  · simp only [hCo, Sum.elim_inl, h, Matrix.smul_apply, smul_eq_mul, ← Algebra.smul_def, map_smul]
    exact (mul_smul_comm _ _ _).symm
  · simp only [hCo, Sum.elim_inr, h, Matrix.smul_apply, smul_eq_mul, ← Algebra.smul_def, map_smul,
      Finsupp.smul_apply]

theorem char_sum {A ι : Type} [AddCommMonoid A] (ψ : AddChar A ℂ) (s : Finset ι) (a : ι → A) :
    ψ (∑ i ∈ s, a i) = ∏ i ∈ s, ψ (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, AddChar.map_add_eq_mul, ih]

end PositivityTheory.Rg.Rsw.L.LApproxId

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.ConjUnitIdeleAt
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LJPos

open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (tensNU tensNU_tmul)
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (CharUnramAt)

def pkgOf (D : D7) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) : SplitPkg D v where
  π := splitAlgEquiv (isCMExt_host D) τ
  swap := splitAlgEquiv_sigR (isCMExt_host D) τ
  int := fun _ => mem_intLoc_iff_split (isCMExt_host D) τ

theorem sigR_tensNU {F E R R' : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] [CommRing R']
    [Algebra F R'] (σ : E →ₐ[F] E) (j : R →ₗ[F] R') (hj : ∀ a b, j (a * b) = j a * j b) (y : R ⊗[F] E) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R' σ (tensNU j hj y) = tensNU j hj (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem conjUnit_ideleAt {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (w : (Fv F v ⊗[F] E)ˣ) :
    conjUnit σ (ideleAt F E v w) = ideleAt F E v (conjUnit σ w) := by
  refine Units.ext ?_
  change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ (1 - tensNU (inFin v) (inFin_mul v) 1 + tensNU (inFin v) (inFin_mul v) w.1) =
    1 - tensNU (inFin v) (inFin_mul v) 1 + tensNU (inFin v) (inFin_mul v) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ w.1)
  rw [map_add, map_sub, map_one, sigR_tensNU, sigR_tensNU, map_one]

theorem resEta_norm {D : D7} {χ : (AE D)ˣ →* Circle} {r : ℕ} (h : ResEta D χ r) (x : (AE D)ˣ) :
    χ (x * conjUnit D.sp.cm.sig x) = 1 := by
  obtain ⟨⟨η, hη⟩, h2⟩ := h
  have e : x * conjUnit D.sp.cm.sig x =
      idF D (Units.map (Algebra.norm (AF D.host.F) : AE D →* AF D.host.F) x) :=
    Units.ext (algebraMap_norm_eq (isCMExt_host D) x.1).symm
  rw [e, h2 η hη, hη.2.2.1, one_pow]

theorem diag_eq_norm {D : D7} {v : Pl D} (P : SplitPkg D v) (u : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ)
    (hu : (P.π u).1 = (P.π u).2) : ∃ w, u = w * conjUnit D.sp.cm.sig w := by
  have h1 : (P.π u).1 * (P.π (u⁻¹ : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ)).1 = 1 := by
    rw [← Prod.fst_mul, ← map_mul, Units.mul_inv, map_one, Prod.fst_one]
  refine ⟨⟨P.π.symm ((P.π u).1, 1), P.π.symm ((P.π (u⁻¹ : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ)).1, 1), ?_, ?_⟩,
    Units.ext (P.π.injective ?_)⟩
  · rw [← map_mul, Prod.mk_mul_mk, h1, mul_one]; exact map_one _
  · rw [← map_mul, Prod.mk_mul_mk, mul_comm, h1, mul_one]; exact map_one _
  · change _ = P.π (P.π.symm ((P.π u).1, 1) * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ D.sp.cm.sig (P.π.symm ((P.π u).1, 1)))
    rw [map_mul, P.swap, AlgEquiv.apply_symm_apply]
    exact Prod.ext (by simp) (by simp [hu])

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : HeightOneSpectrum (𝓞 F)}

omit [NumberField E] in
theorem snd_tensNU_mem {y : Fv F v ⊗[F] E} (hy : y ∈ intLoc F E v) :
    Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (tensNU (inFin v) (inFin_mul v) y) ∈
      AddSubgroup.closure {y : Af F ⊗[F] E | ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)} := by
  refine intLoc_induction (p := fun y => Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)
      (tensNU (inFin v) (inFin_mul v) y) ∈
      AddSubgroup.closure {y : Af F ⊗[F] E | ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)})
    (fun a ha x => AddSubgroup.subset_closure ⟨singleFin v a, fun w => ?_, x, rfl⟩) ?_ (fun y z hy hz => ?_)
    (fun y hy => ?_) hy
  · by_cases hw : w = v
    · subst hw; rw [evalV_singleFin_self]; exact ha
    · rw [evalV_singleFin_ne hw]; exact zero_mem _
  · rw [map_zero, map_zero]; exact zero_mem _
  · rw [map_add, map_add]; exact add_mem hy hz
  · rw [map_neg, map_neg]; exact neg_mem hy

omit [NumberField E] in
theorem snd_ideleAt_mem {u : (Fv F v ⊗[F] E)ˣ} (hu : u.1 ∈ intLoc F E v) :
    Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (ideleAt F E v u).1 ∈
      AddSubgroup.closure {y : Af F ⊗[F] E | ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)} := by
  rw [ideleAt, val_extUnit, map_add, map_sub, map_one]
  exact add_mem (sub_mem (AddSubgroup.subset_closure ⟨1, fun w => by rw [map_one]; exact one_mem _, 1, rfl⟩)
    (snd_tensNU_mem (one_mem _))) (snd_tensNU_mem hu)

omit [NumberField E] in
theorem eval_snd_ideleAt {w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v) (u : (Fv F v ⊗[F] E)ˣ) :
    Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w) (AlgHom.id F E)
      (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (ideleAt F E v u).1) = 1 := by
  rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]
  exact map_extUnit_zero _ (inFin v) (inFin_mul v) (fun a => evalV_singleFin_ne hw a) u

omit [NumberField E] in
theorem fst_ideleAt (u : (Fv F v ⊗[F] E)ˣ) :
    Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (ideleAt F E v u).1 = 1 :=
  map_extUnit_zero _ _ _ (fun _ => rfl) u

end Gen

theorem unram_ideleAt {D : D7} {χ : (AE D)ˣ →* Circle} {v : Pl D} (h : CharUnramAt D χ v)
    {u : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ} (hu : u.1 ∈ intLoc D.host.F D.host.E v)
    (hu' : (u⁻¹).1 ∈ intLoc D.host.F D.host.E v) : χ (ideleAt D.host.F D.host.E v u) = 1 := by
  refine h _ (fst_ideleAt u) (fun w hw => eval_snd_ideleAt hw u) (snd_ideleAt_mem hu) ?_
  rw [← MonoidHom.map_inv]
  exact snd_ideleAt_mem hu'

theorem placeEx : PlaceEx := by
  classical
  intro D ψ hψ χ hχ r hr S
  have hev := (GlobalTheory.T.character_conductor_condition D.host.F ψ hψ).and (GlobalTheory.FinPl.LastInhab.eventually_charUnramAt D χ hχ.1)
  obtain ⟨v, hv, ⟨τ⟩⟩ := GlobalTheory.Orb.exists_split_place_notMem (isCMExt_host D) (S ∪ (Filter.eventually_cofinite.1 hev).toFinset)
  rw [Finset.mem_union, not_or, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hv
  refine ⟨v, hv.1, pkgOf D v τ, hv.2.1, fun u h1 h2 h3 => ?_, fun u hu => ?_⟩
  · refine unram_ideleAt hv.2.2 (((pkgOf D v τ).int _).2 ⟨h1, by rw [h3]; exact one_mem _⟩)
      (((pkgOf D v τ).int _).2 ⟨h2, ?_⟩)
    have e : ((pkgOf D v τ).π u).2 * ((pkgOf D v τ).π (u⁻¹ : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ)).2 = 1 := by
      rw [← Prod.snd_mul, ← map_mul, Units.mul_inv, map_one, Prod.snd_one]
    rw [h3, one_mul] at e
    rw [e]; exact one_mem _
  · obtain ⟨w, rfl⟩ := diag_eq_norm _ u hu
    rw [map_mul, ← conjUnit_ideleAt]
    exact resEta_norm hr _

end PositivityTheory.Rg.Rsw.L.LJPos

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.KappaReal
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LApproxId

theorem kappa_real {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ) {ε : AF F}
    (ν : Measure (fixE ε)) [SFinite ν] (τ : fixE ε → ℝ) (hτ0 : ∀ h, 0 ≤ τ h) (hτI : Integrable τ ν)
    (hτpos : 0 < ∫ h, τ h ∂ν) (M : ℝ) (hτM : ∀ h, τ h ≤ M) (A : fixE ε → ℂ)
    (hA : ∀ s, A s = ∫ h, (τ h : ℂ) * ψ (h.1 * s.1) ∂ν) (hAI : Integrable A ν) (κ : ℂ)
    (hκ : ∀ s : fixE ε, ∫ h, A h * ψ (h.1 * s.1) ∂ν = κ * τ (-s)) :
    κ.im = 0 ∧ 0 ≤ κ.re := by
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  haveI : SecondCountableTopology (fixE ε) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : OpensMeasurableSpace (fixE ε × fixE ε) := inferInstance
  have hψn : ∀ x, ‖ψ x‖ = 1 := hψ.2.1
  have hconj : ∀ x, (starRingEnd ℂ) (ψ x) = ψ (-x) := by
    intro x
    rw [AddChar.map_neg_eq_inv, Complex.inv_def, Complex.normSq_eq_norm_sq, hψn x]
    simp
  have hτC : Integrable (fun h => (τ h : ℂ)) ν := hτI.ofReal

  have hA' : ∀ h : fixE ε, (starRingEnd ℂ) (A h) = ∫ h', (τ h' : ℂ) * ψ (h.1 * (-h').1) ∂ν := by
    intro h
    rw [hA, ← integral_conj]
    congr 1
    funext h'
    rw [map_mul, Complex.conj_ofReal, hconj]
    congr 2
    change -(h'.1 * h.1) = h.1 * -h'.1
    ring

  set f : fixE ε → fixE ε → ℂ := fun h h' => A h * ((τ h' : ℂ) * ψ (h.1 * (-h').1)) with hf
  have hcont : Continuous fun z : fixE ε × fixE ε => ψ (z.1.1 * (-z.2).1) :=
    hψ.1.comp ((continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp
      (continuous_neg.comp continuous_snd)))
  have hfI : Integrable (Function.uncurry f) (ν.prod ν) := by
    refine Integrable.mono' (hAI.norm.mul_prod hτI) ?_ (Filter.Eventually.of_forall fun z => ?_)
    · exact hAI.aestronglyMeasurable.comp_fst.mul (hτC.aestronglyMeasurable.comp_snd.mul hcont.aestronglyMeasurable)
    · simp only [Function.uncurry, hf, norm_mul, hψn, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hτ0 _)]
      exact le_rfl
  have hsw := integral_integral_swap hfI
  have hL : ∫ h, A h * (starRingEnd ℂ) (A h) ∂ν = ∫ h, ∫ h', f h h' ∂ν ∂ν := by
    congr 1
    funext h
    rw [hA', ← integral_const_mul]
  have hR : ∫ h', ∫ h, f h h' ∂ν ∂ν = κ * ∫ h', ((τ h' * τ h' : ℝ) : ℂ) ∂ν := by
    rw [← integral_const_mul]
    congr 1
    funext h'
    have h1 : ∫ h, f h h' ∂ν = (τ h' : ℂ) * ∫ h, A h * ψ (h.1 * (-h').1) ∂ν := by
      rw [← integral_const_mul]
      congr 1
      funext h
      simp only [hf]
      ring
    rw [h1, hκ, neg_neg]
    push_cast
    ring

  have hLr : ∫ h, A h * (starRingEnd ℂ) (A h) ∂ν = ((∫ h, Complex.normSq (A h) ∂ν : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1
    funext h
    exact Complex.mul_conj _
  have hL0 : 0 ≤ ∫ h, Complex.normSq (A h) ∂ν := integral_nonneg fun h => Complex.normSq_nonneg _
  have hQI : Integrable (fun h => τ h * τ h) ν := by
    refine Integrable.mono' (hτI.const_mul M) (hτI.aestronglyMeasurable.mul hτI.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun h => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hτ0 h) (hτ0 h)), mul_comm M]
    exact mul_le_mul_of_nonneg_left (hτM h) (hτ0 h)
  have hQ0 : 0 < ∫ h, τ h * τ h ∂ν := by
    refine lt_of_le_of_ne (integral_nonneg fun h => mul_nonneg (hτ0 h) (hτ0 h)) fun h0 => ?_
    have hz := (integral_eq_zero_iff_of_nonneg (fun h => mul_nonneg (hτ0 h) (hτ0 h)) hQI).1 h0.symm
    have hz' : τ =ᵐ[ν] 0 := hz.mono fun h hh => by
      simpa using (mul_self_eq_zero.1 hh)
    rw [integral_congr_ae hz'] at hτpos
    simp at hτpos
  have hmain : ((∫ h, Complex.normSq (A h) ∂ν : ℝ) : ℂ) = κ * ((∫ h, τ h * τ h ∂ν : ℝ) : ℂ) := by
    rw [← hLr, hL, hsw, hR, integral_complex_ofReal]
  have hκe : κ = (((∫ h, Complex.normSq (A h) ∂ν) / ∫ h, τ h * τ h ∂ν : ℝ) : ℂ) := by
    have hq : ((∫ h, τ h * τ h ∂ν : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hQ0.ne'
    rw [Complex.ofReal_div, hmain, mul_div_assoc, div_self hq, mul_one]
  rw [hκe, Complex.ofReal_im, Complex.ofReal_re]
  exact ⟨rfl, div_nonneg hL0 hQ0.le⟩

end PositivityTheory.Rg.Rsw.L.LApproxId

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LApproxIdC
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LApproxId

open scoped RestrictedProduct

theorem rp_nhds {ι : Type} {R : ι → Type} [∀ i, TopologicalSpace (R i)] {A : ∀ i, Set (R i)}
    (hA : ∀ i, IsOpen (A i)) (x : ∀ i, A i) (W : Set (Πʳ i, [R i, A i]))
    (hW : W ∈ 𝓝 (RestrictedProduct.structureMap R A cofinite x)) :
    ∃ V : ∀ i, Set (R i), (∀ i, V i ∈ 𝓝 (x i : R i)) ∧ ∀ z : Πʳ i, [R i, A i], (∀ i, z i ∈ V i) → z ∈ W := by
  rw [RestrictedProduct.nhds_eq_map_structureMap hA, Filter.mem_map, nhds_pi, Filter.mem_pi] at hW
  obtain ⟨I, -, t, ht, hIt⟩ := hW
  have ht' : ∀ i, ∃ u ∈ 𝓝 (x i : R i), Subtype.val ⁻¹' u ⊆ t i := fun i => mem_nhds_subtype _ _ _ |>.1 (ht i)
  choose u hu hut using ht'
  refine ⟨fun i => u i ∩ A i, fun i => Filter.inter_mem (hu i) ((hA i).mem_nhds (x i).2), fun z hz => ?_⟩
  let y : ∀ i, A i := fun i => ⟨z i, (hz i).2⟩
  have hyz : RestrictedProduct.structureMap R A cofinite y = z := Subtype.ext rfl
  rw [← hyz]
  exact hIt fun i _ => hut i (hz i).1

theorem af_nhds {F : Type} [Field F] [NumberField F] (W : Set (Af F)) (hW : W ∈ 𝓝 (0 : Af F)) :
    ∃ V : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v), (∀ v, V v ∈ 𝓝 (0 : Fv F v)) ∧
      ∀ z : Af F, (∀ v, z v ∈ V v) → z ∈ W := by
  have hA : ∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := fun v => Valued.isOpen_valuationSubring _
  have h0 : RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite (fun _ => ⟨0, zero_mem _⟩) =
      (0 : Af F) := rfl
  rw [← h0] at hW
  exact rp_nhds hA _ W hW

theorem top1 {F : Type} [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F) (hε : IsIdF S ε)
    (A : ℕ → Set (Ainf F)) (U : ℕ → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v))
    (hA : Tendsto A atTop (𝓝 0).smallSets) (hU : ∀ v, Tendsto (fun k => U k v) atTop (𝓝 0).smallSets) :
    Tendsto (fun k => {a : AF F | ε * a = a ∧ fstA F a ∈ A k ∧ ∀ v ∈ S, (sndA F a) v ∈ U k v}) atTop
      (𝓝 (0 : AF F)).smallSets := by
  rw [Filter.tendsto_smallSets_iff]
  intro W hW
  obtain ⟨W1, hW1, W2, hW2, hsub⟩ := mem_nhds_prod_iff.1 (show W ∈ 𝓝 ((0, 0) : Ainf F × Af F) from hW)
  obtain ⟨V, hV, hVW⟩ := af_nhds W2 hW2
  have e1 := Filter.tendsto_smallSets_iff.1 hA W1 hW1
  have e2 : ∀ᶠ k in atTop, ∀ v ∈ S, U k v ⊆ V v :=
    (Filter.eventually_all_finset S).2 fun v _ => Filter.tendsto_smallSets_iff.1 (hU v) (V v) (hV v)
  filter_upwards [e1, e2] with k h1 h2
  rintro a ⟨hεa, haA, haU⟩
  apply hsub
  refine ⟨h1 haA, hVW (sndA F a) fun v => ?_⟩
  by_cases hv : v ∈ S
  · exact h2 v hv (haU v hv)
  · have h3 : sndA F a = sndA F ε * sndA F a := by rw [← map_mul, hεa]
    have h4 : (sndA F a) v = (sndA F ε) v * (sndA F a) v := congrArg (fun z : Af F => z v) h3
    rw [hε.2 v, if_neg hv, zero_mul] at h4
    rw [h4]
    exact mem_of_mem_nhds (hV v)

end PositivityTheory.Rg.Rsw.L.LApproxId

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LCfRelC
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LCfRel

open Set GlobalTheory.Eis GlobalTheory.StdUnn.HeightExists GlobalTheory.StdUnn.PolesModel

variable {D : D7} {n : ℕ}

theorem law_fam {H : G D n → ℝ≥0} (hH : IsHt H) {χ : (AE D)ˣ →* Circle} {s₁ : ℂ} {φ : G D n → ℂ} (h : IsLaw χ s₁ φ)
    (z : ℂ) : IsLaw χ z (fam H φ s₁ z) := by
  intro q hq a ha g
  simp only [fam]
  rw [hH.2.2 q hq a ha g, h q hq a ha g, npow_mul]
  have e : npow (absA D (Matrix.GeneralLinearGroup.det a)) (z + (n : ℂ) / 2) =
      npow (absA D (Matrix.GeneralLinearGroup.det a)) (z - s₁) *
        npow (absA D (Matrix.GeneralLinearGroup.det a)) (s₁ + (n : ℂ) / 2) := by
    rw [← npow_add (hom_pos _ _)]; congr 1; ring
  rw [e]; ring

theorem cont_fam {H : G D n → ℝ≥0} (hH : IsHt H) {φ : G D n → ℂ} (hφ : Continuous φ) (s₁ : ℂ) :
    Continuous fun u : ℂ × G D n => fam H φ s₁ u.1 u.2 := by
  simp only [fam, npow_eq_exp (hH.2.1 _)]
  have h1 : Continuous fun u : ℂ × G D n => Real.log (H u.2 : ℝ) :=
    (NNReal.continuous_coe.comp (hH.1.comp continuous_snd)).log fun u => (NNReal.coe_pos.2 (hH.2.1 _)).ne'
  exact (((Complex.continuous_ofReal.comp h1).mul (continuous_fst.sub continuous_const)).cexp).mul
    (hφ.comp continuous_snd)

def cset (nb : hermA D n → G D n) {v : Pl D} (C : Cut D n v) (g : G D n) : Set (G D n) :=
  ⋃ x ∈ C.s, (fun k => g * k * nb x) '' (K D n : Set (G D n))

theorem isCompact_cset (nb : hermA D n → G D n) {v : Pl D} (C : Cut D n v) (g : G D n) : IsCompact (cset nb C g) :=
  C.s.isCompact_biUnion fun _ _ => isCompact_K.image ((continuous_const.mul continuous_id).mul continuous_const)

theorem mem_cset (nb : hermA D n → G D n) {v : Pl D} (C : Cut D n v) (g : G D n) (u : KAt D n v) {x : hermA D n}
    (hx : x ∈ C.s) : g * (u : G D n) * nb x ∈ cset nb C g :=
  mem_biUnion hx ⟨u, (Subgroup.mem_inf.1 u.2).1, rfl⟩

theorem farRight {χ : (AE D)ˣ →* Circle} {H : G D n → ℝ≥0} (hH : IsHt H) {s₀ : ℂ} {φ : G D n → ℂ}
    (hφc : Continuous φ) (hφl : IsLaw χ s₀ φ) (nb : hermA D n → G D n) {v : Pl D} (C : Cut D n v) (c : ℂ → ℂ)
    (νv : Measure (KAt D n v)) [IsFiniteMeasure νv]
    (hrel : ∀ z g, ∫ k, cutR nb C (fam H φ s₀ z) (g * k) ∂νv = c z * fam H φ s₀ z g)
    {z : ℂ} (hz : (n : ℝ) / 2 < z.re) (g : G D n) :
    ∫ u, cutR nb C (eisS (fam H φ s₀ z)) (g * u) ∂νv = c z * eisS (fam H φ s₀ z) g := by
  have := t2Space_adeleRing' (F := D.host.F)
  have hcont := cont_fam hH hφc s₀
  have hz' : Continuous (fam H φ s₀ z) := hcont.comp (continuous_const.prodMk continuous_id)
  obtain ⟨w, hw, hwb⟩ := exists_majorant (P := P D n) (Γ := GF D n) (χ := χ.comp detP) (ρ := (n : ℝ) / 2)
    (σ := (n : ℝ) / 2) (Φ := fam H φ s₀) isIwasawa isCompact_K hcont.continuousOn
    (fun s _ q g => by
      have := law_fam hH hφl s q q.2 (leviBlock (D := D) (n := n) q) rfl g
      push_cast
      exact this)
    (fun τ hτ => summable_spherical τ hτ) isCompact_singleton (singleton_subset_iff.2 hz) (isCompact_cset nb C g)
  have hb : ∀ q (u : KAt D n v) x, x ∈ C.s →
      ‖fam H φ s₀ z (((q.out : GF D n) : G D n) * g * u * nb x)‖ ≤ w q := fun q u x hx => by
    have := hwb q z rfl _ (mem_cset nb C g u hx)
    simpa only [term, mul_assoc] using this
  have hterm : ∀ u : KAt D n v, cutR nb C (eisS (fam H φ s₀ z)) (g * u) =
      ∑' q : Cosets (P D n) (GF D n), cutR nb C (fam H φ s₀ z) (((q.out : GF D n) : G D n) * g * u) := by
    intro u
    simp only [cutR, eisS, cosetSum]
    rw [Summable.tsum_finsetSum fun x hx => (Summable.of_norm_bounded hw fun q => by
      simpa only [term, mul_assoc] using hwb q z rfl _ (mem_cset nb C g u hx)).mul_left (C.co x)]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← tsum_mul_left]
    simp only [term, mul_assoc]
  calc ∫ u, cutR nb C (eisS (fam H φ s₀ z)) (g * u) ∂νv
      = ∫ u, ∑' q : Cosets (P D n) (GF D n), cutR nb C (fam H φ s₀ z) (((q.out : GF D n) : G D n) * g * u) ∂νv := by
        congr 1; funext u; exact hterm u
    _ = ∑' q : Cosets (P D n) (GF D n), ∫ u, cutR nb C (fam H φ s₀ z) (((q.out : GF D n) : G D n) * g * u) ∂νv := by
        refine integral_tsum_dom νv _ (fun q => (∑ x ∈ C.s, ‖C.co x‖) * w q) (hw.mul_left _) (fun q u => ?_)
          fun q => ?_
        · simp only [cutR]
          refine (norm_sum_le _ _).trans ?_
          rw [Finset.sum_mul]
          refine Finset.sum_le_sum fun x hx => ?_
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hb q u x hx) (norm_nonneg _)
        · refine Continuous.aestronglyMeasurable ?_
          simp only [cutR]
          exact continuous_finsetSum _ fun x _ => continuous_const.mul
            (hz'.comp ((continuous_const.mul continuous_subtype_val).mul continuous_const))
    _ = ∑' q : Cosets (P D n) (GF D n), c z * fam H φ s₀ z (((q.out : GF D n) : G D n) * g) := by
        congr 1; funext q; exact hrel z _
    _ = c z * eisS (fam H φ s₀ z) g := by
        rw [tsum_mul_left]; rfl

end PositivityTheory.Rg.Rsw.L.LCfRel

end
end

