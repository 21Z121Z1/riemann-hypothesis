import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0777
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0924
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0820
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0828
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1098
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0826
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0845
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0825
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0840
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0849
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0867
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0245
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0280
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1032
import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1121
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1084
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0182
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0075
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetCConstMul
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.ColNorms

theorem sqAt_nonneg {X : Fields} {n : ℕ} (lam : X.Tau → DomWeight n) (σ : X.K →+* ℂ) (x : Formalism.L2.DIV.VV X.K lam) :
    0 ≤ sqAt σ lam x := by
  rw [← (GlobalTheory.T.coefficientGram_posSemidef_and_normAtPlace X.E X.K X.Tau X.emb n lam σ).2 x]
  have h := (GlobalTheory.T.coefficientGram_posSemidef_and_normAtPlace X.E X.K X.Tau X.emb n lam (InfinitePlace.mk σ).embedding).1.dotProduct_mulVec_nonneg
    fun i => (InfinitePlace.mk σ).embedding ((bVV X.K lam).repr x i)
  refine le_of_le_of_eq (Complex.le_def.1 h).1 ?_
  congr 1
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.map_apply, Matrix.of_apply, Pi.star_apply, mul_assoc]
  rfl

theorem sqAt_smul {K : Type} [Field K] [StarRing K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (σ : K →+* ℂ) (a : K)
    (x : Formalism.L2.DIV.VV K lam) : sqAt σ lam (a • x) = ‖σ a‖ ^ 2 * sqAt σ lam x := by
  unfold sqAt
  rw [← Complex.re_ofReal_mul]
  congr 1
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h : ((‖σ a‖ ^ 2 : ℝ) : ℂ) = starRingEnd ℂ (σ a) * σ a := by
    rw [Complex.conj_mul']
    push_cast
    rfl
  rw [h]
  ring

theorem jetOp_sum {K : Type} [Field K] {ι : Type} [Fintype ι] {a b : ℕ} (lam : ι → DomWeight a) (lam' : ι → DomWeight b)
    (n : ι → ℕ) {α : Type} (R : Finset α) (c : α → K) (J : α → (DVar ι a b →₀ ℕ) → K) :
    jetOp lam lam' (fun m => ∑ x ∈ R, c x * J x m) n = ∑ x ∈ R, c x • jetOp lam lam' (J x) n := by
  have h : jetLin (fun m => ∑ x ∈ R, c x * J x m) = ∑ x ∈ R, c x • jetLin (K := K) (J x) := by
    refine (MvPolynomial.basisMonomials _ K).ext fun m => ?_
    simp only [jetLin, Module.Basis.constr_basis, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, MvPolynomial.smul_monomial,
      smul_eq_mul]
  ext1 P
  simp only [jetOp, jetMap, h, LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]

theorem jetC_const_mul {ι : Type} [Fintype ι] {a b : ℕ} (cD : ι → ℂ) (κ : ℂ) (F : VCx ι a b → ℂ)
    (h : Differentiable ℂ fun z => κ * F z) (m : DVar ι a b →₀ ℕ) : jetC cD (fun z => κ * F z) m = κ * jetC cD F m := by
  by_cases hκ : κ = 0
  · have := GlobalTheory.T.jet_finset_linear_combination ι a b cD Unit ∅ (fun _ => 0) (fun _ => F) (by simp) m
    simpa [hκ] using this
  · have hF : Differentiable ℂ F := by
      have := h.const_mul κ⁻¹
      simpa [← mul_assoc, inv_mul_cancel₀ hκ] using this
    have := GlobalTheory.T.jet_finset_linear_combination ι a b cD Unit {()} (fun _ => κ) (fun _ => F) (fun _ _ => hF) m
    simpa using this

theorem cj_coe (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (x : M) : StandardLatticesGL3.cj M ρ (x : ℂ) = ρ x := by
  unfold StandardLatticesGL3.cj TaylorLogMetric.liftM
  rw [dif_pos x.2]

theorem toHost_back {D : D7} {X : Fields} (s : Seam D X) {a b : ℕ} (F : VCx X.Tau a b → ℂ) :
    (fun z : VCx X.Tau a b => toHost s F fun τ => z (s.iT.symm τ)) = F := by
  funext z
  simp [toHost]

theorem diff_back {D : D7} {X : Fields} (s : Seam D X) {a b : ℕ} (F : TaylorLogMetric.VC D a b → ℂ) (h : Differentiable ℂ F) :
    Differentiable ℂ fun z : VCx X.Tau a b => F fun τ => z (s.iT.symm τ) := by
  refine h.comp ?_
  fun_prop

theorem block : GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.BlockBound → ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (dl : ℂ) (B : Base D cc dl) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (t0 : ℂ), X.Ok → s.Ok → StandardLatticesGL3.Crv D cc dl → GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc dl) t0 → (∀ τ, cD τ ≠ 0) → ∀ (a b : ℕ), a < b → Even (a * b) → StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc dl) t0 (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) (B.thZero a b) → ∀ (lam nu : X.Tau → DomWeight a) (lam' : X.Tau → DomWeight b), (∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.StepWeights (lam τ) (nu τ) (lam' τ)) → ∀ (S SB : Finset (HeightOneSpectrum (𝓞 X.E))) (cA c c' : ℕ), 0 < cA → 0 < c → 0 < c' → (ambOf s B χ cD).IndAdd a b S (cA * (c * c')) → JetsInField (ambOf s B χ cD) a b S (cA * (c * c')) (fun τ => ∑ i, (nu τ).w i) → ∀ (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (mI : SB → X.E → X.K) (L : Submodule (𝓞 X.E) (Sp X.E a)) (fr : Frs X.E a SB) (L' : Submodule (𝓞 X.E) (Sp X.E b)) (fr' : Frs X.E b SB), IsSdLat L → IsSdLat L' → ∀ (Ξ : HomE X.E a b → X.K) (β : ℝ), SmallDatum S L L' c Ξ β → ∀ (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (hK : ∀ k, s.σ₀ k ∈ M) (ρ : M →ₐ[ℚ] ℂ), TaylorLogMetric.DataIn D B.tor M → (∀ τ, cD τ ∈ M) → TaylorLogMetric.CoefIn D (B.thZero a b) M → ‖((ρ : M →+* ℂ).comp (s.σ₀.codRestrict M hK)) (muInvDet sel SB mU mI L fr * (muInvDet sel SB mU mI L' fr')⁻¹)‖ ≤ 1 → CoefOpLe ((ρ : M →+* ℂ).comp (s.σ₀.codRestrict M hK)) lam lam' (kerOf (thDistC (ambOf s B χ cD) S SB (cA * (c * c')) sel mU mI lam lam' fun τ => GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.lastEntry (nu τ)) S cA (c * c') L fr L' fr' Ξ) (GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.tmax b nu (β * (c : ℝ) ^ (2 * (Module.finrank ℚ X.E * a * b)) * Real.sqrt (supConst D a b) * Real.exp (logThAt B M ρ a b / 2)) fun τ => Real.exp (logOmAt B cD M ρ (s.iT τ))) := by
  intro hB D X s cc dl B χ cD t0 hX hs hcrv ht0 hc0 a b hab hev hE0 lam nu lam' hst S SB cA c c' hcA hc hc' hInd hJ sel mU mI
    L fr L' fr' hL hL' Ξ β hΞ M _ hK ρ hD hcM hco hsc
  classical
  set A := ambOf s B χ cD with hA
  set σ : X.K →+* ℂ := (ρ : M →+* ℂ).comp (s.σ₀.codRestrict M hK) with hσ
  set κ := (A.chiF a b L L')⁻¹ with hκ
  have hβ : 0 ≤ β := (norm_nonneg _).trans (hΞ.2.2 σ 0)
  obtain ⟨sd0, sdL⟩ := GlobalTheory.T.hermitianLatticeTransport_preserves_selfDual D X s hs a
  obtain ⟨sd0', sdL'⟩ := GlobalTheory.T.hermitianLatticeTransport_preserves_selfDual D X s hs b
  have hmv := GlobalTheory.T.thetaVectorUpToUnits_thMoved_of_thZero D cc dl B t0 hcrv ht0 a b _ _ (sdL L hL) (sdL' L' hL') hE0
  obtain ⟨ρ', hρ', hlam, harea, hnorm⟩ := GlobalTheory.T.exists_algebraicNumbers_extension_conj_vacuum_normSq D cc dl t0 hcrv ht0 M ρ hD
  have hnorm' := hnorm a b _ _ _ _ (sdL L hL) (sdL' L' hL') sd0 sd0' hev _ _ hmv hE0 hco
  have hdiff : ∀ (c₁ : ℕ) (x : HomE X.E a b), 0 < c₁ → Differentiable ℂ fun z => κ * A.thInd S L L' c₁ x z := by
    intro c₁ x h₁
    have h2 := (GlobalTheory.T.conj_torsionTranslateCombination_entire_gaussianGrowth D cc dl t0 hcrv ht0 a b _ _ (sdL L hL) (sdL' L' hL') hev _ _ _ hmv
      (GlobalTheory.T.cosetIndicatorTheta_torsionTranslates D X s cc dl B χ cD hX hs hcrv a b S L L' c₁ x hL hL' h₁) ρ').1
    have h3 := diff_back s _ h2
    rwa [toHost_back] at h3

  haveI := (GlobalTheory.T.finite_semilocal_hom_lattice_classes_mod X.E a b S L L' cA (c * c') hL.1 hL'.1 hcA (Nat.mul_pos hc hc')).1
  let Qt := ↥(divLat cA (homAt S L L')) ⧸ (mulLat (c * c') (homAt S L L')).comap (divLat cA (homAt S L L')).subtype
  letI : Fintype Qt := Fintype.ofFinite Qt
  let rep : Qt → ↥(divLat cA (homAt S L L')) := Function.surjInv (Submodule.Quotient.mk_surjective _)
  have hsum : ∀ {Y : Type} [AddCommMonoid Y] (f : HomE X.E a b → Y),
      latSum (divLat cA (homAt S L L')) (mulLat (c * c') (homAt S L L')) f = ∑ q : Qt, f (rep q) := fun f =>
    finsum_eq_sum_of_fintype _
  have hrep : ∀ q, ((rep q : HomE X.E a b)) ∈ divLat (cA * (c * c')) (homAt S L L') := by
    intro q
    have h1 : ((cA : ℕ) : 𝓞 X.E) • (rep q : HomE X.E a b) ∈ homAt S L L' := (rep q).2
    show (((cA * (c * c') : ℕ)) : 𝓞 X.E) • (rep q : HomE X.E a b) ∈ homAt S L L'
    rw [mul_comm cA, Nat.cast_mul, mul_smul]
    exact Submodule.smul_mem _ _ h1
  let J : (DVar X.Tau a b →₀ ℕ) → X.K := fun m => ∑ q : Qt, Ξ (rep q) * A.jetK S L L' (c * c') (rep q) m
  have hker : kerOf (thDistC A S SB (cA * (c * c')) sel mU mI lam lam' fun τ => GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.lastEntry (nu τ)) S cA (c * c')
      L fr L' fr' Ξ = (muInvDet sel SB mU mI L fr * (muInvDet sel SB mU mI L' fr')⁻¹) •
        jetOp lam lam' J fun τ => GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.lastEntry (nu τ) := by
    unfold kerOf
    rw [hsum, jetOp_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    unfold thDistC
    rw [if_pos ⟨Dvd.intro_left _ rfl, hrep q⟩, smul_comm]

  let F : VCx X.Tau a b → ℂ := fun z => ∑ q : Qt, s.σ₀ (Ξ (rep q)) * (κ * A.thInd S L L' (c * c') (rep q) z)
  have hJF : ∀ e, (∀ τ, ((degAt e τ : ℕ) : ℤ) = ∑ i, (nu τ).w i) → s.σ₀ (J e) = jetC A.cD F e := by
    intro e he
    rw [GlobalTheory.T.jet_finset_linear_combination X.Tau a b A.cD Qt Finset.univ _ _ (fun q _ => hdiff _ _ (Nat.mul_pos hc hc')) e, map_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [map_mul, jetC_const_mul _ _ _ (hdiff _ _ (Nat.mul_pos hc hc'))]
    congr 1
    have h1 := hJ L L' (c * c') (rep q) ⟨hL, hL', Nat.mul_pos hc hc', Dvd.intro_left _ rfl, hrep q⟩ e (fun τ => by
      refine Eq.trans ?_ (he τ)
      unfold degAt
      congr)
    unfold Amb.jetK desc
    rw [dif_pos h1]
    exact h1.choose_spec
  obtain ⟨R, hRc, hR⟩ := GlobalTheory.T.exists_finset_latSum_thInd_eq_sum X A a b S L L' cA c c' (fun x => s.σ₀ (Ξ x)) hInd hL hL' hcA hc hc'
    (fun x hx => hΞ.1 x fun h => hx (by rw [h, map_zero])) (fun x y hy => by rw [hΞ.2.1 x y hy])
  have hF : toHost s F = fun w => ∑ x ∈ R, s.σ₀ (Ξ x) * toHost s (fun z => κ * A.thInd S L L' c x z) w := by
    funext w
    have h1 := hR fun τ => w (s.iT τ)
    rw [hsum] at h1
    show ∑ q : Qt, s.σ₀ (Ξ (rep q)) * (κ * _) = ∑ x ∈ R, s.σ₀ (Ξ x) * (κ * _)
    simp only [mul_left_comm _ κ, ← Finset.mul_sum]
    exact congrArg _ h1
  have hKQ : ∀ k, s.σ₀ k ∈ TaylorLogMetric.Qbar := fun k => (hρ' _ (hK k)).1
  have hpres := GlobalTheory.T.presentation_closed_under_bounded_combination D (TaylorLogMetric.tor0 D cc dl) a b (s.lat L) (s.lat L') _ _ R (fun x => s.σ₀ (Ξ x)) _ _ β hβ
    (fun x _ => GlobalTheory.T.cosetIndicatorTheta_torsionTranslates D X s cc dl B χ cD hX hs hcrv a b S L L' c x hL hL' hc)
    (fun x _ => ⟨hKQ _, fun ρ₁ => by
      have h1 := hΞ.2.2 ((ρ₁ : TaylorLogMetric.Qbar →+* ℂ).comp (s.σ₀.codRestrict TaylorLogMetric.Qbar hKQ)) x
      have h2 := cj_coe TaylorLogMetric.Qbar ρ₁ ⟨s.σ₀ (Ξ x), hKQ _⟩
      exact h2 ▸ h1⟩)
  rw [← hF] at hpres
  obtain ⟨hFd, hFQ, F', hF'd, hF't, hF'b⟩ := GlobalTheory.T.conj_torsionTranslateCombination_entire_gaussianGrowth D cc dl t0 hcrv ht0 a b _ _ (sdL L hL) (sdL' L' hL') hev _ _ _ hmv hpres ρ'
  rw [hnorm', hlam] at hF'b
  set ar := TaylorLogMetric.area (TaylorLogMetric.lamConj M ρ (TaylorLogMetric.lamOf D cc dl)) with har
  let cD' : X.Tau → ℂ := fun τ => ρ (TaylorLogMetric.liftM M (cD (s.iT τ)))
  have hcD' : ∀ τ, cD' τ ≠ 0 := fun τ => by
    have h1 : TaylorLogMetric.liftM M (cD (s.iT τ)) = ⟨cD (s.iT τ), hcM _⟩ := dif_pos (hcM _)
    show ρ _ ≠ 0
    rw [h1, map_ne_zero]
    exact fun h => hc0 _ (congrArg Subtype.val h)
  have hJ' : ∀ e, (∀ τ, ((degAt e τ : ℕ) : ℤ) = ∑ i, (nu τ).w i) →
      σ (J e) = jetC cD' (fun z : VCx X.Tau a b => F' fun τ => z (s.iT.symm τ)) e := by
    intro e he
    have h1 : σ (J e) = StandardLatticesGL3.cj TaylorLogMetric.Qbar ρ' (s.σ₀ (J e)) := by
      rw [(hρ' _ (hK _)).2]
      exact (cj_coe M ρ ⟨_, hK _⟩).symm
    rw [h1, hJF e he, ← toHost_back s F]
    unfold jetC
    rw [GlobalTheory.T.derivAtZero_reindex_eq_taylor_coefficient D X.Tau s.iT a b _ hFd, GlobalTheory.T.derivAtZero_reindex_eq_taylor_coefficient D X.Tau s.iT a b _ hF'd, hF't]
    have hq : ∀ τ, cD (s.iT τ) ∈ TaylorLogMetric.Qbar := fun τ => (hρ' _ (hcM _)).1
    have h2 := cj_coe TaylorLogMetric.Qbar ρ' ((e.prod fun k n => (⟨cD (s.iT k.1), hq _⟩ : TaylorLogMetric.Qbar) ^ n) *
      ((e.prod fun _ n => (n.factorial : TaylorLogMetric.Qbar)) * ⟨_, hFQ (Finsupp.equivMapDomain (s.iT.prodCongr (Equiv.refl (Fin b × Fin a))) e)⟩))
    have h3 : ∀ τ, ρ' ⟨cD (s.iT τ), hq τ⟩ = cD' τ := fun τ => (cj_coe TaylorLogMetric.Qbar ρ' ⟨_, hq τ⟩).symm.trans (hρ' _ (hcM _)).2
    refine Eq.trans (congrArg _ ?_) (h2.trans ?_)
    · simp only [Finsupp.prod, IntermediateField.coe_mul, IntermediateField.coe_prod, IntermediateField.coe_pow]
      simp [hA, ambOf]
    · simp only [Finsupp.prod, map_mul, map_prod, map_pow, map_natCast, h3]
      rw [← cj_coe TaylorLogMetric.Qbar ρ']
  have hr : 0 < Real.pi / ar := div_pos Real.pi_pos harea
  have hblock := hB X.Tau a b hab.le lam nu lam' hst (fun h => absurd h hab.ne) (fun _ => Real.sqrt (Real.pi / ar))
    (fun τ => Real.exp (logOmAt B cD M ρ (s.iT τ))) cD' (fun _ => Real.sqrt_pos.2 hr) (fun _ => Real.exp_pos _) (fun τ => by
      have h1 : 0 < ‖cD' τ‖ := norm_pos_iff.2 (hcD' τ)
      unfold logOmAt TaylorLogMetric.logMet
      rw [Real.exp_neg, one_div, inv_inv, Real.exp_log (by show 0 < Real.pi * ‖cD' τ‖ ^ 2 / ar; positivity), norm_mul, mul_pow,
        Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hr.le]
      show _ = Real.pi * ‖cD' τ‖ ^ 2 / ar
      ring)
    (fun z : VCx X.Tau a b => F' fun τ => z (s.iT.symm τ))
    (β * (c : ℝ) ^ (2 * (Module.finrank ℚ X.E * a * b)) * Real.sqrt (supConst D a b) * Real.exp (logThAt B M ρ a b / 2))
    (diff_back s _ hF'd) (fun z => by
      have hsup : 0 ≤ supConst D a b := by
        unfold supConst Host.rdE
        positivity
      refine abs_le_of_sq_le_sq' ?_ (by positivity) |>.2
      refine (hF'b _).trans ?_
      have e1 : Real.pi * (∑ τ, ∑ i, ∑ j, ‖z (s.iT.symm τ) i j‖ ^ 2) / ar =
          GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.unitSq (fun _ => Real.sqrt (Real.pi / ar)) z := by
        unfold GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.unitSq
        rw [s.iT.symm.sum_comp fun τ => ∑ i, ∑ j, ‖z τ i j‖ ^ 2]
        simp only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hr.le, ← Finset.mul_sum]
        ring
      have e2 : ∀ y : ℝ, Real.exp (y / 2) ^ 2 = Real.exp y := fun y => by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      have b1 : (R.card : ℝ) * β * (c : ℝ) ^ (Module.finrank ℚ X.E * a * b) ≤ β * (c : ℝ) ^ (2 * (Module.finrank ℚ X.E * a * b)) := by
        have h1 : (R.card : ℝ) ≤ (c : ℝ) ^ (Module.finrank ℚ X.E * a * b) := by exact_mod_cast hRc
        calc _ ≤ (c : ℝ) ^ (Module.finrank ℚ X.E * a * b) * β * (c : ℝ) ^ (Module.finrank ℚ X.E * a * b) := by gcongr
          _ = _ := by ring
      have b2 := Real.le_exp_log (TaylorLogMetric.normSq D (TaylorLogMetric.torConj D (TaylorLogMetric.tor0 D cc dl) M ρ)
        (TaylorLogMetric.La D (TaylorLogMetric.torConj D (TaylorLogMetric.tor0 D cc dl) M ρ) (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b)) (TaylorLogMetric.fnConj D M ρ (B.thZero a b)))
      rw [e1]
      calc _ ≤ (β * (c : ℝ) ^ (2 * (Module.finrank ℚ X.E * a * b))) ^ 2 * (supConst D a b * Real.exp (logThAt B M ρ a b) *
            Real.exp (GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.unitSq (fun _ => Real.sqrt (Real.pi / ar)) z)) := by
            refine mul_le_mul (pow_le_pow_left₀ (by positivity) b1 2) ?_ ?_ (by positivity)
            · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left b2 hsup) (Real.exp_pos _).le
            · refine mul_nonneg (mul_nonneg hsup ?_) (Real.exp_pos _).le
              unfold TaylorLogMetric.normSq
              exact MeasureTheory.integral_nonneg fun _ => by positivity
        _ = _ := by
            rw [mul_pow _ (Real.exp _), mul_pow _ (Real.exp _), mul_pow _ (Real.sqrt _), e2, e2, Real.sq_sqrt hsup]
            ring)
  have hbc := GlobalTheory.T.jetOperatorBound_at_embedding_of_complexOpNormSq X.K σ X.Tau a b lam nu lam' hst (GlobalTheory.T.jetMap_coeffSpace_of_jetStepPartitionTriples X.K X.Tau a b hab lam nu lam' hst)
    (GlobalTheory.T.jetMap_coeffSpace_of_jetStepPartitionTriples ℂ X.Tau a b hab lam nu lam' hst) J _ hJ' _ hblock
  intro x
  rw [hker, LinearMap.smul_apply, sqAt_smul]
  refine le_trans ?_ (hbc x)
  refine mul_le_of_le_one_left (sqAt_nonneg _ _ _) ?_
  exact pow_le_one₀ (norm_nonneg _) hsc

end GlobalTheory.ColNorms
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftModelHolomorphicOverReflexField
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

namespace GlobalTheory.LowRow

theorem isEnum_unique {n : ℕ} {S : SPar} {lam lam' : Fin n → ℝ} {ε ε' : Fin n → Bool}
    (h : IsEnum S lam ε) (h' : IsEnum S lam' ε') : lam = lam' ∧ ε = ε' := by
  obtain ⟨hA, q, hq, hS⟩ := h
  obtain ⟨hA', q', hq', hS'⟩ := h'
  have hqA : StrictAnti q := fun a b hab => by
    have := hA hab; rw [hq, hq] at this; exact_mod_cast this
  have hqA' : StrictAnti q' := fun a b hab => by
    have := hA' hab; rw [hq', hq'] at this; exact_mod_cast this
  have himg : Finset.univ.image q = Finset.univ.image q' := by
    have e := congrArg (Finset.image Prod.fst) (hS.symm.trans hS')
    simpa [Finset.image_image, Function.comp_def] using e
  have hr : Set.range q = Set.range q' := by
    have := congrArg (fun s : Finset ℚ => (s : Set ℚ)) himg
    simpa [Finset.coe_image] using this
  have hqq : q = q' := (StrictAnti.range_inj hqA hqA').1 hr
  subst hqq
  refine ⟨funext fun a => by rw [hq, hq'], funext fun a => ?_⟩
  have hm : (q a, ε a) ∈ S := by rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
  rw [hS'] at hm
  obtain ⟨b, -, hb⟩ := Finset.mem_image.1 hm
  have hb1 : b = a := hqA.injective (congrArg Prod.fst hb)
  subst hb1
  exact (congrArg Prod.snd hb).symm

theorem parAt_overK {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
    (σ : D.what₂.LL →+* ℂ) (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ) (ρ : D.what₂.Tau) :
    parAt (Wc D i) σ ρ = parAt (Wc D i) (sg0 D A) (lab σ ρ) := by
  have hs : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0
  have hsig : ∀ τ, (Wc D i).sig (tauE D τ) = D.R.sigW ((i : ℕ) + 1) :=
    fun τ => D.sp.W_sigval _ (Nat.le_add_left _ _) i.2 _
  have hl := ((GlobalTheory.GalLift.labels_overK σ).1 hK).2 ρ
  unfold parAt kapAt
  rw [if_pos hl, hs, GlobalTheory.ThetaFiresProbe.lab_fixed, if_pos (GlobalTheory.ThetaFiresProbe.labE_fixed _), hsig ρ, hsig (lab σ ρ)]

theorem model_overK {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
    (σ : D.what₂.LL →+* ℂ) (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ) (ρ : D.what₂.Tau) :
    (R.MW i σ).lam ρ = (R.MW i (sg0 D A)).lam (lab σ ρ) ∧ (R.MW i σ).ε ρ = (R.MW i (sg0 D A)).ε (lab σ ρ) := by
  have h1 := (R.MW i σ).enum ρ
  rw [parAt_overK R i σ hK ρ] at h1
  exact isEnum_unique h1 ((R.MW i (sg0 D A)).enum (lab σ ρ))

theorem holShape_overK : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F →
    ∀ i σ s, IsEmbOverK D σ s → HolShape (R.MW i σ) ∧ ∃ w, WtIs (R.MW i σ) w := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hc i σ s hE
  have hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ := hE.2
  obtain ⟨hH, w0, hw0⟩ := holShape_fixed D G Pl0 T A Ks R hc.models.order i
  have hm := model_overK R i σ hK
  refine ⟨fun ρ => ?_, fun ρ c => w0 (lab σ ρ) c, fun ρ c => ?_⟩
  · have h := hH (lab σ ρ)
    rw [← (hm ρ).1, ← (hm ρ).2] at h
    exact h
  · have h := hw0 (lab σ ρ) c
    unfold extWt at h ⊢
    rw [← (hm ρ).1, ← (hm ρ).2] at h
    exact h

end GlobalTheory.LowRow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftsEquivariantTwistedAndPlainModelsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lifts_equivariant_twisted_and_plain_models : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.phase → R.PGEquiv F → (∀ t g (v : (A3.A.MtildeCSD t).Forms), R.Th t (R.jX t (A3.A.leftGroupActionRight t g v)) = R.gE g (R.Th t (R.jX t v))) ∧ ∀ i t g (v : (A3.A.MtCSD i t).Forms), R.thG i t (R.jV i t (A3.A.leftGroupActionLift i t g v)) = R.gW i (sg0 D A3.A) g (R.thG i t (R.jV i t v)) := by
  first | exact @GlobalTheory.GEqBr.geq_br | exact GlobalTheory.GEqBr.geq_br | (intros; apply GlobalTheory.GEqBr.geq_br <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIntersectionNumberEqGenericRankMulStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleIntersectionNumber_eq_genericRank_mul : ∀ (κ : Type) [Field κ] (Z : Scheme.{0}) [IsIntegral Z] [Algebra κ Γ(Z, ⊤)], IsProjOver (strHom κ Z) → ∀ (ι : Type) [Fintype ι], topologicalKrullDim Z ≤ (Fintype.card ι : ℕ) → ∀ (G : Z.Modules) [GlobalTheory.QCoh.IsFiniteQC G] (P : ι → LB Z), (∀ i, (P i).IsLB) → interNum κ G P = (GlobalTheory.VB.genRank G : ℤ) * interNum κ (structureModule Z) P := by
  first | exact @GlobalTheory.VB.interNum_eq_genRank_mul_of_isProjOver | exact GlobalTheory.VB.interNum_eq_genRank_mul_of_isProjOver | (intros; apply GlobalTheory.VB.interNum_eq_genRank_mul_of_isProjOver <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleTrivialOnFibre
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KTrivJacobson

theorem exists_specializes {R : Type} [CommRing R] {J : Ideal R} (hJ : J ≤ Ideal.jacobson ⊥)
    (p : PrimeSpectrum R) :
    ∃ q : PrimeSpectrum (R ⧸ J), p ⤳ PrimeSpectrum.comap (Ideal.Quotient.mk J) q := by
  obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p.asIdeal p.2.ne_top
  have hJm : J ≤ m := hJ.trans (sInf_le ⟨bot_le, hm⟩)
  have : (⟨m, hm.isPrime⟩ : PrimeSpectrum R) ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk J)) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
    exact hJm
  obtain ⟨q, hq⟩ := this
  refine ⟨q, ?_⟩
  rw [hq, ← PrimeSpectrum.le_iff_specializes]
  exact hpm

theorem kTriv_of_quotient : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (J : Ideal R), J ≤ Ideal.jacobson ⊥ → ∀ (B : Over (Spec (CommRingCat.of R))) [GrpObj B], IsAbelianScheme B → ∀ M : LB B.left, M.IsLB → RelAmple B M → ∀ (Y₀ : Over (Spec (CommRingCat.of (R ⧸ J)))) [GrpObj Y₀] (b : Y₀.left ⟶ B.left), IsGrpPullback Y₀ B (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) b → ∀ N₀ : LB Y₀.left, N₀.IsLB → LBIso N₀ (M.pull b) → KTriv Y₀ N₀ → KTriv B M := by
  intro R _ _ J hJ B _ hB M hM hA Y₀ _ b hb N₀ hN₀ e hK
  have key : ∀ p : Spec (CommRingCat.of R), ∃ U : (Spec (CommRingCat.of R)).Opens, p ∈ U ∧
      KTriv ((Over.pullback U.ι).obj B) (M.pull (pullback.fst B.hom U.ι)) := fun p => by
    obtain ⟨q, hq⟩ := exists_specializes hJ p
    obtain ⟨U, hU, H⟩ := GlobalTheory.KTrivGlob.exists_open hM hN₀ hB hA hb e hK q
    exact ⟨U, hq.mem_open U.2 hU, H⟩
  choose U hU hK using key
  have hL := fun p => pull_isLB hM (pullback.fst B.hom (U p).ι)
  exact GlobalTheory.CoverGlue.kTriv_of_cover _ _ U B _ _
    (top_le_iff.1 fun p _ => TopologicalSpace.Opens.mem_iSup.2 ⟨p, hU p⟩)
    (fun p => isGrpPullback_pullback B (U p).ι) _ _ hM hL (fun p => GlobalTheory.lbIso_refl (hL p)) hB
    (fun p => GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hB (isGrpPullback_pullback B (U p).ι)) hK

end GlobalTheory.KTrivJacobson
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearFormAlternatingOfAdjacentSwapBlocks
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

set_option autoImplicit false

namespace GlobalTheory.FlagPush

theorem perm_submonoid_eq_top_of_adj (k : ℕ) (T : Submonoid (Equiv.Perm (Fin k)))
    (h : ∀ a b : Fin k, (b : ℕ) = a + 1 → Equiv.swap a b ∈ T) : T = ⊤ := by
  cases k with
  | zero =>
    rw [eq_top_iff]
    intro x _
    have : x = 1 := Subsingleton.elim _ _
    rw [this]; exact T.one_mem
  | succ n =>
    rw [eq_top_iff, ← Equiv.Perm.mclosure_swap_castSucc_succ, Submonoid.closure_le]
    rintro _ ⟨i, rfl⟩
    exact h _ _ (by simp)

theorem alternating_of_adjacent_swap (ι : Type) [Fintype ι] (m : ι → ℕ)
    (L : MvPolynomial (Root m) ℝ →ₗ[ℝ] ℝ)
    (hL : ∀ (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 → ∀ Q,
      L (rename (Equiv.swap (⟨τ, a⟩ : Root m) ⟨τ, b⟩) Q) = - L Q)
    (w : ∀ τ, Equiv.Perm (Fin (m τ))) (Q : MvPolynomial (Root m) ℝ) :
    L (rename (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) Q) =
      (((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) : ℝ) * L Q := by
  let S : Submonoid (∀ τ, Equiv.Perm (Fin (m τ))) :=
    { carrier := {w | ∀ Q, L (rename (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) Q) =
        (((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) : ℝ) * L Q}
      one_mem' := by
        intro Q
        have : (fun x : Root m => (⟨x.1, (1 : ∀ τ, Equiv.Perm (Fin (m τ))) x.1 x.2⟩ : Root m)) = id := by
          funext x; rfl
        rw [this, rename_id]
        simp
      mul_mem' := by
        intro v w hv hw Q
        have : (fun x : Root m => (⟨x.1, (v * w) x.1 x.2⟩ : Root m)) =
            (fun x : Root m => (⟨x.1, v x.1 x.2⟩ : Root m)) ∘
              (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) := by
          funext x; rfl
        simp only [Set.mem_setOf_eq] at hv hw ⊢
        rw [this, ← rename_rename, hv, hw]
        simp only [Pi.mul_apply, map_mul, Finset.prod_mul_distrib, Units.val_mul, Int.cast_mul]
        ring }
  have hS : S = ⊤ := by
    have htop : (⊤ : Submonoid (∀ τ, Equiv.Perm (Fin (m τ)))) =
        Submonoid.pi Set.univ (fun τ => (⊤ : Submonoid (Equiv.Perm (Fin (m τ))))) := by
      ext x; simp [Submonoid.mem_pi]
    rw [eq_top_iff, htop, ← Submonoid.iSup_map_mulSingle, iSup_le_iff]
    intro τ
    rw [Submonoid.map_le_iff_le_comap]
    rw [perm_submonoid_eq_top_of_adj (m τ) (Submonoid.comap (MonoidHom.mulSingle (fun τ => Equiv.Perm (Fin (m τ))) τ) S) ?_]
    intro a b hab Q
    have hf : (fun x : Root m => (⟨x.1, (MonoidHom.mulSingle (fun τ => Equiv.Perm (Fin (m τ))) τ
        (Equiv.swap a b)) x.1 x.2⟩ : Root m)) = Equiv.swap (⟨τ, a⟩ : Root m) ⟨τ, b⟩ := by
      funext ⟨σ, c⟩
      by_cases h : σ = τ
      · subst h
        simp only [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same]
        rw [Equiv.swap_apply_def, Equiv.swap_apply_def]
        by_cases h1 : c = a
        · subst h1; simp
        · by_cases h2 : c = b
          · subst h2; simp [h1]
          · simp [h1, h2]
      · simp only [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne h, Equiv.Perm.coe_one, id]
        rw [Equiv.swap_apply_of_ne_of_ne]
        · intro e; exact h (congrArg Sigma.fst e)
        · intro e; exact h (congrArg Sigma.fst e)
    have hab' : a ≠ b := by
      intro e; subst e; omega
    have hs : (∏ σ, Equiv.Perm.sign ((MonoidHom.mulSingle (fun τ => Equiv.Perm (Fin (m τ))) τ
        (Equiv.swap a b)) σ)) = -1 := by
      have : ∀ σ, Equiv.Perm.sign ((MonoidHom.mulSingle (fun τ => Equiv.Perm (Fin (m τ))) τ
          (Equiv.swap a b)) σ) = (Pi.mulSingle τ (Equiv.Perm.sign (Equiv.swap a b)) : ι → ℤˣ) σ := by
        intro σ
        by_cases h : σ = τ
        · subst h; simp
        · simp [Pi.mulSingle_eq_of_ne h]
      simp only [this, Finset.prod_pi_mulSingle', Finset.mem_univ, if_true]
      exact Equiv.Perm.sign_swap hab'
    show L _ = _
    rw [hf, hs, hL τ a b hab Q]
    simp
  have hw : w ∈ S := by rw [hS]; trivial
  exact hw Q

end GlobalTheory.FlagPush
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralComplexInvPowAddNormSqStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_complex_inv_pow_add_norm_sq : ∀ (m : ℕ) (a : ℝ), 0 < a → ∫⁻ z : ℂ, ENNReal.ofReal (((a + ‖z‖ ^ 2) ^ (m + 2))⁻¹) = ENNReal.ofReal (Real.pi / ((m + 1) * a ^ (m + 1))) := by
  first | exact @GlobalTheory.RadialIntegral.lintegral_inv_pow_add_norm_sq | exact GlobalTheory.RadialIntegral.lintegral_inv_pow_add_norm_sq | (intros; apply GlobalTheory.RadialIntegral.lintegral_inv_pow_add_norm_sq <;> assumption)
end

