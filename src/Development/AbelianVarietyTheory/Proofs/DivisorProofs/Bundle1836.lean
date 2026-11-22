import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1712
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1783
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1779
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1678
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1796
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixTwoByTwoFinTranspose
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1803
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1702
import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1219
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1220
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0222
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1782
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1804
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewSelfDualLatticeLocalisedAtPlace
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix GlobalTheory.VacAny

namespace GlobalTheory.SkewLocDual

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem form_smul_left (σ : E →ₐ[F] E) {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (c : E) (x y : Fin d → E) :
    form σ J (c • x) y = c * form σ J x y := by
  simp [form, smul_dotProduct]

theorem form_add_right (σ : E →ₐ[F] E) {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (x y z : Fin d → E) :
    form σ J x (y + z) = form σ J x y + form σ J x z := by
  have h : (fun i => σ ((y + z) i)) = (fun i => σ (y i)) + fun i => σ (z i) := funext fun i => by simp
  simp only [form, h, Matrix.mulVec_add, dotProduct_add]

theorem form_zero_right (σ : E →ₐ[F] E) {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (x : Fin d → E) :
    form σ J x 0 = 0 := by
  have h : (fun i => σ ((0 : Fin d → E) i)) = 0 := funext fun i => by simp
  simp only [form, h, Matrix.mulVec_zero, dotProduct_zero]

theorem form_smul_right (σ : E →ₐ[F] E) {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (o : 𝓞 E) (x y : Fin d → E) :
    form σ J x (o • y) = σ (o : E) * form σ J x y := by
  have h : (fun i => σ ((o • y) i)) = σ (o : E) • fun i => σ (y i) := funext fun i => by
    simp [Algebra.smul_def]
  simp only [form, h, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem isIntegral_algebraMap_int (a : 𝓞 F) : IsIntegral ℤ (algebraMap F E (a : F)) :=
  (NumberField.RingOfIntegers.isIntegral_coe a).map (algebraMap F E).toIntAlgHom

theorem isIntegral_conj (σ : E →ₐ[F] E) (o : 𝓞 E) : IsIntegral ℤ (σ (o : E)) :=
  (NumberField.RingOfIntegers.isIntegral_coe o).map (σ : E →+* E).toIntAlgHom

end GlobalTheory.SkewLocDual

open GlobalTheory.SkewLocDual in
theorem GlobalTheory.SkewLocDual.exists_smul_mem_of_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) {d r s : ℕ} (Y : Spc F E d), Y.IsSkew σ B r s → ∀ (v : Pl F) (u : Fin d → E),
    (∀ y ∈ Y.L, ∃ t : 𝓞 F, t ∉ v.asIdeal ∧ IsIntegral ℤ (algebraMap F E (t : F) * form σ Y.J u y)) →
    ∃ t : 𝓞 F, t ∉ v.asIdeal ∧ algebraMap F E (t : F) • u ∈ Y.L := by
  intro F E _ _ _ _ _ σ B d r s Y hY v u hu
  classical
  haveI := v.isPrime
  obtain ⟨S, hS⟩ := hY.lat.fg
  have hgen : ∀ y ∈ S, y ∈ Y.L := fun y hy => hS ▸ Submodule.subset_span hy
  choose! T hT using fun y (hy : y ∈ S) => hu y (hgen y hy)
  have ht : (∏ y ∈ S, T y) ∉ v.asIdeal := by
    rw [Ideal.IsPrime.prod_mem_iff]
    push_neg
    exact fun y hy => (hT y hy).1
  have key : ∀ y ∈ Y.L,
      IsIntegral ℤ (algebraMap F E ((∏ y ∈ S, T y : 𝓞 F) : F) * form σ Y.J u y) := by
    rw [← hS]
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      have hsplit : algebraMap F E ((∏ y ∈ S, T y : 𝓞 F) : F) =
          algebraMap F E ((∏ y ∈ S.erase x, T y : 𝓞 F) : F) * algebraMap F E (T x : F) := by
        rw [← map_mul, ← Finset.prod_erase_mul S T hx]; rfl
      rw [hsplit, mul_assoc]
      exact (isIntegral_algebraMap_int _).mul (hT x hx).2
    | zero => simpa [form_zero_right] using (isIntegral_zero : IsIntegral ℤ (0 : E))
    | add x y _ _ hx hy => rw [form_add_right, mul_add]; exact hx.add hy
    | smul o x _ hx => rw [form_smul_right, mul_left_comm]; exact (isIntegral_conj σ o).mul hx
  refine ⟨∏ y ∈ S, T y, ht, (hY.dual _).2 fun x hx o => ?_⟩
  rw [form_smul_left]
  exact Algebra.isIntegral_trace ((NumberField.RingOfIntegers.isIntegral_coe o).mul (key x hx))
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareBottomPairsWeightsEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.BottomWeights

theorem mul_n_eq {D : D7} {N N' : ℕ} (χ : HeckeU D N) (χ' : HeckeU D N') (e e' : ℤ)
    (h : ∀ x, χ.f x ^ e = χ'.f x ^ e') (τ : D.what₂.Tau) : e * χ.n τ = e' * χ'.n τ := by
  have hc := GlobalTheory.SplitWeight.exps_eq_zero (Formalism.L2.Host.embTau D) (GlobalTheory.SplitWeight.embTau_inj D)
    (GlobalTheory.SplitWeight.embTau_ne_conj D) (fun τ => e * χ.n τ - e' * χ'.n τ) (fun a ha => by
      set u := Units.mk0 a ha
      set φ := Formalism.L2.Host.embTau D
      have hne : ∀ τ, φ τ a ≠ 0 := fun τ => by simpa using ha
      have hu : ∀ τ, φ τ a / ((‖φ τ a‖ : ℝ) : ℂ) ≠ 0 := fun τ =>
        div_ne_zero (hne τ) (by exact_mod_cast norm_ne_zero_iff.2 (hne τ))
      have hA : ((χ.f (Units.map (inc D).toMonoidHom u) : ℂˣ) : ℂ) *
          ∏ τ, (φ τ a / ((‖φ τ a‖ : ℝ) : ℂ)) ^ (χ.n τ) = 1 := χ.aut u
      have hB : ((χ'.f (Units.map (inc D).toMonoidHom u) : ℂˣ) : ℂ) *
          ∏ τ, (φ τ a / ((‖φ τ a‖ : ℝ) : ℂ)) ^ (χ'.n τ) = 1 := χ'.aut u
      have hE := congrArg Units.val (h (Units.map (inc D).toMonoidHom u))
      simp only [Units.val_zpow_eq_zpow_val] at hE
      rw [eq_inv_of_mul_eq_one_left hA, eq_inv_of_mul_eq_one_left hB, inv_zpow, inv_zpow, inv_inj,
        ← Finset.prod_zpow, ← Finset.prod_zpow] at hE
      simp_rw [zpow_sub₀ (hu _), Finset.prod_div_distrib, mul_comm e, mul_comm e', zpow_mul]
      rw [hE]
      exact div_self (Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ (zpow_ne_zero _ (hu τ))))
  exact sub_eq_zero.1 (congrFun hc τ)

theorem isBottom_n_eq : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (t : T) (i j : Fin D.R.m)
    (𝔪 : Ideal (𝓞 D.host.E)) {δ t0 : ℂ} {Q : ℕ} (P P' : Pair D ⊤ δ t0 Q), IsBottom G t i j 𝔪 P P' → P'.n = P.n := by
  intro D T Lc sc G t i j 𝔪 δ t0 Q P P' h
  funext τ
  have h1 := mul_n_eq P.W.chV' P'.W.chV' P.W.ep' P'.W.ep' (fun x => (h.chars.2 x).trans (h.chars'.2 x).symm) τ
  have h2 := P.wt τ
  have h3 := P'.wt τ
  have h4 : P'.d = P.d := h.rank.2.2.2
  omega

end GlobalTheory.BottomWeights

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdditiveCharacterProductFormula
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.AdeleCharProd

variable {F : Type} [Field F] [NumberField F]

lemma isOpen_intV (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (HeightOneSpectrum.adicCompletionIntegers F v : Set (HeightOneSpectrum.adicCompletion F v)) :=
  Valued.isOpen_valuationSubring _

def ofInt (q : ∀ v : HeightOneSpectrum (𝓞 F), HeightOneSpectrum.adicCompletionIntegers F v) : Af F :=
  RestrictedProduct.structureMap _ _ _ q

lemma continuous_ofInt : Continuous (ofInt (F := F)) :=
  (RestrictedProduct.isOpenEmbedding_structureMap (fun v => isOpen_intV (F := F) v)).continuous

lemma ofInt_add (p q : ∀ v : HeightOneSpectrum (𝓞 F), HeightOneSpectrum.adicCompletionIntegers F v) :
    ofInt (p + q) = ofInt p + ofInt q := by
  apply RestrictedProduct.ext; intro w; rfl

open Classical in
lemma ofInt_single (v : HeightOneSpectrum (𝓞 F)) (t : HeightOneSpectrum.adicCompletionIntegers F v) :
    ofInt (Pi.single v t) = singleFin v (t : Fv F v) := by
  apply RestrictedProduct.ext; intro w
  by_cases h : w = v
  · subst h
    show ((Pi.single w t : ∀ v : HeightOneSpectrum (𝓞 F), HeightOneSpectrum.adicCompletionIntegers F v) w : Fv F w) = _
    rw [Pi.single_eq_same]
    exact (RestrictedProduct.single_eq_same _ w (t : Fv F w)).symm
  · show ((Pi.single v t : ∀ v : HeightOneSpectrum (𝓞 F), HeightOneSpectrum.adicCompletionIntegers F v) w : Fv F w) = _
    rw [Pi.single_eq_of_ne h]
    exact (RestrictedProduct.single_eq_of_ne _ (t : Fv F v) h).symm

end GlobalTheory.AdeleCharProd

namespace GlobalTheory.AdeleCharProd

variable {F : Type} [Field F] [NumberField F]

lemma psiLoc_int {ψ : AddChar (AF F) ℂ} {v : Pl F} (hv : PsiUnr ψ v) {t : Fv F v}
    (ht : t ∈ HeightOneSpectrum.adicCompletionIntegers F v) : psiLoc ψ v t = 1 := by
  have := ((hv 1).2 (one_mem _)) t ht
  simpa using this

open Classical in
lemma psi_ofInt_single (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))
    (t : HeightOneSpectrum.adicCompletionIntegers F v) (h : PsiUnr ψ v ∨ t = 0) :
    ψ (LinearMap.inr F (Ainf F) (Af F) (ofInt (Pi.single v t))) = 1 := by
  classical
  rw [ofInt_single]
  rcases h with h | h
  · exact psiLoc_int h t.2
  · subst h
    have h0 : (LinearMap.inr F (Ainf F) (Af F)) ((singleFin v) ((0 : HeightOneSpectrum.adicCompletionIntegers F v) : Fv F v)) = (0 : AF F) := by
      simp; rfl
    rw [h0]; exact AddChar.map_zero_eq_one ψ

open Classical in

lemma psi_ofInt (ψ : AddChar (AF F) ℂ) (hc : Continuous ψ)
    (q : ∀ v : HeightOneSpectrum (𝓞 F), HeightOneSpectrum.adicCompletionIntegers F v)
    (hq : ∀ v, PsiUnr ψ v ∨ q v = 0) :
    ψ (LinearMap.inr F (Ainf F) (Af F) (ofInt q)) = 1 := by
  set g : (∀ v : HeightOneSpectrum (𝓞 F), HeightOneSpectrum.adicCompletionIntegers F v) → ℂ :=
    fun p => ψ (LinearMap.inr F (Ainf F) (Af F) (ofInt p)) with hg
  have gc : Continuous g := by
    refine hc.comp ?_
    refine Continuous.comp ?_ continuous_ofInt
    exact (continuous_const.prodMk continuous_id)
  let tr : Finset (HeightOneSpectrum (𝓞 F)) → ∀ v : HeightOneSpectrum (𝓞 F), HeightOneSpectrum.adicCompletionIntegers F v :=
    fun T => ∑ v ∈ T, Pi.single v (q v)
  have htr : Tendsto tr atTop (𝓝 q) := by
    rw [tendsto_pi_nhds]; intro w
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop {w}] with T hT
    have hw : w ∈ T := hT (Finset.mem_singleton_self w)
    simp only [tr, Finset.sum_apply]
    rw [Finset.sum_eq_single w]
    · simp
    · intro b _ hb; simp [Pi.single_eq_of_ne' hb]
    · intro h; exact absurd hw h
  have h1 : ∀ T, g (tr T) = 1 := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      have h0 : ofInt (F := F) 0 = 0 := by apply RestrictedProduct.ext; intro w; rfl
      simp only [g, tr, Finset.sum_empty, h0, map_zero]; exact AddChar.map_zero_eq_one ψ
    | insert a T ha ih =>
      have hmul : ∀ p p', g (p + p') = g p * g p' := by
        intro p p'; simp only [g, ofInt_add, map_add]; exact AddChar.map_add_eq_mul _ _ _
      have e : tr (insert a T) = Pi.single a (q a) + tr T := by simp only [tr, Finset.sum_insert ha]
      rw [e, hmul, ih, mul_one]; exact psi_ofInt_single ψ a (q a) (hq a)
  have := gc.continuousAt.tendsto.comp htr
  have h2 : Tendsto (g ∘ tr) atTop (𝓝 1) := by
    simp only [Function.comp_def, h1]; exact tendsto_const_nhds
  exact tendsto_nhds_unique this h2

end GlobalTheory.AdeleCharProd

namespace GlobalTheory.AdeleCharProd

variable {F : Type} [Field F] [NumberField F]

open Classical in

lemma finite_decomp (ψ : AddChar (AF F) ℂ) (hunr : ∀ᶠ v in cofinite, PsiUnr ψ v) (x : Af F) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 F)))
      (q : ∀ v : HeightOneSpectrum (𝓞 F), HeightOneSpectrum.adicCompletionIntegers F v),
      (∀ v, PsiUnr ψ v ∨ q v = 0) ∧ (∀ v ∉ S, PsiUnr ψ v ∧ x v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧
      x = ofInt q + ∑ v ∈ S, singleFin v (x v) := by
  have hev : ∀ᶠ v in cofinite, PsiUnr ψ v ∧ x v ∈ HeightOneSpectrum.adicCompletionIntegers F v :=
    hunr.and x.2
  have hS := Filter.eventually_cofinite.1 hev
  refine ⟨hS.toFinset, fun v => if h : PsiUnr ψ v ∧ x v ∈ HeightOneSpectrum.adicCompletionIntegers F v
    then ⟨x v, h.2⟩ else 0, ?_, ?_, ?_⟩
  · intro v
    by_cases h : PsiUnr ψ v ∧ x v ∈ HeightOneSpectrum.adicCompletionIntegers F v
    · exact Or.inl h.1
    · exact Or.inr (dif_neg h)
  · intro v hv
    by_contra h
    exact hv (hS.mem_toFinset.2 h)
  · apply RestrictedProduct.ext; intro w
    show evalV F w x = evalV F w (_ + _)
    rw [map_add, map_sum]
    have hsame : ∀ (t : Fv F w), evalV F w (singleFin w t) = t := fun t =>
      RestrictedProduct.single_eq_same (fun v => HeightOneSpectrum.adicCompletionIntegers F v) w t
    have hne : ∀ v (t : Fv F v), v ≠ w → evalV F w (singleFin v t) = 0 := fun v t h =>
      RestrictedProduct.single_eq_of_ne (fun v => HeightOneSpectrum.adicCompletionIntegers F v) t (Ne.symm h)
    by_cases hw : PsiUnr ψ w ∧ x w ∈ HeightOneSpectrum.adicCompletionIntegers F w
    · have hwS : w ∉ hS.toFinset := fun h => (hS.mem_toFinset.1 h) hw
      rw [Finset.sum_eq_zero]
      · show x w = ((if h : PsiUnr ψ w ∧ x w ∈ HeightOneSpectrum.adicCompletionIntegers F w
          then (⟨x w, h.2⟩ : HeightOneSpectrum.adicCompletionIntegers F w) else 0 : _) : Fv F w) + 0
        rw [dif_pos hw, add_zero]
      · intro v hv
        apply hne
        rintro rfl; exact hwS hv
    · have hwS : w ∈ hS.toFinset := hS.mem_toFinset.2 hw
      rw [Finset.sum_eq_single w]
      · rw [hsame]
        show x w = ((if h : PsiUnr ψ w ∧ x w ∈ HeightOneSpectrum.adicCompletionIntegers F w
          then (⟨x w, h.2⟩ : HeightOneSpectrum.adicCompletionIntegers F w) else 0 : _) : Fv F w) + x w
        rw [dif_neg hw]; simp
      · intro v _ hv; exact hne v _ hv
      · intro h; exact absurd hwS h

end GlobalTheory.AdeleCharProd

namespace GlobalTheory.AdeleCharProd

variable {F : Type} [Field F] [NumberField F]

lemma addChar_sum {ι : Type} (ψ : AddChar (AF F) ℂ) (S : Finset ι) (f : ι → AF F) :
    ψ (∑ v ∈ S, f v) = ∏ v ∈ S, ψ (f v) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Finset.prod_empty]; exact AddChar.map_zero_eq_one ψ
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

end GlobalTheory.AdeleCharProd

namespace GlobalTheory.AdeleCharProd

theorem psi_eq_inf_mul_finprod : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    (∀ᶠ v in cofinite, PsiUnr ψ v) →
    ∀ a : AF F, ψ a = Complex.exp (-(2 * Real.pi * Complex.I) *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F a) : ℝ)) * ∏ᶠ v, psiLoc ψ v (evFin F v a) := by
  intro F _ _ ψ hstd hunr a
  classical
  obtain ⟨S, q, hq, hout, hx⟩ := finite_decomp ψ hunr a.2
  let j : Af F →+ AF F :=
    { toFun := fun y => (LinearMap.inr F (Ainf F) (Af F) y : AF F)
      map_zero' := by simp; rfl
      map_add' := fun y z => by
        show ((0 : Ainf F), y + z) = ((0 : Ainf F) + 0, y + z)
        rw [add_zero] }
  let i1 : AF F := LinearMap.inl F (Ainf F) (Af F) a.1
  have ha : a = i1 + j a.2 := by
    show a = (a.1 + 0, 0 + a.2)
    rw [add_zero, zero_add]; rfl
  have hinf : ψ i1 = Complex.exp (-(2 * Real.pi * Complex.I) *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F a) : ℝ)) := by
    refine hstd.2.2 _ ?_
    intro u hu
    have hu1 : u.1 = 0 := by
      have : (InfiniteAdeleRing.ringEquiv_mixedSpace F) u.1 = 0 := hu
      exact (map_eq_zero_iff _ (RingEquiv.injective _)).1 this
    show (u.1 * a.1, u.2 * 0) = ((0 : AF F))
    rw [hu1, zero_mul, mul_zero]; rfl
  have hfin : ψ (j a.2) = ∏ v ∈ S, psiLoc ψ v (evFin F v a) := by
    rw [hx, map_add, map_sum, AddChar.map_add_eq_mul, addChar_sum]
    rw [show ψ (j (ofInt q)) = 1 from psi_ofInt ψ hstd.1 q hq, one_mul]
    refine Finset.prod_congr rfl fun v _ => ?_
    rfl
  have hfp : ∏ᶠ v, psiLoc ψ v (evFin F v a) = ∏ v ∈ S, psiLoc ψ v (evFin F v a) := by
    apply finprod_eq_prod_of_mulSupport_subset
    intro v hv
    by_contra hvS
    obtain ⟨h1, h2⟩ := hout v hvS
    exact hv (psiLoc_int h1 h2)
  rw [hfp]
  conv_lhs => rw [ha]
  rw [AddChar.map_add_eq_mul, hinf, hfin]

end GlobalTheory.AdeleCharProd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardCompactUnderWittChart
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.SWLit
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (UA incM ratU)
open GlobalTheory.WeilM (Darboux symp schA thetaSum UG)
open GlobalTheory.SiegelFormula (coord)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SWLink

noncomputable section

namespace GlobalTheory.SWLink

open GlobalTheory.AdelicU in

theorem mem_stabArch_one_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hc : IsCMExt F E σ) {k : ℕ} (J : Matrix (Fin k) (Fin k) E) (w : InfinitePlace F)
    (τ : EmbOver E w) (x : GArch σ J w) :
    x ∈ stabArch σ J w (Formalism.UG.bc (compInf F E w) 1) ↔
      (matHom _ σ J x).1.map (infEmb τ) ∈ Matrix.unitaryGroup (Fin k) ℂ := by
  rw [mem_stabArch, map_one, inv_one, one_mul, mul_one, Matrix.mem_unitaryGroup_iff']
  generalize matHom _ σ J x = y
  change Formalism.UG.cT _ y.1 * 1 * y.1 = 1 ↔ _
  rw [← (Matrix.map_injective (infEmb_bijective hc τ).1).eq_iff]
  beta_reduce
  rw [mul_one, Matrix.map_mul, Frames.map_cT_sigR hc, Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.star_eq_conjTranspose]

open GlobalTheory.AdelicU in

theorem mem_levelAll_std_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hc : IsCMExt F E σ) {k : ℕ} (J : Matrix (Fin k) (Fin k) E) (x : GAd σ J) :
    x ∈ levelAll σ J (stdLattice E k) 1 ↔
      (∀ v i j, compFin F E v ((matHom _ σ J x).1 i j) ∈ intLoc F E v ∧
        compFin F E v ((matHom _ σ J x⁻¹).1 i j) ∈ intLoc F E v) ∧
      ∀ (w : InfinitePlace F) (τ : EmbOver E w),
        (matHom _ σ J x).1.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf τ) ∈ Matrix.unitaryGroup (Fin k) ℂ := by
  rw [mem_levelAll]
  refine and_congr (forall_congr' fun v => ?_) (forall_congr' fun w => ?_)
  · rw [mem_stabLoc_stdLattice_iff, ← map_inv (proj σ J v)]
    simp only [forall_and]
    exact Iff.rfl
  · have hm : ∀ τ : EmbOver E w, (matHom _ σ J x).1.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf τ) =
        (matHom _ σ J (projArch σ J w x)).1.map (infEmb τ) := fun τ => Matrix.ext fun _ _ => rfl
    simp only [hm, ← mem_stabArch_one_iff hc J w, forall_const]

theorem stdK_iff : ∀ (D : D7) (n : ℕ) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E) (T : GL (Fin (n + n)) D.host.E) (κ : UD D J₂ ≃* GlobalTheory.StdUnn.G D n), IsChartW T κ → ∀ K : Subgroup (UD D J₂), IsStdK D.sp.cm.sig T K → ∀ g : UD D J₂, g ∈ K ↔ κ g ∈ GlobalTheory.StdUnn.K D n := by
  intro D n J₂ T κ hκ K hK g
  rw [hK g, ← hκ g, ← hκ g⁻¹, map_inv]
  exact (mem_levelAll_std_iff (GlobalTheory.AdelicU.isCMExt_host D) (GlobalTheory.StdUnn.Jst D n) (κ g)).symm

end GlobalTheory.SWLink

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAdelicAddCharLocalComponentNeOneStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped GlobalTheory.VacAny

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardTraceAdelicAddChar_localComponent_ne_one : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ →
    ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, GlobalTheory.VacAny.psiV ψ v ≠ 1 := by
  first | exact @GlobalTheory.PsiNontriv.psiV_ne_one | exact GlobalTheory.PsiNontriv.psiV_ne_one | (intros; apply GlobalTheory.PsiNontriv.psiV_ne_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumInnerIntegralEq
section
noncomputable section

open MeasureTheory GlobalTheory.Orb GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary
open Formalism.REAL (UJ KG toM toMK muK)
open GlobalTheory.PsCo.Pc1
open scoped InnerProductSpace

namespace GlobalTheory.PsCo.Pc3

theorem sum_inner_integral_eq {X U ι : Type} [MeasurableSpace X] [NormedAddCommGroup U] [InnerProductSpace ℂ U]
    [CompleteSpace U] [Fintype ι] (ν : Measure X) (f : X → ℂ) (ρ : X → U →L[ℂ] U) (e : ι → U) (T : U →L[ℂ] U)
    (h : ∀ v, Integrable (fun x => f x • ρ x v) ν ∧ T v = ∫ x, f x • ρ x v ∂ν) :
    ∑ j, ⟪e j, T (e j)⟫_ℂ = ∫ x, f x * ∑ j, ⟪e j, ρ x (e j)⟫_ℂ ∂ν := by
  have h1 : ∀ j, ⟪e j, T (e j)⟫_ℂ = ∫ x, ⟪e j, f x • ρ x (e j)⟫_ℂ ∂ν := fun j => by
    rw [(h (e j)).2, integral_inner (h (e j)).1]
  simp only [h1]
  rw [← integral_finsetSum _ fun j _ => (h (e j)).1.const_inner (e j)]
  simp only [inner_smul_right, Finset.mul_sum]

theorem stTr_of_range_steps (hF : UFin) (hS : RangeShape) (hK : RangeK) (hT : TraceSum) : StTr := by
  intro n ε μ _ U _ _ _ π hπ hirr d
  obtain ⟨L, hL, hmem, -⟩ := hF n ε U π hπ hirr d
  refine ⟨fun g => ∑ j, ⟪(stdOrthonormalBasis ℂ L j : U), π g (stdOrthonormalBasis ℂ L j : U)⟫_ℂ, ?_, ?_, ?_⟩
  · exact continuous_finsetSum _ fun j _ => continuous_const.inner (hπ.continuous_apply _)
  · intro φ hφ
    obtain ⟨hop, hr⟩ := hS n ε μ U π hπ d φ hφ
    have := hT U L _ fun u => hmem _ (hr u).1
    rwa [sum_inner_integral_eq μ (fun g => φ (toM g)) (fun g => π g) _ _ hop] at this
  · intro P hP
    obtain ⟨B, hB, hr⟩ := hK n ε U π hπ P
    refine ⟨B, fun v => (hB v).2, ?_⟩
    have := hT U L B fun u => hmem _ fun l => by
      obtain ⟨Q, hQ, hQ'⟩ := hr u l
      exact ⟨Q, hQ.trans hP, hQ'⟩
    rwa [sum_inner_integral_eq (muK ε) (fun k : KG ε => ev (toMK k) P) (fun k : KG ε => π k) _ _ hB] at this

theorem stTr : StTr := stTr_of_range_steps GlobalTheory.T.polyCoeff_vectors_lie_in_finiteDimensional_smooth GlobalTheory.T.shapeIntegratedOperator_ranges_polynomial rangeK GlobalTheory.OpTrace.hasTrace_sum_inner_of_range_le

end GlobalTheory.PsCo.Pc3

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIoExtensionOfWeakCharacterisationFramesStatement
section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ioExt_of_weakCharacterisation_of_orthonormal_frames : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → R.toRealDat.ExAt → (∀ i, (∀ a b, (Vc D i).hT ((Vc D i).frame a) ((Vc D i).frame b) = if a = b then 1 else 0) ∧ (Vc D i).L0 = Submodule.span (𝓞 D.host.E) (Set.range (Vc D i).frame)) → IoExt R.toRealDat := by
  first | exact @GlobalTheory.IoExtStd.thetaIoExtension_of_weakCharacterisation_frames | exact GlobalTheory.IoExtStd.thetaIoExtension_of_weakCharacterisation_frames | (intros; apply GlobalTheory.IoExtStd.thetaIoExtension_of_weakCharacterisation_frames <;> assumption)
end

