import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0777
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0066
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0656
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0729
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0793
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0779
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0747
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0709
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0762
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0776
import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeightedNormSquareRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0014
import Formalism.LocalToGlobal.Columns.ToHLatLemmas
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantSecond
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.ColNorms.BadPrimes

theorem false_of_isCoprime {A : Type} [CommRing A] [IsDedekindDomain A] (P : HeightOneSpectrum A) {a b : A}
    (h : IsCoprime a b) (ha : a ∈ P.asIdeal) (hb : b ∈ P.asIdeal) : False := by
  obtain ⟨x, y, hxy⟩ := h
  exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hxy ▸ add_mem (Ideal.mul_mem_left _ _ ha) (Ideal.mul_mem_left _ _ hb)))

theorem eq_of_natCast_mem {A : Type} [CommRing A] [IsDedekindDomain A] (P : HeightOneSpectrum A) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (ha : (p : A) ∈ P.asIdeal) (hb : (q : A) ∈ P.asIdeal) : p = q := by
  by_contra hne
  exact false_of_isCoprime P (Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 hne)) ha hb

variable {X : Fields} {Pr : Primes X}

theorem g_injective (hPr : Pr.Ok) : Function.Injective Pr.g := by
  intro i j h
  have := hPr.g_ne
  fin_cases i <;> fin_cases j <;> simp_all

theorem exists_vG {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ Pr.vGs) : ∃ i, P ∈ Pr.vG i := by
  classical
  rcases Finset.mem_union.mp h with h | h
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩

theorem g_mem (hPr : Pr.Ok) {i : Fin 2} {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ Pr.vG i) :
    ((Pr.g i : ℕ) : 𝓞 X.E) ∈ P.asIdeal :=
  hPr.piG_norm i ▸ Ideal.mul_mem_left _ _ (mem_of_mem_divs h)

theorem T_mem (hPr : Pr.Ok) {u : Pr.Word} {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ Pr.vT u) :
    ((Pr.T u : ℕ) : 𝓞 X.E) ∈ P.asIdeal :=
  hPr.piT_norm u ▸ Ideal.mul_mem_right _ _ (mem_of_mem_divs h)

theorem natCast_mem_of_conjP {P : HeightOneSpectrum (𝓞 X.E)} {n : ℕ} (h : ((n : ℕ) : 𝓞 X.E) ∈ (conjPrime₂ P).asIdeal) :
    ((n : ℕ) : 𝓞 X.E) ∈ P.asIdeal := by
  rw [mem_conjP, map_natCast] at h
  exact h

theorem rowSG_one (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) :
    rowSG Pr sel (1 : Tup X.F X.E X.K Sg) = Pr.vGs := by
  classical
  ext w
  constructor
  · intro hw
    rcases Finset.mem_union.mp hw with h | h
    · exact h
    · have h' : w ∈ QE sel ((mu0 X.F X.E X.K Sg : Tup X.F X.E X.K Sg) : Chr X.F X.E X.K) := h
      rw [twistPrimes_trivialTuple_empty sel Sg] at h'
      simp at h'
  · intro hw
    exact Finset.mem_union.mpr (Or.inl hw)

theorem prod_qOf_vGs (hPr : Pr.Ok) : ∏ P ∈ Pr.vGs, Formalism.L2.Col.qOf P = (Pr.g 0 * Pr.g 1) ^ X.f := by
  classical
  have hd : Disjoint (Pr.vG 0) (Pr.vG 1) := Finset.disjoint_left.2 fun P h0 h1 =>
    hPr.g_ne (eq_of_natCast_mem P (hPr.g_prime 0) (hPr.g_prime 1) (g_mem hPr h0) (g_mem hPr h1))
  have hi : ∀ i, ∏ P ∈ Pr.vG i, Formalism.L2.Col.qOf P = Pr.g i ^ X.f := fun i => by
    unfold Formalism.L2.Col.qOf
    rw [Finset.prod_congr rfl (g := fun _ => Pr.g i) (fun P hP => hPr.vG_norm i P hP), Finset.prod_const, hPr.vG_card]
  have hu : Pr.vGs = (Pr.vG 0).disjUnion (Pr.vG 1) hd := by
    ext w
    simp [Primes.vGs]
  rw [hu, Finset.prod_disjUnion, hi, hi, mul_pow]

theorem odd_g (hPr : Pr.Ok) (h2 : 2 ∣ Pr.cond) (i : Fin 2) : Odd (Pr.g i) :=
  Nat.odd_iff.2 ((hPr.g_cong i).of_dvd h2)

theorem two_notMem_vT (hPr : Pr.Ok) (h2 : 2 ∣ Pr.cond) {u : Pr.Word} {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ Pr.vT u) :
    (2 : 𝓞 X.E) ∉ P.asIdeal := by
  intro hP
  obtain ⟨c, hc⟩ := hPr.piT_cong u
  obtain ⟨k, hk⟩ := h2
  have h1 : Pr.piT u - 1 ∈ P.asIdeal := by
    rw [hc, hk]
    push_cast
    rw [mul_assoc, mul_assoc]
    exact Ideal.mul_mem_right _ _ hP
  exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using sub_mem (mem_of_mem_divs h) h1))

theorem odd_typePrime_of_two_dvd_cond (hX : X.Ok) (hPr : Pr.Ok) (h2 : 2 ∣ Pr.cond) (u : Pr.Word) : Odd (Pr.T u) := by
  obtain ⟨P, hP⟩ : (Pr.vT u).Nonempty := Finset.card_pos.1 (hPr.vT_card u ▸ hX.f_pos)
  refine (hPr.T_prime u).odd_of_ne_two fun h => two_notMem_vT hPr h2 hP ?_
  have := T_mem hPr hP
  rw [h] at this
  exact_mod_cast this

theorem conjP_notMem (hPr : Pr.Ok) (u : Pr.Word) {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ Pr.vT u ∨ P ∈ Pr.vGs) :
    ¬ (conjPrime₂ P ∈ Pr.vT u ∨ conjPrime₂ P ∈ Pr.vGs) := by
  rintro (h' | h')
  · rcases h with h | h
    · exact false_of_isCoprime P (hPr.piT_cop u) (mem_of_mem_divs h) (mem_of_mem_divs h' :)
    · obtain ⟨i, hi⟩ := exists_vG h
      exact hPr.T_ne_g u i (eq_of_natCast_mem P (hPr.T_prime u) (hPr.g_prime i)
        (natCast_mem_of_conjP (T_mem hPr h')) (g_mem hPr hi))
  · obtain ⟨j, hj⟩ := exists_vG h'
    have hg := natCast_mem_of_conjP (g_mem hPr hj)
    rcases h with h | h
    · exact hPr.T_ne_g u j (eq_of_natCast_mem P (hPr.T_prime u) (hPr.g_prime j) (T_mem hPr h) hg)
    · obtain ⟨i, hi⟩ := exists_vG h
      obtain rfl : i = j := g_injective hPr (eq_of_natCast_mem P (hPr.g_prime i) (hPr.g_prime j) (g_mem hPr hi) hg)
      have h1 : cO X.E (cO X.E (Pr.piG i)) ∈ P.asIdeal := (mem_of_mem_divs hj :)
      rw [cO_cO] at h1
      exact false_of_isCoprime P (hPr.piG_cop i) h1 (mem_of_mem_divs hi)

theorem bad_primes : ∀ (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), Hyp N s W Ch G sel mu cst I dl χ cD pl u δ → (∀ P ∈ rowSG Pr sel mu, P ∈ Pr.vGs) ∧ (∀ P ∈ Pr.vGs, ∃ i, P ∈ Pr.vG i ∧ Formalism.L2.Col.qOf P = Pr.g i ∧ ((Pr.g i : ℕ) : 𝓞 X.E) ∈ P.asIdeal ∧ ((Pr.g i : ℕ) : 𝓞 X.E) ∉ P.asIdeal ^ 2 ∧ ((Pr.g (1 - i) : ℕ) : 𝓞 X.E) ∉ P.asIdeal ∧ ((Pr.T u : ℕ) : 𝓞 X.E) ∉ P.asIdeal ∧ Pr.piT u ∉ P.asIdeal) ∧ (∀ P ∈ Pr.vT u, ((Pr.T u : ℕ) : 𝓞 X.E) ∈ P.asIdeal) ∧ (∏ P : rowSG Pr sel mu, Formalism.L2.Col.qOf P.1) = (Pr.g 0 * Pr.g 1) ^ N.R.f ∧ Odd (Pr.T u) ∧ (∀ i, Odd (Pr.g i)) ∧ ∀ P ∈ Sall sel mu u, conjPrime₂ P ∉ Sall sel mu u ∧ (2 : 𝓞 X.E) ∉ P.asIdeal := by
  classical
  intro D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ h
  obtain ⟨⟨-, -, -, -, -, -, hX1, -, -, hPr, -, hc, -, -⟩, -, -, -, hmu, -⟩ := h
  subst hmu
  have hX := hX1.ok
  have h2 : 2 ∣ Pr.cond := by
    rw [hc, NumDatum.cond]
    exact N.H.two_dvd_condN
  have hS : ∀ P, P ∈ Sall sel (1 : Tup X.F X.E X.K Sg) u ↔ P ∈ Pr.vT u ∨ P ∈ Pr.vGs := fun P => by
    rw [← rowSG_one sel Sg]
    exact Finset.mem_union
  refine ⟨fun P hP => rowSG_one sel Sg ▸ hP, fun P hP => ?_, fun P hP => T_mem hPr hP, ?_, odd_typePrime_of_two_dvd_cond hX hPr h2 u,
    odd_g hPr h2, fun P hP => ⟨fun h' => conjP_notMem hPr u ((hS _).1 hP) ((hS _).1 h'), ?_⟩⟩
  · obtain ⟨i, hi⟩ := exists_vG hP
    have hT : ((Pr.T u : ℕ) : 𝓞 X.E) ∉ P.asIdeal := fun hT =>
      hPr.T_ne_g u i (eq_of_natCast_mem P (hPr.T_prime u) (hPr.g_prime i) hT (g_mem hPr hi))
    refine ⟨i, hi, hPr.vG_norm i P hi, g_mem hPr hi,
      (GlobalTheory.TypePrimeUnif.typePrime_mem_and_notMem_sq hX hPr i P hi).2, fun hg => ?_, hT,
      fun hπ => hT (hPr.piT_norm u ▸ Ideal.mul_mem_right _ _ hπ)⟩
    have := g_injective hPr (eq_of_natCast_mem P (hPr.g_prime _) (hPr.g_prime _) hg (g_mem hPr hi))
    fin_cases i <;> simp at this
  · rw [Finset.prod_coe_sort _ (fun P => Formalism.L2.Col.qOf P), rowSG_one, prod_qOf_vGs hPr,
      GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors.card_eq_f N X pl.symm]
  · rcases (hS _).1 hP with h | h
    · exact two_notMem_vT hPr h2 h
    · obtain ⟨i, hi⟩ := exists_vG h
      intro hP2
      have := eq_of_natCast_mem P (hPr.g_prime i) Nat.prime_two (g_mem hPr hi) (by exact_mod_cast hP2)
      have ho := odd_g hPr h2 i
      rw [this] at ho
      exact absurd ho (by decide)

end GlobalTheory.ColNorms.BadPrimes
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CloseParamTaylorShift
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.AnPer.close_paramTaylor_shift : ∀ {I I₀ : Type} [Fintype I] [DecidableEq I] [Fintype I₀] {g : ℕ} {D : Type} [CommRing D] [Algebra ℂ D] {Λ : Type} [AddCommGroup Λ] (F : Fam I g Λ) (F₀ : Fam I₀ g Λ), (0 : I → ℂ) ∈ F.V → (∀ l z, F₀.τ l z = F.τ l 0) → ∀ (J : Ideal D) (N : ℕ), (∀ s : Fin (N + 1) → D, (∀ a, s a ∈ J) → ∏ a, s a = 0) → ∀ (t : I → D) (r : ℕ) (n : Fin r → I → D), (∀ j i, n j i ∈ J) → (∀ j i i', n j i * n j i' = 0) → (∀ i, t i = ∑ j, n j i) → ∀ (K : Charts F) (K₀ : Charts F₀) (l : Λ) (k k' : K.K) (k₀ k₀' : K₀.K) (h : K.le l k' k) (h₀ : K₀.le l k₀' k₀), (∀ p ∈ K₀.W k₀', (((0 : I → ℂ), p.2) : Tot I g) ∈ K.W k') → ∀ (Ta : Hol (K.W k) →ₐ[ℂ] D ⊗[ℂ] Hol (K₀.W k₀)) (Ta' : Hol (K.W k') →ₐ[ℂ] D ⊗[ℂ] Hol (K₀.W k₀')), (∀ (h : Hol (K.W k)) (p : Tot I₀ g) (hp : p ∈ K₀.W k₀), Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) (Ta h) = GlobalTheory.PeriodFamily.taylor N t fun z ↦ h.fn (z, p.2)) → (∀ (h : Hol (K.W k')) (p : Tot I₀ g) (hp : p ∈ K₀.W k₀'), Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) (Ta' h) = GlobalTheory.PeriodFamily.taylor N t fun z ↦ h.fn (z, p.2)) → Close (J.map (Algebra.TensorProduct.includeLeft : D →ₐ[ℂ] D ⊗[ℂ] Hol (K₀.W k₀'))) (Ta'.toRingHom.comp (Charts.sh h)) (((Algebra.TensorProduct.map (AlgHom.id ℂ D) (Hol.comap (F₀.shift l) (F₀.shift_analytic l (K₀.base k₀')) (K₀.maps h₀))).comp Ta).toRingHom) := by
  intro I I₀ _ _ _ g D _ _ Λ _ F F₀ h0 hτ J N hN t r n hn hnn ht K K₀ l k k' k₀ k₀' h h₀ hW Ta Ta' hTa hTa'
  have htJ : ∀ i, t i ∈ J := fun i ↦ by rw [ht]; exact J.sum_mem fun j _ ↦ hn j i
  have hnil : ∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0 := fun s ↦ hN _ fun a ↦ htJ _
  have hτa : AnalyticAt ℂ (F.τ l) 0 := F.hol l 0 h0
  obtain ⟨n', h1, h2, h3⟩ := GlobalTheory.PeriodFamily.taylor_sum_sub_value_eq_sum_sqZero J N hN r n hn hnn (fun (a : Fin g) z ↦ F.τ l z a)
    fun a ↦ analyticAt_pi_iff.1 hτa a
  have et : (fun i ↦ ∑ j, n j i) = t := funext fun i ↦ (ht i).symm
  rw [et] at h3
  obtain ⟨-, -, hconst, hcongr, -, -⟩ := GlobalTheory.T.taylorPolynomialEvalAlgebra_formal_properties N t
  have hm : ∀ p ∈ K₀.W k₀', (((0 : I → ℂ), p.2 + F.τ l 0) : Tot I g) ∈ K.W k := fun p hp ↦ K.maps h _ (hW p hp)
  refine GlobalTheory.AnPer.close_of_sliceTaylor J N hN t htJ r n' h1 h2 (K.W k) (K₀.W k₀') (fun p : Tot I₀ g ↦ p.2 + F.τ l 0)
    (fun p _ ↦ analyticAt_snd.add analyticAt_const) hm _ _ (fun f p hp ↦ ?_) fun f p hp ↦ ?_
  · refine (hTa' (Charts.sh h f) p hp).trans ?_
    have e : (fun z : I → ℂ ↦ (Charts.sh h f).fn (z, p.2)) =ᶠ[𝓝 0] fun z ↦ f.fn (z, p.2 + F.τ l z) := by
      have hc : Continuous (fun z : I → ℂ ↦ ((z, p.2) : Tot I g)) := by fun_prop
      filter_upwards [hc.continuousAt.eventually ((K.W k').isOpen.mem_nhds (hW p hp))] with z hz
        using Charts.fn_sh h f hz
    rw [hcongr _ _ e, GlobalTheory.PeriodFamily.taylor_shear N t hnil f.fn (F.τ l) p.2 hτa (f.analytic _ (hm p hp))]
    simp only [h3]
  · have hp' := K₀.maps h₀ p hp
    have e : ∀ x : D ⊗[ℂ] Hol (K₀.W k₀), Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) (Algebra.TensorProduct.map (AlgHom.id ℂ D)
        (Hol.comap (F₀.shift l) (F₀.shift_analytic l (K₀.base k₀')) (K₀.maps h₀)) x) =
        Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev (F₀.shift l p) hp')) (fun _ _ ↦ Commute.all _ _) x := fun x ↦ by
      induction x using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul d c =>
        simp only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply,
          Hol.ev_apply, Hol.fn_comap _ _ _ _ hp, AlgHom.id_apply]
    refine (e (Ta f)).trans ((hTa f _ hp').trans ?_)
    have e2 : (F₀.shift l p).2 = p.2 + F.τ l 0 := by simp only [Fam.shift, hτ]
    rw [e2, GlobalTheory.PeriodFamily.taylor_shear N t hnil f.fn (fun _ ↦ F.τ l 0) p.2 analyticAt_const (f.analytic _ (hm p hp))]
    simp only [hconst, sub_self]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CloseTaylorShift
section
open Filter Topology TopologicalSpace TensorProduct
open GlobalTheory.AnPer GlobalTheory.PeriodFamily

namespace GlobalTheory.AnPer

theorem evT_map_shA {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {K : Charts F}
    {R : Type} [CommRing R] [Algebra ℂ R] {l : Λ} {k k' : K.K} (h : K.le l k' k) (p : Tot I g) (hp : p ∈ K.W k')
    (y : R ⊗[ℂ] Hol (K.W k)) :
    evT R p hp (Algebra.TensorProduct.map (AlgHom.id ℂ R) (Charts.shA h) y) =
      evT R (F.shift l p) (K.maps h p hp) y := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  | tmul x y =>
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul,
      AlgHom.comp_apply, AlgHom.comp_apply, Hol.ev_apply, Hol.ev_apply, Charts.shA_apply, Charts.fn_sh h y hp]
    rfl

theorem close_taylor_shift : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {F₀ : Fam Empty g Λ} (K : Charts F) (K₀ : Charts F₀) {R : Type} [CommRing R] [Algebra ℂ R] (J : Ideal R) (N : ℕ), (∀ s : Fin (N + 1) → R, (∀ a, s a ∈ J) → ∏ a, s a = 0) → ∀ (r : ℕ) (m : Fin r → I → R), (∀ j i, m j i ∈ J) → (∀ j i i', m j i * m j i' = 0) → (∀ l z, F₀.τ l z = F.τ l 0) → ∀ (l : Λ) (k k' : K.K) (k₀ k₀' : K₀.K) (h : K.le l k' k) (h₀ : K₀.le l k₀' k₀), (∀ p ∈ K₀.W k₀', (((0 : I → ℂ), p.2) : Tot I g) ∈ K.W k') → ∀ (ρ : Hol (K.W k) →+* R ⊗[ℂ] Hol (K₀.W k₀)) (ρ' : Hol (K.W k') →+* R ⊗[ℂ] Hol (K₀.W k₀')), IsTay N (fun i ↦ ∑ j, m j i) ρ → IsTay N (fun i ↦ ∑ j, m j i) ρ' → Close (J.map (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] Hol (K₀.W k₀'))) (ρ'.comp (Charts.sh h)) ((Algebra.TensorProduct.map (AlgHom.id ℂ R) (Charts.shA h₀)).toRingHom.comp ρ) := by
  intro I _ _ g Λ _ F F₀ K K₀ R _ _ J N hJ r m hm hmm hτ l k k' k₀ k₀' h h₀ hW ρ ρ' hρ hρ'
  by_cases hne : ∃ p, p ∈ K₀.W k₀'
  swap
  · have e : ρ'.comp (Charts.sh h) =
        (Algebra.TensorProduct.map (AlgHom.id ℂ R) (Charts.shA h₀)).toRingHom.comp ρ :=
      RingHom.ext fun f ↦ GlobalTheory.tensor_hol_ext_of_values _ _ _ _ fun p hp ↦ (hne ⟨p, hp⟩).elim
    rw [e]
    exact Relation.ReflTransGen.refl
  obtain ⟨p₀, hp₀⟩ := hne
  have h0 : (0 : I → ℂ) ∈ F.V := K.base k' _ (hW p₀ hp₀)
  have hτa : AnalyticAt ℂ (F.τ l) 0 := F.hol l _ h0
  obtain ⟨n, hn, hnn, hd⟩ := GlobalTheory.T.taylor_sub_value_eq_sum_sqZero_vector J N hJ r m hm hmm (F.τ l) hτa
  have ht : ∀ i, (fun i ↦ ∑ j, m j i) i ∈ J := fun i ↦ J.sum_mem fun j _ ↦ hm j i
  have htN : ∀ s : Fin (N + 1) → I, ∏ a, (fun i ↦ ∑ j, m j i) (s a) = 0 :=
    fun s ↦ hJ _ fun a ↦ ht (s a)
  have hin : ∀ p ∈ K₀.W k₀', (((0 : I → ℂ), p.2 + F.τ l 0) : Tot I g) ∈ K.W k :=
    fun p hp ↦ K.maps h _ (hW p hp)
  obtain ⟨-, -, hconst, hgerm, -, -⟩ := taylor_formal_properties N (fun i ↦ ∑ j, m j i)
  refine close_of_sliceTaylor J N hJ _ ht r n hn hnn (K.W k) (K₀.W k₀') (fun p ↦ p.2 + F.τ l 0)
    (fun p _ ↦ analyticAt_snd.add analyticAt_const) hin _ _ ?_ ?_
  · intro f p hp
    refine (hρ' (Charts.sh h f) p hp).trans ?_
    have hc : ContinuousAt (fun z : I → ℂ ↦ ((z, p.2) : Tot I g)) 0 := by fun_prop
    have e : (fun z ↦ (Charts.sh h f).fn (z, p.2)) =ᶠ[𝓝 0] fun z ↦ f.fn (z, p.2 + F.τ l z) := by
      filter_upwards [hc.preimage_mem_nhds ((K.W k').isOpen.mem_nhds (hW p hp))] with z hz
      exact Charts.fn_sh h f hz
    rw [hgerm _ _ e, taylor_shear N _ htN f.fn (F.τ l) p.2 hτa (f.analytic _ (hin p hp))]
    simp only [hd]
  · intro f p hp
    refine (evT_map_shA h₀ p hp (ρ f)).trans ?_
    refine (hρ f _ _).trans ?_
    have e : (F₀.shift l p).2 = p.2 + F.τ l 0 := by
      change p.2 + F₀.τ l p.1 = _
      rw [hτ]
    rw [e]
    refine (taylor_shear N _ htN f.fn (fun _ ↦ F.τ l 0) p.2 analyticAt_const (f.analytic _ (hin p hp))).trans ?_
    simp only [hconst, sub_self]

end GlobalTheory.AnPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubfunctorStalkIdealCriterion
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FinStalk

theorem stalk_isArtinianRing (K : Type) [Field K] (X : Scheme) (f : X ⟶ Sp K) [IsFinite f] (x : X) :
    IsArtinianRing (X.presheaf.stalk x) := by
  have : IsAffine X := isAffine_of_isAffineHom f
  have hfin : ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop).hom.Finite :=
    f.finite_appTop.comp (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2)
  letI := ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop).hom.toAlgebra
  haveI : Module.Finite K Γ(X, ⊤) := hfin
  haveI : IsArtinianRing Γ(X, ⊤) := IsArtinianRing.of_finite K Γ(X, ⊤)
  have hU := isAffineOpen_top X
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, trivial⟩ : (⊤ : X.Opens))
  have hl := hU.isLocalization_stalk ⟨x, trivial⟩
  exact IsArtinianRing.localization_artinian (hU.primeIdealOf ⟨x, trivial⟩).asIdeal.primeCompl _

end GlobalTheory.FinStalk

namespace GlobalTheory.FinStalk

theorem stalk_quotient_ne_top_and_isArtinianRing : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (H : Over (Sp K)) [GrpObj H] (j : H ⟶ A), IsMonHom j → IsClosedImmersion j.left → IsFinite H.hom → ∀ x₀ : A.left, x₀ ∈ Set.range (η[A]).left.base → ∀ J : Ideal (A.left.presheaf.stalk x₀), (∀ (R' : Type) [CommRing R'] (ψ : A.left.presheaf.stalk x₀ →+* R'), (∃ y : Sp R' ⟶ H.left, y ≫ j.left = Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk x₀) ↔ J ≤ RingHom.ker ψ) → J ≠ ⊤ ∧ IsArtinianRing (A.left.presheaf.stalk x₀ ⧸ J) := by
  intro K _ A _ H _ j hj hci hfin x₀ hx₀ J hJ
  obtain ⟨p, hp⟩ := hx₀
  have hη : (η[H] ≫ j).left = η[A].left := congrArg CommaMorphism.left (IsMonHom.one_hom j)
  obtain ⟨h₀, e⟩ : ∃ h₀ : H.left, x₀ = j.left.base h₀ :=
    ⟨η[H].left.base p, by rw [← hp, ← hη]; rfl⟩
  subst e

  have hJ1 : J ≤ RingHom.ker (j.left.stalkMap h₀).hom :=
    (hJ (H.left.presheaf.stalk h₀) (j.left.stalkMap h₀).hom).1
      ⟨H.left.fromSpecStalk h₀, (Scheme.SpecMap_stalkMap_fromSpecStalk j.left).symm⟩
  have hne : J ≠ ⊤ := fun h => RingHom.ker_ne_top _ (top_le_iff.1 (h ▸ hJ1))
  refine ⟨hne, ?_⟩
  haveI : Nontrivial (A.left.presheaf.stalk (j.left.base h₀) ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hne
  haveI : IsLocalRing (A.left.presheaf.stalk (j.left.base h₀) ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (Ideal.Quotient.mk J) :=
    Function.Surjective.isLocalHom _ Ideal.Quotient.mk_surjective
  obtain ⟨y, hy⟩ := (hJ _ (Ideal.Quotient.mk J)).2 (by rw [Ideal.mk_ker])
  let R := CommRingCat.of (A.left.presheaf.stalk (j.left.base h₀) ⧸ J)
  have hpt : y.base (IsLocalRing.closedPoint R) = h₀ := by
    apply j.left.isClosedEmbedding.injective
    have : j.left.base (y.base (IsLocalRing.closedPoint R)) = (A.left.fromSpecStalk (j.left.base h₀)).base
        ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).base (IsLocalRing.closedPoint R)) :=
      congrArg (fun g : Sp R ⟶ A.left => g.base (IsLocalRing.closedPoint R)) hy
    rw [this]
    haveI : IsLocalHom (CommRingCat.ofHom (Ideal.Quotient.mk J)).hom := by
      change IsLocalHom (Ideal.Quotient.mk J); infer_instance
    rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
  have key : ∀ z (_ : y.base (IsLocalRing.closedPoint R) = z),
      ∃ φ : H.left.presheaf.stalk z ⟶ R, Spec.map φ ≫ H.left.fromSpecStalk z = y := by
    rintro z rfl
    exact ⟨_, Scheme.Spec_stalkClosedPointTo_fromSpecStalk y⟩
  obtain ⟨φ, hφ⟩ := key h₀ hpt
  have hcomp : j.left.stalkMap h₀ ≫ φ = CommRingCat.ofHom (Ideal.Quotient.mk J) := by
    apply Spec.map_injective
    rw [← cancel_mono (A.left.fromSpecStalk (j.left.base h₀)), ← hy, ← hφ, Spec.map_comp,
      Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk, Category.assoc]
  have hsurj : Function.Surjective φ.hom := by
    intro r
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (I := J) r
    exact ⟨(j.left.stalkMap h₀).hom a, by
      rw [← CommRingCat.comp_apply, hcomp]; rfl⟩
  haveI := stalk_isArtinianRing K H.left H.hom h₀
  exact hsurj.isArtinianRing

end GlobalTheory.FinStalk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureNormOneProductsSubgroupPropertiesStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closure_normOneProducts_h0_properties : ∀ (F : Type) [Field F] [NumberField F] (a b : F) (ε : AF F), ε * ε = ε → (∀ x ∈ closure (H0 (a := a) (b := b) ε), ∀ y ∈ closure (H0 (a := a) (b := b) ε), x * y ∈ closure (H0 (a := a) (b := b) ε)) ∧ (∀ x ∈ closure (H0 (a := a) (b := b) ε), star x ∈ closure (H0 (a := a) (b := b) ε)) ∧ (∀ δ δ' : ℍ[F, a, b], δ * δ' = 1 → ∀ x ∈ closure (H0 (a := a) (b := b) ε), rat δ * x * rat δ' ∈ closure (H0 (a := a) (b := b) ε)) ∧ (∀ x ∈ closure (H0 (a := a) (b := b) ε), nrm x = 1) := by
  first | exact @GlobalTheory.QSA.Grp.closure_normOneProducts_subgroup_properties | exact GlobalTheory.QSA.Grp.closure_normOneProducts_subgroup_properties | (intros; apply GlobalTheory.QSA.Grp.closure_normOneProducts_subgroup_properties <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColsInIsometry
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows

noncomputable section

namespace GlobalTheory.ColFirstIso

section Generic

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S S' : GSD K}

def clEquiv (eG : S'.G ≃* S.G) (eD : S'.D ≃ S.D) (hs : ∀ g d, eD (g • d) = eG g • eD d) : S'.Cl ≃ S.Cl :=
  Quotient.congr eD fun a b => by
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨eG g, (hs g b).symm⟩
    · rintro ⟨g, hg⟩
      refine ⟨eG.symm g, eD.injective ?_⟩
      have hg' : g • eD b = eD a := hg
      show eD (eG.symm g • b) = eD a
      rw [hs, MulEquiv.apply_symm_apply, hg']

theorem clEquiv_cls (eG : S'.G ≃* S.G) (eD : S'.D ≃ S.D) (hs : ∀ g d, eD (g • d) = eG g • eD d) (d : S'.D) :
    clEquiv eG eD hs (S'.cls d) = S.cls (eD d) := rfl

theorem card_stab (eG : S'.G ≃* S.G) (eD : S'.D ≃ S.D) (hs : ∀ g d, eD (g • d) = eG g • eD d) (d : S'.D) :
    Nat.card (MulAction.stabilizer S'.G d) = Nat.card (MulAction.stabilizer S.G (eD d)) := by
  refine Nat.card_congr (eG.toEquiv.subtypeEquiv fun g => ?_)
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
  show _ ↔ eG g • eD d = eD d
  rw [← hs, eD.injective.eq_iff]

theorem ipAt_transport (R : S.Rat) (h : S.Ok) (h' : S'.Ok) (eG : S'.G ≃* S.G) (eD : S'.D ≃ S.D)
    (hs : ∀ g d, eD (g • d) = eG g • eD d) (v : InfinitePlace K) (φ : S.EqFun) (φ' : S'.D → S'.V)
    (hp : ∀ d, S'.pairAt v (φ' d) (φ' d) = S.pairAt v ((φ : S.D → S.V) (eD d)) ((φ : S.D → S.V) (eD d))) :
    S'.ipAt h' v φ' φ' = S.ipAt h v φ φ := by
  let e := clEquiv eG eD hs
  let s : S.Sec :=
    { rep := fun c => eD (S'.outSec.rep (e.symm c))
      spec := fun c => by
        rw [← clEquiv_cls eG eD hs, S'.outSec.spec]
        exact e.apply_symm_apply c }
  rw [R.ipAt_indep h s v φ φ]
  let _ := h.fintypeCl
  let _ := h'.fintypeCl
  unfold GSD.ipAt
  refine Fintype.sum_equiv e _ _ fun c => ?_
  have h1 : s.rep (e c) = eD (S'.outSec.rep c) := by
    show eD (S'.outSec.rep (e.symm (e c))) = _
    rw [e.symm_apply_apply]
  rw [h1, S'.wt_eq h' S'.outSec c, card_stab eG eD hs, hp]

end Generic

section Frames

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}

def decoEquiv (hQ : Q = ∅) : DecoF X.E n ST SG Q ≃ DecoSet X.E n ST SG where
  toFun := DecoF.deco
  invFun d := ⟨(d, fun _ => 1), fun P => absurd P.2 (by simp [hQ])⟩
  left_inv p := Subtype.ext (Prod.ext rfl (funext fun P => absurd P.2 (by simp [hQ])))
  right_inv _ := rfl

def grpEquiv (hQ : Q = ∅) (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) : FrmG Λ Θ ≃* FormG Λ where
  toFun g := (g.1, g.2.1)
  invFun g := (g.1, g.2, 1)
  left_inv g := Prod.ext rfl (Prod.ext rfl (Subtype.ext (funext fun P => absurd P.2 (by simp [hQ]))))
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem ipAt_frm (hQ : Q = ∅) (C : CoefPk X n (DecoSet X.E n ST SG)) (Λ Λ' : LevFam X.E X.K n SG) (hΛ : Λ' = Λ)
    (Θ : LevQFam X.E X.K n Q) (R : (formGSD C Λ).Rat) (h : (formGSD C Λ).Ok)
    (h' : (frmGSD (C.pull (DecoF.deco (Q := Q))) Λ' Θ).Ok) (v : InfinitePlace X.K) (φ : (formGSD C Λ).EqFun) :
    (frmGSD (C.pull (DecoF.deco (Q := Q))) Λ' Θ).ipAt h' v (fun p => (φ : _ → C.V) (DecoF.deco p))
      (fun p => (φ : _ → C.V) (DecoF.deco p)) = (formGSD C Λ).ipAt h v φ φ := by
  subst hΛ
  exact ipAt_transport R h h' (grpEquiv hQ Λ' Θ) (decoEquiv hQ) (fun _ _ => rfl) v φ _ fun _ => rfl

end Frames

theorem qe_one {X : Fields} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {Sg : Set ℕ} :
    QE sel ((1 : Tup X.F X.E X.K Sg) : Chr X.F X.E X.K) = ∅ := by
  have h : Qprime ((1 : Tup X.F X.E X.K Sg) : Chr X.F X.E X.K) = ∅ := by
    change Qprime (1 : Chr X.F X.E X.K) = ∅
    ext v
    simp [Qprime, MonoidHom.ker_one]
  unfold QE
  split_ifs with hf
  · rw [(Set.Finite.toFinset_eq_empty (h := hf)).2 h]
    rfl
  · rfl

theorem colsIn_isometry : ∀ (X : Fields) (hX : X.Ok) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ) (hL : I.Ok Ch sel mu cst G m2) (u : Pr.Word) (h : (chF W sel mu I u 0).Ok), mu = 1 → (∀ v, IsUnit ((MramH W Ch hX u).X v).det) ∧ ∀ (v : InfinitePlace X.K) (x : Fin (ramDim W Ch hX u) → X.K), ((Formalism.HermitianLatticesTheory.normAt (Pi.basisFun X.K (Fin (ramDim W Ch hX u))) (MramH W Ch hX u).X v x ^ 2 : ℝ) : ℂ) = famIpAt (chF W sel mu I u 0) h v (colsIn W Ch hX sel mu cst I hL u x) (colsIn W Ch hX sel mu cst I hL u x) := by
  intro X hX Pr R W Ch sel Sg mu cst I G m2 hL u h hmu
  refine ⟨(colPosH W Ch hX u 0).frameOK_sub (MramV W Ch u) (MramL W Ch u), fun v x => ?_⟩
  have hQ : QE sel (mu : Chr X.F X.E X.K) = ∅ := by
    subst hmu
    exact qe_one sel
  obtain ⟨b, hb⟩ := hL.zero_uniq
  have h1 : famIpAt (chF W sel mu I u 0) h v (colsIn W Ch hX sel mu cst I hL u x) (colsIn W Ch hX sel mu cst I hL u x) =
      (colGSD W Ch u 0).ipAt (colOk W Ch hX u 0) v (colOfCoord W Ch hX u x) (colOfCoord W Ch hX u x) := by
    unfold famIpAt
    rw [Fintype.sum_eq_single b fun b' hb' => absurd (hb b') hb']
    exact ipAt_frm hQ (colVal W u 0 (Pr.vT u) Pr.vGs) (colLev Ch 0) (I.levG 0 b) (hL.zero_G b) (I.levQ 0 b)
      (colRat W Ch hX u 0) (colOk W Ch hX u 0) (h b) v (colOfCoord W Ch hX u x)
  rw [h1, ← (colRat W Ch hX u 0).maj_eq]
  have h2 := (colPosH W Ch hX u 0).sub_maj (MramV W Ch u) v ((ramBas W Ch hX u).equivFun.symm x)
    ((ramBas W Ch hX u).equivFun.symm x)
  rw [thl_majAt_coord, LinearEquiv.apply_symm_apply] at h2
  refine Eq.trans ?_ h2
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.majAt Formalism.HermitianLatticesTheory.cnorm
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => by positivity)), Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  rfl

end GlobalTheory.ColFirstIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivWeierstrassPAddHalfPeriodStatement
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivWeierstrassP_add_half_period' : ∀ (L : PeriodPair) (a t : ℂ), a ∉ L.lattice → 2 * a ∈ L.lattice → t ∉ L.lattice → t + a ∉ L.lattice → L.derivWeierstrassP (t + a) * (L.weierstrassP t - L.weierstrassP a) ^ 2 = -(3 * L.weierstrassP a ^ 2 - L.g₂ / 4) * L.derivWeierstrassP t := by
  first | exact @GlobalTheory.derivWeierstrassP_add_half_period | exact GlobalTheory.derivWeierstrassP_add_half_period | (intros; apply GlobalTheory.derivWeierstrassP_add_half_period <;> assumption)
end

