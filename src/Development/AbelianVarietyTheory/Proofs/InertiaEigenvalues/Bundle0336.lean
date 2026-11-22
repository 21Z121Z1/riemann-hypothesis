import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0311
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedIntegersTensorEqLetterwiseProductAinf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0206
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0307
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0310
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0319
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0316
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0101
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0318
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverEta
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0322
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWachInclusionPowerSeriesIntoOneTmulAinf
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.Prism GlobalTheory.PrismS
open scoped Formalism.Per

namespace GlobalTheory.PrismS.IoDescent

section General

variable {Z O A : Type} [CommRing Z] [CommRing O] [CommRing A] [Algebra Z O] [Algebra Z A]

theorem exists_retraction [IsLocalRing Z] [Module.Free Z O] (p : Z)
    (hp : IsLocalRing.maximalIdeal Z = Ideal.span {p}) (hu : ¬ IsUnit (algebraMap Z O p)) :
    ∃ r : O →ₗ[Z] Z, r 1 = 1 := by
  let b := Module.Free.chooseBasis Z O
  by_cases h : ∃ i, IsUnit (b.repr 1 i)
  · obtain ⟨i, hi⟩ := h
    obtain ⟨v, hv⟩ := hi.exists_left_inv
    exact ⟨v • b.coord i, by simpa using hv⟩
  · exfalso
    apply hu
    have h1 : ∀ i, p ∣ b.repr 1 i := fun i => by
      rw [← Ideal.mem_span_singleton, ← hp, IsLocalRing.mem_maximalIdeal]
      exact fun hi => h ⟨i, hi⟩
    refine isUnit_of_dvd_one ?_
    rw [← b.linearCombination_repr 1, Finsupp.linearCombination_apply, Finsupp.sum]
    refine Finset.dvd_sum fun i _ => ?_
    rw [Algebra.smul_def]
    exact (map_dvd _ (h1 i)).mul_right _

theorem exists_factor {W : Type} [CommRing W] (r : O →ₗ[Z] Z) (hr : r 1 = 1)
    (f : PowerSeries W →+* O ⊗[Z] A) (π : A) (hX : f PowerSeries.X = (1 : O) ⊗ₜ[Z] π)
    (hC : ∀ w, ∃ a, f (PowerSeries.C w) = (1 : O) ⊗ₜ[Z] a)
    (hs : IsHausdorff (Ideal.span {(1 : O) ⊗ₜ[Z] π}) (O ⊗[Z] A)) :
    (∀ a b : A, (1 : O) ⊗ₜ[Z] a = (1 : O) ⊗ₜ[Z] b → a = b) ∧
      ∃ io : PowerSeries W →+* A, ∀ x, f x = (1 : O) ⊗ₜ[Z] io x := by
  let p : O ⊗[Z] A →ₗ[Z] A := (TensorProduct.lid Z A).toLinearMap ∘ₗ r.rTensor A
  have hp : ∀ o a, p (o ⊗ₜ a) = r o • a := fun o a => by simp [p]
  have hp1 : ∀ a, p (1 ⊗ₜ a) = a := fun a => by rw [hp, hr, one_smul]
  let j : A →+* O ⊗[Z] A := (Algebra.TensorProduct.includeRight (R := Z) (A := O) (B := A)).toRingHom
  have hj : ∀ a, j a = (1 : O) ⊗ₜ[Z] a := fun _ => rfl
  have hpm : ∀ a y, p (j a * y) = a * p y := fun a y => by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul o b => rw [hj, Algebra.TensorProduct.tmul_mul_tmul, one_mul, hp, hp, mul_smul_comm]
    | add y z hy hz => rw [mul_add, map_add, map_add, hy, hz, mul_add]
  have hinj : Function.Injective j := fun a b h => by
    rw [← hp1 a, ← hp1 b, ← hj, ← hj, h]
  have hpoly : ∀ q : Polynomial W, f (q : PowerSeries W) ∈ j.range := fun q => by
    induction q using Polynomial.induction_on' with
    | add q q' h h' => rw [Polynomial.coe_add, map_add]; exact add_mem h h'
    | monomial n w =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_C,
        Polynomial.coe_X, map_mul, map_pow]
      obtain ⟨a, ha⟩ := hC w
      exact mul_mem (RingHom.mem_range.2 ⟨a, ha.symm⟩) (pow_mem (RingHom.mem_range.2 ⟨π, hX.symm⟩) _)
  have hall : ∀ x, f x ∈ j.range := fun x => by
    refine ⟨p (f x), ?_⟩
    rw [← sub_eq_zero]
    refine hs.haus _ fun m => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    obtain ⟨x', hx'⟩ : ∃ x', x = ((PowerSeries.trunc m x : Polynomial W) : PowerSeries W) + PowerSeries.X ^ m * x' :=
      ⟨_, PowerSeries.eq_X_pow_mul_shift_add_trunc m x |>.trans (add_comm _ _)⟩
    obtain ⟨a, ha⟩ := hpoly (PowerSeries.trunc m x)
    have e : f x = j a + j (π ^ m) * f x' := by
      conv_lhs => rw [hx']
      rw [map_add, map_mul, map_pow, hX, ha, map_pow, hj]
    refine ⟨j (p (f x')) - f x', ?_⟩
    rw [e, map_add, hpm, hj a, hp1, map_add, map_mul, ← hj a, ← hj π, map_pow]
    ring
  refine ⟨fun a b h => hinj h, ?_⟩
  let e : A ≃+* j.range := RingEquiv.ofBijective j.rangeRestrict
    ⟨fun a b h => hinj (congrArg Subtype.val h), j.rangeRestrict_surjective⟩
  refine ⟨e.symm.toRingHom.comp (f.codRestrict j.range hall), fun x => ?_⟩
  have := congrArg Subtype.val (e.apply_symm_apply (f.codRestrict j.range hall x))
  exact this.symm

theorem tmul_algebraMap (c : Z) :
    algebraMap O (O ⊗[Z] A) (algebraMap Z O c) = (1 : O) ⊗ₜ[Z] algebraMap Z A c := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_tmul]

theorem exists_sum {W C : Type} [CommRing W] [CommRing C] (F : W →+* O ⊗[Z] A) (θ : A →+* C) (g : W →+* C)
    {n : ℕ} (z u : Fin n → W) (hz : ∀ i, ∃ a, F (z i) = (1 : O) ⊗ₜ[Z] a ∧ θ a = g (z i))
    (hu : ∀ i, ∃ a, F (u i) = (1 : O) ⊗ₜ[Z] a ∧ θ a = g (u i)) :
    ∃ a, F (∑ i, z i * u i) = (1 : O) ⊗ₜ[Z] a ∧ θ a = g (∑ i, z i * u i) := by
  choose a a1 a2 using hz
  choose b b1 b2 using hu
  refine ⟨∑ i, a i * b i, ?_, ?_⟩
  · rw [map_sum, tmul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, a1, b1, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  · rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, a2, b2]

end General

variable {l : ℕ} [Fact l.Prime]

theorem εroot_pow {P : LocPrime l} (AI : LocAinf l P) (s : ℕ) : AI.εroot s ^ l ^ s = AI.ε := by
  induction s with
  | zero => simp [LocAinf.εroot]
  | succ s ih =>
    rw [pow_succ', pow_mul, LocAinf.εroot, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]
    exact ih

theorem εroot_sub_not_unit {P : LocPrime l} (AI : LocAinf l P) (s : ℕ) : ¬ IsUnit (AI.εroot s - 1) := by
  intro h
  have h1 := (h.pow (l ^ s)).map (PreTilt.coeff (O := OC l) (p := l) 0)
  rw [sub_pow_char_pow, εroot_pow, one_pow, map_sub, AI.ε_coeff, AI.ζ_zero, map_one, map_one,
    sub_self] at h1
  exact not_isUnit_zero h1

theorem letEmb_C {K LL : FinExt l} {n : ℕ} (emb : ZMod n → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1)) (w : WK K) :
    letEmb emb (PowerSeries.C w) = fun k => PowerSeries.C (embW (emb k) w) := by
  funext k
  rw [letEmb_apply, PowerSeries.map_C]
  rfl

theorem letEmb_X {K LL : FinExt l} {n : ℕ} (emb : ZMod n → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1)) :
    letEmb emb PowerSeries.X = letπ := by
  funext k
  rw [letEmb_apply, PowerSeries.map_X]
  rfl

theorem letEmb_scalar {K LL : FinExt l} {n : ℕ} (emb : ZMod n → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1)) (c : ℤ_[l]) :
    letEmb emb (PowerSeries.C (algebraMap ℤ_[l] (WK K) c)) =
      algebraMap ↥(OL LL) (LetA ↥(OL LL) n) (algebraMap ℤ_[l] ↥(OL LL) c) := by
  rw [letEmb_C]
  funext k
  rw [(embW (emb k)).commutes c]
  rfl

theorem map_scalar {K LL : FinExt l} {n : ℕ} (emb : ZMod n → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1))
    (φ : LetA ↥(OL LL) n →ₐ[↥(OL LL)] RA LL) (c : ℤ_[l]) :
    φ (letEmb emb (PowerSeries.C (algebraMap ℤ_[l] (WK K) c))) =
      (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] algebraMap ℤ_[l] (Ainf l) c := by
  rw [letEmb_scalar, AlgHom.commutes, tmul_algebraMap]

theorem theta_scalar (K : FinExt l) (c : ℤ_[l]) :
    Formalism.Per.θ l (algebraMap ℤ_[l] (Ainf l) c) = intToOC K (algebraMap ℤ_[l] ↥(OL K) c) :=
  Subtype.ext ((GlobalTheory.UnramIdem.ringHom_eq ((Formalism.Per.θ l).comp (algebraMap ℤ_[l] (Ainf l))) c).trans
    (GlobalTheory.UnramIdem.ringHom_eq ((intToOC K).comp (algebraMap ℤ_[l] ↥(OL K))) c).symm)

theorem exists_span (K : FinExt l) (w : WK K) : ∃ (n : ℕ) (z : Fin n → ℤ_[l]) (u : Fin n → WK K),
    (∀ i, ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ ((u i : ↥(K0 K)) : Om l) ^ m = 1) ∧
      w = ∑ i, algebraMap ℤ_[l] (WK K) (z i) * u i := by
  obtain ⟨n, z, ω, hω, hsum⟩ := GlobalTheory.UnramSpan.exists_sum_rootsOfUnity l K ((w : ↥(K0 K)) : Om l)
    (w : ↥(K0 K)).2 (norm_le_one_of_mem_OL (unr K) w)
  choose h0 m hm hl h1 using hω
  refine ⟨n, z, fun i => ⟨⟨ω i, h0 i⟩, IsIntegral.of_pow (hm i) (by
    rw [show (⟨ω i, h0 i⟩ : ↥(K0 K)) ^ m i = 1 from Subtype.ext (h1 i)]; exact isIntegral_one)⟩,
    fun i => ⟨m i, hm i, hl i, h1 i⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  rw [hsum]
  push_cast
  rfl

theorem exists_const {K LL : FinExt l} {n : ℕ} (emb : ZMod n → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1))
    (φ : LetA ↥(OL LL) n →ₐ[↥(OL LL)] RA LL)
    (hI : ∀ (c : ↥(K0 K)) (m : ℕ), 0 < m → ¬ l ∣ m → (c : Om l) ^ m = 1 → ∀ xb : OCb l,
      IsTiltOf (c : Om l) m xb → ∀ o : ZMod n → ↥(OL LL), (∀ i, ((o i : ↥(OL LL)) : ↥LL.1) = emb i c) →
      φ (fun i => PowerSeries.C (o i)) = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] WittVector.teichmuller l xb) (w : WK K) :
    ∃ a : Ainf l, φ (letEmb emb (PowerSeries.C w)) = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] a ∧
      Formalism.Per.θ l a = intToOC (unr K) w := by
  obtain ⟨r, z, u, hu, rfl⟩ := exists_span K w
  refine exists_sum ((φ.toRingHom.comp (letEmb emb)).comp PowerSeries.C) (Formalism.Per.θ l)
    (intToOC (unr K)) (fun i => algebraMap ℤ_[l] (WK K) (z i)) u
    (fun i => ⟨_, map_scalar emb φ (z i), theta_scalar (unr K) (z i)⟩) (fun i => ?_)
  obtain ⟨m, hm, hl, h1⟩ := hu i
  obtain ⟨xb, hxb⟩ := GlobalTheory.MemLoc.exists_isTiltOf _ m hm hl h1
  refine ⟨WittVector.teichmuller l xb, ?_, ?_⟩
  · change φ (letEmb emb (PowerSeries.C (u i))) = _
    rw [letEmb_C]
    exact hI _ m hm hl h1 xb hxb _ (fun k => rfl)
  · apply Subtype.ext
    exact (congrArg Subtype.val (WittVector.fontaineTheta_teichmuller xb)).trans
      (GlobalTheory.MemLoc.IsTiltOf.untilt_eq hxb)

theorem exists_io {K LL : FinExt l} {n : ℕ} (emb : ZMod n → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1))
    (φ : LetA ↥(OL LL) n →ₐ[↥(OL LL)] RA LL) (e : OCb l) (he : ¬ IsUnit (e - 1))
    (hπ : φ letπ = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (WittVector.teichmuller l e - 1))
    (hC : ∀ w : WK K, ∃ a : Ainf l, φ (letEmb emb (PowerSeries.C w)) = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] a ∧
      Formalism.Per.θ l a = intToOC (unr K) w) :
    ∃ io : PowerSeries (WK K) →+* Ainf l, (∀ x, φ (letEmb emb x) = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] io x) ∧
      io PowerSeries.X = WittVector.teichmuller l e - 1 ∧
      ∀ w : WK K, Formalism.Per.θ l (io (PowerSeries.C w)) = intToOC (unr K) w := by
  obtain ⟨_, -, -, hu, hfree, -⟩ := GlobalTheory.Per.integers_completeDVR l LL
  obtain ⟨r, hr⟩ := exists_retraction (Z := ℤ_[l]) (O := ↥(OL LL)) (l : ℤ_[l])
    PadicInt.maximalIdeal_eq_span_p (by rwa [map_natCast])
  have hX : φ (letEmb emb PowerSeries.X) =
      (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (WittVector.teichmuller l e - 1) := by
    rw [letEmb_X, hπ]
  obtain ⟨hinj, io, hio⟩ := exists_factor r hr (φ.toRingHom.comp (letEmb emb)) _ hX
    (fun w => (hC w).imp fun a h => h.1)
    ((GlobalTheory.HWL.TensorWitt.main l LL).2.2.2.2 e he).toIsHausdorff
  refine ⟨io, hio, hinj _ _ ((hio _).symm.trans hX), fun w => ?_⟩
  obtain ⟨a, h1, h2⟩ := hC w
  rw [hinj _ _ ((hio _).symm.trans h1), h2]

theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∃ io : PowerSeries (WK K) →+* Ainf l, (∀ x, I.io (letEmb Γ.emb x) = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] io x) ∧ io PowerSeries.X = WittVector.teichmuller l (AI.εroot s) - 1 ∧ ∀ w : WK K, Formalism.Per.θ l (io (PowerSeries.C w)) = intToOC (unr K) w :=
  fun _ _ _ AI _ s _ Γ _ I hI =>
    exists_io Γ.emb I.io _ (εroot_sub_not_unit AI s) I.io_π (exists_const Γ.emb I.io hI)

end GlobalTheory.PrismS.IoDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteIrrCharactersAndFinsumCentralIdempotentsEq
section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq.ZSumOne

open CategoryTheory

variable {G : Type} [Group G] [Fintype G]

theorem zOf_coeff (χ : G → ℂ) (y : G) : (zOf χ).coeff y = χ 1 / (Fintype.card G : ℂ) * χ y⁻¹ := by
  simp only [zOf, MonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply, MonoidAlgebra.single_apply,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem irr_one_eq_finrank {χ : G → ℂ} {V : FDRep ℂ G} (hV : ∀ x, V.character x = χ x) :
    χ 1 = (Module.finrank ℂ V : ℂ) := by
  rw [← hV 1, FDRep.char_one]

theorem zOf_eq_zIdem (χ : G → ℂ) (V : FDRep ℂ G) (hV : ∀ x, V.character x = χ x) :
    zOf χ = Formalism.IrreducibleCountingLemmas.TYPES.zIdem V := by
  have h1 := irr_one_eq_finrank hV
  unfold zOf Formalism.IrreducibleCountingLemmas.TYPES.zIdem
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [h1, ← hV x⁻¹]
  rfl

theorem zOf_injOn : Set.InjOn (zOf (G := G)) {χ | IsIrr χ} := by
  intro χ hχ χ' hχ' h
  obtain ⟨V, hs, hV⟩ := hχ
  obtain ⟨V', hs', hV'⟩ := hχ'
  have hc : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h1 := irr_one_eq_finrank hV
  have h1' := irr_one_eq_finrank hV'
  have e1 := congrArg (fun a => a.coeff 1) h
  simp only [zOf_coeff, inv_one] at e1
  rw [h1, h1'] at e1
  have e2 : ((Module.finrank ℂ V * Module.finrank ℂ V : ℕ) : ℂ) =
      ((Module.finrank ℂ V' * Module.finrank ℂ V' : ℕ) : ℂ) := by
    push_cast
    field_simp at e1
    linear_combination e1
  have hn : Module.finrank ℂ V = Module.finrank ℂ V' := Nat.mul_self_inj.mp (by exact_mod_cast e2)
  have h11 : χ 1 = χ' 1 := by rw [h1, h1', hn]
  haveI := PI.GreenLabelSurjWork.nontrivial_of_simple V hs
  have hpos : (Module.finrank ℂ V : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℂ) (M := V)).ne'
  have hk : χ 1 / (Fintype.card G : ℂ) ≠ 0 := div_ne_zero (h1 ▸ hpos) hc
  funext y
  have e3 := congrArg (fun a => a.coeff y⁻¹) h
  simp only [zOf_coeff, inv_inv] at e3
  rw [← h11] at e3
  exact mul_left_cancel₀ hk e3

theorem zOf_image :
    zOf '' {χ : G → ℂ | IsIrr χ} =
      {z : MonoidAlgebra ℂ G | ∃ τ : FDRep ℂ G, Simple τ ∧ Formalism.IrreducibleCountingLemmas.TYPES.zIdem τ = z} := by
  ext z
  constructor
  · rintro ⟨χ, ⟨V, hs, hV⟩, rfl⟩
    exact ⟨V, hs, (zOf_eq_zIdem χ V hV).symm⟩
  · rintro ⟨τ, hs, rfl⟩
    exact ⟨τ.character, ⟨τ, hs, fun _ => rfl⟩, zOf_eq_zIdem _ τ fun _ => rfl⟩

end GlobalTheory.GLq.ZSumOne

namespace GlobalTheory.GLq

theorem irr_finite_and_finsum_zOf_eq_one : ∀ (G : Type) [Group G] [Fintype G],
    {χ : G → ℂ | IsIrr χ}.Finite ∧ ∑ᶠ χ ∈ {χ : G → ℂ | IsIrr χ}, zOf χ = 1 := by
  intro G _ _
  have hZ := GlobalTheory.SerOSys.zIdem_finite_and_finsum_eq_one G
  rw [← ZSumOne.zOf_image] at hZ
  refine ⟨Set.Finite.of_finite_image hZ.1 ZSumOne.zOf_injOn, ?_⟩
  have himg := finsum_mem_image (f := fun z : MonoidAlgebra ℂ G => z) (ZSumOne.zOf_injOn (G := G))
  rw [← himg]
  exact hZ.2

end GlobalTheory.GLq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobFixedLatticeConditionSmulOfFrobeniusFixed
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PMon.ResR TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.ResR

theorem latC_smul_of_fr_fixed : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (r : ℕ) (n : Type) [Fintype n] [DecidableEq n] (U : Fin r → GL n P.R.BdR) (x y : Fin r × n) (a : n → P.R.B) (e : ↥(MaximalUnramifiedExtension l)), fr l r e = e → LatC P U x y a → LatC P U x y (e • a) := by
  intro l _ P r n _ _ U x y a e he h
  obtain ⟨h1, h2⟩ := h
  have hsm : ∀ i, (e • a) i = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B e * a i := fun i => by
    rw [Pi.smul_apply, Algebra.smul_def]
  have hev : ∀ (m : ℕ) (b : P.R.B), ev P m (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B e * b) = kd P (fr l m e) * ev P m b := by
    intro m b
    rw [← evHom_apply, map_mul, evHom_apply, evHom_apply, ev_kur]
  refine ⟨fun i => ?_, fun m => ?_⟩
  · rw [hsm]
    have key : ∀ k : ℕ, P.φB^[k] (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B e * a i) = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (fr l k e) * P.φB^[k] (a i) := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => rw [Function.iterate_succ_apply', ih, map_mul, Function.iterate_succ_apply', phiB_algebraMap, add_comm, fr_add, fr_one]
    rw [key, he, h1]
  · obtain ⟨w, hw, hw'⟩ := h2 m
    refine ⟨fun i => kd P (fr l m e) * w i, fun i => Fil_mul_left (kd_mem_Fil P _) (hw i), ?_⟩
    funext i
    rw [hsm, hev]
    have := congrFun hw' i
    rw [this]
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring

end GlobalTheory.PMon.ResR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisFixedTensorWittCompletePiAdicModEllStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisFixedTensorWitt_complete_piAdic_modEll : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (LL : FinExt l) (s : ℕ) (H : Set (GQ l)), piR AI LL s ∈ fixSub AI LL H → ∀ (k : ℕ) (f : ℕ → RW LL), (∀ i, f i ∈ fixSub AI LL H) → (∀ i, NearPi AI LL s (i + k) (f i)) → ∃ x ∈ fixSub AI LL H, ∀ m, NearPi AI LL s (m + k) (x - ∑ i ∈ Finset.range m, f i) := by
  first | exact @GlobalTheory.Decompl.fixSub_nearPi_complete | exact GlobalTheory.Decompl.fixSub_nearPi_complete | (intros; apply GlobalTheory.Decompl.fixSub_nearPi_complete <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisGroupFixedFieldBaseChangeLocalField
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem baseChange_fixedField :
    ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L] (A : Subgroup (L ≃ₐ[K] L)), ∃ j : (L ≃ₐ[↥(IntermediateField.fixedField A)] L) →* (L ≃ₐ[K] L), Function.Injective j ∧ j.range = A ∧ (∀ σ x, j σ x = σ x) ∧ ∀ i : ℤ, lowerRamificationGroup ↥(IntermediateField.fixedField A) L i = (lowerRamificationGroup K L i).comap j := by
  intro K L _ _ _ _ _ _ _ _ _ _ _ _ A
  refine ⟨AlgEquiv.restrictScalarsHom K, AlgEquiv.restrictScalarsHom_injective K, ?_, ?_, ?_⟩
  · rw [GroundTheory.LocalField.range_restrictScalarsHom, IntermediateField.fixingSubgroup_fixedField]
  · intro σ x
    rfl
  · intro i
    exact (lowerRamificationGroup_comap_restrictScalars (IntermediateField.fixedField A) i).symm

end GlobalTheory.PMon.Ram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisInvComplexPadicPeriodMatrixStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_inv_complexPadic_periodMatrix : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (ρ : ↥(GK K) →* GL n ℚ_[l]) (M : GL n ℂ_[l]), (∀ g : ↥(GK K), (ρ g : Matrix n n ℚ_[l]).map (algebraMap ℚ_[l] ℂ_[l]) * (M : Matrix n n ℂ_[l]).map (Formalism.Per.σC (g : GQ l)) = M) → ∀ g : ↥(GK K), ((M⁻¹ : GL n ℂ_[l]) : Matrix n n ℂ_[l]).map (Formalism.Per.σC (g : GQ l)) = ((M⁻¹ : GL n ℂ_[l]) : Matrix n n ℂ_[l]) * (ρ g : Matrix n n ℚ_[l]).map (algebraMap ℚ_[l] ℂ_[l]) := by
  first | exact @GlobalTheory.PMon.galois_inv_period_matrix | exact GlobalTheory.PMon.galois_inv_period_matrix | (intros; apply GlobalTheory.PMon.galois_inv_period_matrix <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussNormAcrisRadiusPosDefiniteStatement
section
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussNormAcrisRadius_pos_definite : ∀ (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l), x ≠ 0 → ∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → 0 < gC l ρ x := by
  first | exact @GlobalTheory.PMon.Gauss.gC_pos_target | exact GlobalTheory.PMon.Gauss.gC_pos_target | (intros; apply GlobalTheory.PMon.Gauss.gC_pos_target <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharLocPowEqOneOnLocalUnits
section
open NumberField IsDedekindDomain Formalism.L2.Host

namespace GlobalTheory.LocUnitPow

variable {L : Type} [Field L] [NumberField L]

theorem le_exp_neg_one' {γ : WithZero (Multiplicative ℤ)} (h : γ < 1) : γ ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne γ 0 with rfl | h0
  · exact zero_le
  · rw [← WithZero.exp_log h0] at h ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega

theorem val_pow_sub_one_le {v : HeightOneSpectrum (𝓞 L)} {z : v.adicCompletion L} (hz : Valued.v z = 1) (i : ℕ) :
    Valued.v (z ^ i - 1) ≤ Valued.v (z - 1) := by
  induction i with
  | zero => simp
  | succ m ih =>
    have e : z ^ (m + 1) - 1 = z ^ m * (z - 1) + (z ^ m - 1) := by ring
    rw [e]
    refine Valuation.map_add_le _ ?_ ih
    rw [map_mul, map_pow, hz, one_pow, one_mul]

theorem val_pow_sub_one_step {v : HeightOneSpectrum (𝓞 L)} {N : ℕ}
    (hN : Valued.v (N : v.adicCompletion L) ≤ WithZero.exp (-1 : ℤ))
    {z : v.adicCompletion L} (hz : Valued.v z = 1) {j : ℤ} (hj : Valued.v (z - 1) ≤ WithZero.exp (-j)) (hj1 : 1 ≤ j) :
    Valued.v (z ^ N - 1) ≤ WithZero.exp (-(j + 1)) := by
  have e : z ^ N - 1 = (z - 1) * ((∑ i ∈ Finset.range N, (z ^ i - 1)) + (N : v.adicCompletion L)) := by
    rw [← geom_sum_mul, Finset.sum_sub_distrib]
    simp [mul_comm]
  have hS : Valued.v ((∑ i ∈ Finset.range N, (z ^ i - 1)) + (N : v.adicCompletion L)) ≤ WithZero.exp (-1 : ℤ) := by
    refine Valuation.map_add_le _ ?_ hN
    refine Valuation.map_sum_le _ fun i _ => ?_
    exact (val_pow_sub_one_le hz i).trans (hj.trans (WithZero.exp_le_exp.mpr (by omega)))
  rw [e, map_mul]
  calc _ ≤ WithZero.exp (-j) * WithZero.exp (-1 : ℤ) := mul_le_mul' hj hS
    _ = _ := by rw [← WithZero.exp_add]; congr 1; ring

theorem val_pow_pow_sub_one_le {v : HeightOneSpectrum (𝓞 L)} {N : ℕ}
    (hN : Valued.v (N : v.adicCompletion L) ≤ WithZero.exp (-1 : ℤ))
    {z : v.adicCompletion L} (hz : Valued.v z = 1) (hz1 : Valued.v (z - 1) ≤ WithZero.exp (-1 : ℤ)) (k : ℕ) :
    Valued.v (z ^ (N ^ k) - 1) ≤ WithZero.exp (-((k : ℤ) + 1)) := by
  induction k with
  | zero => simpa using hz1
  | succ k ih =>
    rw [pow_succ, pow_mul]
    have hzk : Valued.v (z ^ N ^ k) = 1 := by rw [map_pow, hz, one_pow]
    have := val_pow_sub_one_step hN hzk ih (by omega)
    convert this using 3
    push_cast
    ring

theorem loc_pow_eq_one : ∀ (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L) (v : HeightOneSpectrum (𝓞 L))
    (x : (v.adicCompletion L)ˣ), Formalism.L2.Host.IsUnitAt v x → ∃ m : ℕ, 0 < m ∧ χ.loc v x ^ m = 1 := by
  intro L _ _ χ v x hx
  obtain ⟨n, hn⟩ := GlobalTheory.Mem.UnrAe.exists_levelLe χ v
  have := Formalism.UG.P.glint_finite_residueField (F := L) v
  let _ := Fintype.ofFinite (IsLocalRing.ResidueField (v.adicCompletionIntegers L))
  set N := Fintype.card (IsLocalRing.ResidueField (v.adicCompletionIntegers L)) with hNdef
  have hN2 : 1 < N := Fintype.one_lt_card
  have hNv : Valued.v (N : v.adicCompletion L) ≤ WithZero.exp (-1 : ℤ) := by
    have hr : IsLocalRing.residue (v.adicCompletionIntegers L) (N : v.adicCompletionIntegers L) = 0 := by
      rw [map_natCast]; exact FiniteField.cast_card_eq_zero _
    rw [IsLocalRing.residue_eq_zero_iff] at hr
    have hlt : Valued.v (((N : v.adicCompletionIntegers L)) : v.adicCompletion L) < 1 :=
      (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion L) (WithZero (Multiplicative ℤ))))).1 hr
    have e : (((N : v.adicCompletionIntegers L)) : v.adicCompletion L) = (N : v.adicCompletion L) := by
      push_cast; rfl
    rw [e] at hlt
    exact le_exp_neg_one' hlt
  have hxO : (x : v.adicCompletion L) ∈ v.adicCompletionIntegers L := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]; exact hx.le
  set y : v.adicCompletionIntegers L := ⟨x, hxO⟩
  have hyu : IsUnit y := HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.2 hx
  have hr : IsLocalRing.residue _ y ≠ 0 := by
    rw [ne_eq, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
    exact hyu
  have hp : IsLocalRing.residue _ (y ^ (N - 1) - 1) = 0 := by
    rw [map_sub, map_pow, map_one, FiniteField.pow_card_sub_one_eq_one _ hr, sub_self]
  rw [IsLocalRing.residue_eq_zero_iff] at hp
  have hlt : Valued.v (((y ^ (N - 1) - 1 : v.adicCompletionIntegers L)) : v.adicCompletion L) < 1 :=
    (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion L) (WithZero (Multiplicative ℤ))))).1 hp
  have e : (((y ^ (N - 1) - 1 : v.adicCompletionIntegers L)) : v.adicCompletion L) =
      (x : v.adicCompletion L) ^ (N - 1) - 1 := by
    push_cast; rfl
  rw [e] at hlt
  have hx1 := le_exp_neg_one' hlt
  have hz : Valued.v ((x : v.adicCompletion L) ^ (N - 1)) = 1 := by
    rw [map_pow, show Valued.v (x : v.adicCompletion L) = 1 from hx, one_pow]
  have key := val_pow_pow_sub_one_le hNv hz hx1 n
  refine ⟨(N - 1) * N ^ n, Nat.mul_pos (by omega) (pow_pos (by omega) _), ?_⟩
  rw [← map_pow]
  refine hn _ (GlobalTheory.Mem.UnrAe.isUnitAt_pow hx _) ?_
  rw [Units.val_pow_eq_pow_val, pow_mul]
  exact key.trans (WithZero.exp_le_exp.mpr (by omega))

end GlobalTheory.LocUnitPow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeEigenspaceSumDisjointComplStatement
section
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeEigenspaceSum_disjoint_compl : ∀ (D : D7) (i : D.nd.Loc) (Y : Set (D.nd.X i)), Disjoint (D.nd.eigSum i Y) (D.nd.eigSum i Yᶜ) := by
  first | exact @GlobalTheory.EtaJoin.eigSum_disjoint_compl | exact GlobalTheory.EtaJoin.eigSum_disjoint_compl | (intros; apply GlobalTheory.EtaJoin.eigSum_disjoint_compl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismaticFCrystalValueLocalPrismAinfWittTensorStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.Prism
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prismaticFCrystal_value_localPrism_ainf_wittTensor : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (PS PW : Obj l ↥(OL K)) (ev : Hom PS PW) (ioH : Hom PS (ainfObj K)) (gH : ↥(GK K) → Hom PS PS) (π Q : PS.A) (ψ : PS.A →+* WCb l), (∀ x, ψ x = inclW l (ainfId K (ioH.f x))) → (∀ g, ioH.comp (gH g) = (ainfHom K g).comp ioH) → (∀ g, ev.comp (gH g) = ev) → RingHom.ker ev.f = Ideal.span {π} → Q ∈ PS.I → IsLocalRing PS.A → ψ Q ≠ 0 → ∀ (T : Type) [AddCommGroup T] [Module ℤ_[l] T] (ρ : ↥(GK K) → (T →ₗ[ℤ_[l]] T)) (E : FCrys l ↥(OL K)) (j : E.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T)), Realises K E (ainfObj K) (ainfId K) T ρ j → ∃ (q : ℕ) (b : Module.Basis (Fin q) PS.A (E.M PS)) (c : Module.Basis (Fin q) (WCb l) (WCb l ⊗[ℤ_[l]] T)), (∀ i, c i = j (E.tr ioH (b i))) ∧ (∀ x, ∃ (k : ℕ) (m : E.M PS), ψ Q ^ k • TensorProduct.map (frobW l).toLinearMap LinearMap.id (j (E.tr ioH x)) = j (E.tr ioH m)) ∧ (∀ x, ∃ (k : ℕ) (s : Fin q → PS.A), ψ Q ^ k • j (E.tr ioH x) = ∑ i, ψ (s i) • TensorProduct.map (frobW l).toLinearMap LinearMap.id (c i)) ∧ (∀ (g : ↥(GK K)) x, TensorProduct.map (galW l (g : GQ l)).toLinearMap (ρ g) (j (E.tr ioH x)) = j (E.tr ioH (E.tr (gH g) x))) ∧ (∀ g x, ∃ y, E.tr (gH g) x - x = π • y) := by
  first | exact @GlobalTheory.Prism.LocalValue.main | exact GlobalTheory.Prism.LocalValue.main | (intros; apply GlobalTheory.Prism.LocalValue.main <;> assumption)
end

