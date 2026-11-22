import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0052
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0047
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0013
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0006
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0039
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0009
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0048
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0014
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0008
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0010
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0002
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0037
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0049
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0020
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0007
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0005

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CompletelyReducibleKroneckerPowerTransposeStatement
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completelyReducible_kroneckerPower_transpose : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → SS Γ → ∀ n : ℕ, SS ((fun g => (tpow n g)ᵀ) '' Γ) := by
  first | exact @GlobalTheory.ClassFin.ss_tpow_transpose | exact GlobalTheory.ClassFin.ss_tpow_transpose | (intros; apply GlobalTheory.ClassFin.ss_tpow_transpose <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsComplexPolyBlockDiagPartOfFibreConst
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.FibreDescent

variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def rtr (g : Matrix ι ι ℂ) : MvPolynomial (ι × ι) ℂ →ₐ[ℂ] MvPolynomial (ι × ι) ℂ :=
  MvPolynomial.aeval fun ij : ι × ι => ∑ k, g k ij.2 • MvPolynomial.X (ij.1, k)

omit [Fintype ι] [DecidableEq ι] in
lemma evC_add (p q : MvPolynomial (ι × ι) ℂ) (y : Matrix ι ι ℂ) : evC (p + q) y = evC p y + evC q y := by
  simp [evC]

omit [Fintype ι] [DecidableEq ι] in
lemma evC_mul (p q : MvPolynomial (ι × ι) ℂ) (y : Matrix ι ι ℂ) : evC (p * q) y = evC p y * evC q y := by
  simp [evC]

omit [Fintype ι] [DecidableEq ι] in
lemma evC_smul (c : ℂ) (p : MvPolynomial (ι × ι) ℂ) (y : Matrix ι ι ℂ) : evC (c • p) y = c * evC p y := by
  simp [evC, MvPolynomial.smul_eval]

omit [DecidableEq ι] in
lemma evC_rtr (g y : Matrix ι ι ℂ) (f : MvPolynomial (ι × ι) ℂ) : evC (rtr g f) y = evC f (y * g) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [evC, rtr]
  | add p q hp hq => rw [map_add, evC_add, evC_add, hp, hq]
  | mul_X p ij hp =>
    rw [map_mul, evC_mul, evC_mul, hp]
    congr 1
    simp [evC, rtr, Matrix.mul_apply, MvPolynomial.smul_eval, mul_comm]

omit [DecidableEq ι] in
lemma evC_ltr (g y : Matrix ι ι ℂ) (f : MvPolynomial (ι × ι) ℂ) : evC (ltr g f) y = evC f (g * y) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [evC, ltr]
  | add p q hp hq => rw [map_add, evC_add, evC_add, hp, hq]
  | mul_X p ij hp =>
    rw [map_mul, evC_mul, evC_mul, hp]
    congr 1
    simp [evC, ltr, Matrix.mul_apply]

omit [Fintype ι] [DecidableEq ι] in
lemma evC_map (p : MvPolynomial (ι × ι) ℚ) (y : Matrix ι ι ℂ) :
    evC (MvPolynomial.map (algebraMap ℚ ℂ) p) y = ev p y := by
  rw [evC, ev, MvPolynomial.eval_map, MvPolynomial.aeval_def]

omit [DecidableEq ι] in

lemma exists_fg_rtr (f : MvPolynomial (ι × ι) ℂ) :
    ∃ V : Submodule ℂ (MvPolynomial (ι × ι) ℂ), V.FG ∧ ∀ g, rtr g f ∈ V := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    refine ⟨Submodule.span ℂ {MvPolynomial.C a}, Submodule.fg_span (Set.finite_singleton _), fun g => ?_⟩
    apply Submodule.subset_span
    simp [rtr]
  | add p q hp hq =>
    obtain ⟨V, hV, h⟩ := hp
    obtain ⟨V', hV', h'⟩ := hq
    refine ⟨V ⊔ V', hV.sup hV', fun g => ?_⟩
    rw [map_add]
    exact Submodule.add_mem_sup (h g) (h' g)
  | mul_X p ij hp =>
    obtain ⟨V, hV, h⟩ := hp
    refine ⟨V * Submodule.span ℂ (Set.range MvPolynomial.X),
      hV.mul (Submodule.fg_span (Set.finite_range _)), fun g => ?_⟩
    rw [map_mul]
    refine Submodule.mul_mem_mul (h g) ?_
    rw [rtr, MvPolynomial.aeval_X]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

omit [DecidableEq ι] in

lemma exists_finset_rtr (Γ : Set (Matrix ι ι ℂ)) (f : MvPolynomial (ι × ι) ℂ) :
    ∃ s : Finset (MvPolynomial (ι × ι) ℂ), (∀ p ∈ s, ∃ g ∈ Γ, p = rtr g f) ∧
      ∀ g ∈ Γ, rtr g f ∈ Submodule.span ℂ (s : Set (MvPolynomial (ι × ι) ℂ)) := by
  obtain ⟨V, hV, h⟩ := exists_fg_rtr f
  have hle : Submodule.span ℂ ((fun g => rtr g f) '' Γ) ≤ V := by
    rw [Submodule.span_le]
    rintro _ ⟨g, -, rfl⟩
    exact h g
  have hfg : (Submodule.span ℂ ((fun g => rtr g f) '' Γ)).FG := by
    have : Module.Finite ℂ V := Module.Finite.iff_fg.2 hV
    exact Module.Finite.iff_fg.1 (Submodule.finiteDimensional_of_le hle)
  obtain ⟨s, hs, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 hfg
  refine ⟨s, fun p hp => ?_, fun g hg => ?_⟩
  · obtain ⟨g, hg, rfl⟩ := hs hp
    exact ⟨g, hg, rfl⟩
  · rw [← hspan]
    exact Submodule.subset_span ⟨g, hg, rfl⟩

def multIdeal (Γ : Set (Matrix ι ι ℂ)) (π : Matrix ι ι ℂ → Matrix ι ι ℂ) (f : MvPolynomial (ι × ι) ℂ) :
    Ideal (MvPolynomial (ι × ι) ℂ) where
  carrier := {b | ∀ g ∈ Γ, ∃ b' : MvPolynomial (ι × ι) ℂ, ∀ x ∈ Γ,
    evC b (π x) * evC f (x * g) = evC b' (π x)}
  zero_mem' := fun g _ => ⟨0, fun x _ => by simp [evC]⟩
  add_mem' := by
    intro a b ha hb g hg
    obtain ⟨a', ha'⟩ := ha g hg
    obtain ⟨b', hb'⟩ := hb g hg
    exact ⟨a' + b', fun x hx => by rw [evC_add, evC_add, add_mul, ha' x hx, hb' x hx]⟩
  smul_mem' := by
    intro c b hb g hg
    obtain ⟨b', hb'⟩ := hb g hg
    exact ⟨c * b', fun x hx => by rw [smul_eq_mul, evC_mul, evC_mul, mul_assoc, hb' x hx]⟩

omit [DecidableEq ι] in
lemma exists_common_zero (D : Ideal (MvPolynomial (ι × ι) ℂ)) (hD : D ≠ ⊤) :
    ∃ z : Matrix ι ι ℂ, ∀ b ∈ D, evC b z = 0 := by
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal D hD
  obtain ⟨x, rfl⟩ := MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton.1 hM
  refine ⟨Matrix.of fun i j => x (i, j), fun b hb => ?_⟩
  have := (MvPolynomial.mem_vanishingIdeal_singleton_iff _ _).1 (hle hb)
  simpa [evC, MvPolynomial.aeval_eq_eval] using this

end GlobalTheory.ClassFin.FibreDescent

open GlobalTheory.ClassFin.FibreDescent in

theorem GlobalTheory.ClassFin.exists_evC_blk_of_fibre_const : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (e : Matrix ι ι ℚ), IsQGroup Γ → e * e = e → (∀ g ∈ Γ, (1 - e.map (algebraMap ℚ ℂ)) * g * e.map (algebraMap ℚ ℂ) = 0) → ∀ f : MvPolynomial (ι × ι) ℂ, (∀ x ∈ Γ, ∀ x' ∈ Γ, blk e x = blk e x' → evC f x = evC f x') → ∃ b : MvPolynomial (ι × ι) ℂ, ∀ x ∈ Γ, evC f x = evC b (blk e x) := by
  intro ι _ _ Γ e hΓ he htri f hf
  have hmul : ∀ x ∈ Γ, ∀ y ∈ Γ, blk e (x * y) = blk e x * blk e y := fun x hx y hy =>
    ((GlobalTheory.ClassFin.blk_mul_of_triangular ι e ℂ he).2.1 x y (htri x hx) (htri y hy)).1
  have hpre : IsPre (blk e '' Γ) := GlobalTheory.ClassFin.isPre_blk_image ι Γ e hΓ.toIsPre he htri
  obtain ⟨-, hm, hadj, hdet⟩ := GlobalTheory.T.ratZariskiClosurePoints_isGroup ι _ hpre ℂ
  obtain ⟨s, hs, hspan⟩ := exists_finset_rtr Γ f
  obtain ⟨b₀, ⟨x₀, hx₀, hb₀⟩, hb⟩ := GlobalTheory.T.exists_multiplier_descend_blockDiagPartOfRatIdempotent ι Γ e hΓ.closed ⟨1, hΓ.one_mem⟩ s (by
    intro p hp x hx x' hx' hxx
    obtain ⟨g, hg, rfl⟩ := hs p hp
    rw [evC_rtr, evC_rtr]
    exact hf _ (hΓ.mul_mem _ hx _ hg) _ (hΓ.mul_mem _ hx' _ hg)
      (by rw [hmul _ hx _ hg, hmul _ hx' _ hg, hxx]))
  have hb₀D : b₀ ∈ multIdeal Γ (blk e) f := by
    intro g hg
    have key : ∀ p ∈ Submodule.span ℂ (s : Set (MvPolynomial (ι × ι) ℂ)),
        ∃ b' : MvPolynomial (ι × ι) ℂ, ∀ x ∈ Γ, evC b₀ (blk e x) * evC p x = evC b' (blk e x) := by
      intro p hp
      induction hp using Submodule.span_induction with
      | mem p hp => exact hb p hp
      | zero => exact ⟨0, fun x _ => by simp [evC]⟩
      | add p q _ _ hp hq =>
        obtain ⟨a', ha'⟩ := hp
        obtain ⟨b', hb'⟩ := hq
        exact ⟨a' + b', fun x hx => by rw [evC_add, evC_add, mul_add, ha' x hx, hb' x hx]⟩
      | smul c p _ hp =>
        obtain ⟨a', ha'⟩ := hp
        exact ⟨c • a', fun x hx => by rw [evC_smul, evC_smul, ← ha' x hx]; ring⟩
    obtain ⟨b', hb'⟩ := key _ (hspan g hg)
    exact ⟨b', fun x hx => by rw [← hb' x hx, evC_rtr]⟩
  have hstab : ∀ h ∈ Γ, rtr (blk e h) b₀ ∈ multIdeal Γ (blk e) f := by
    intro h hh g hg
    obtain ⟨b', hb'⟩ := hb₀D (h.adjugate * g) (hΓ.mul_mem _ (hΓ.adj_mem _ hh) _ hg)
    refine ⟨rtr (blk e h) b', fun x hx => ?_⟩
    rw [evC_rtr, evC_rtr, ← hmul _ hx _ hh, ← hb' _ (hΓ.mul_mem _ hx _ hh), Matrix.mul_assoc,
      ← Matrix.mul_assoc h, Matrix.mul_adjugate, hΓ.det_eq _ hh, one_smul, Matrix.one_mul]
  have htop : multIdeal Γ (blk e) f = ⊤ := by
    by_contra hD
    obtain ⟨z, hz⟩ := exists_common_zero _ hD
    have hzp : z ∈ pts (blk e '' Γ) ℂ := by
      intro p hp
      rw [← evC_map]
      refine hz _ fun g _ => ⟨0, fun x hx => ?_⟩
      rw [evC_map, hp _ ⟨x, hx, rfl⟩]
      simp [evC]
    have hx₀p : blk e x₀ ∈ pts (blk e '' Γ) ℂ := fun p hp => hp _ ⟨x₀, hx₀, rfl⟩
    have := GlobalTheory.T.evalComplexPoly_eq_zero_on_ratZariskiClosure ι _ hpre.aut_mem (ltr z b₀) (by
      rintro _ ⟨h, hh, rfl⟩
      rw [evC_ltr, ← evC_rtr]
      exact hz _ (hstab h hh)) _ (hm _ (hadj z hzp) _ hx₀p)
    rw [evC_ltr, ← Matrix.mul_assoc, Matrix.mul_adjugate, hdet z hzp, one_smul, Matrix.one_mul] at this
    exact hb₀ this
  have h1 : (1 : MvPolynomial (ι × ι) ℂ) ∈ multIdeal Γ (blk e) f := htop ▸ Submodule.mem_top
  obtain ⟨b, hb⟩ := h1 1 hΓ.one_mem
  refine ⟨b, fun x hx => ?_⟩
  rw [← hb x hx, Matrix.mul_one]
  simp [evC]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsPlaceIsSquareAndNotIsSquare
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem exists_place_isSquare_and_not_isSquare :
    ∀ (F : Type) [Field F] [NumberField F] (δ u : F) (S₀ : Finset (HeightOneSpectrum (𝓞 F))), δ ≠ 0 → u ≠ 0 → ¬ IsSquare δ → ¬ IsSquare u → ¬ IsSquare (u * δ) → ∃ v, v ∉ S₀ ∧ IsSquare (algebraMap F (v.adicCompletion F) δ) ∧ ¬ IsSquare (algebraMap F (v.adicCompletion F) u) := by
  classical
  intro F _ _ δ u S₀ hδ hu hδs hus huδs
  obtain ⟨E, _, _, _, θ, σ, hq⟩ := exists_isQuad F δ hδs
  have hbasic := isQuad_basic F E δ θ σ hq
  have huE : ¬ IsSquare (algebraMap F E u) := fun h => (hbasic.2.2.2.2.2.1 u h).elim hus huδs
  have hu0E : algebraMap F E u ≠ 0 := (map_ne_zero_iff _ (algebraMap F E).injective).mpr hu
  obtain ⟨S, hS₀, hSunits⟩ := exists_superset_mem_sUnits F
    {Units.mk0 (2 : F) two_ne_zero, Units.mk0 u hu, Units.mk0 (u * δ) (mul_ne_zero hu hδ)} S₀
  have hgood : ∀ v, v ∉ S → ∀ x ∈ ({Units.mk0 (2 : F) two_ne_zero, Units.mk0 u hu,
      Units.mk0 (u * δ) (mul_ne_zero hu hδ)} : Finset Fˣ), v.valuation F (x : F) = 1 :=
    fun v hv x hx => (mem_sUnits F S x).mp (hSunits S subset_rfl x hx) v hv
  obtain ⟨hover, -, -⟩ := places_over F E
  obtain ⟨SE, hSE⟩ := hover S
  obtain ⟨w, hwS, hwu⟩ := GlobalTheory.T.exists_place_not_isSquare_adicCompletion E (algebraMap F E u) SE hu0E huE
  have hvS : w.under (𝓞 F) ∉ S := fun h => hwS ((hSE w).mpr h)
  obtain ⟨φ, hφ⟩ := exists_ringHom_adicCompletion_under F E w
  have hθ : algebraMap E (w.adicCompletion E) θ ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap E (w.adicCompletion E)).injective).mpr hq.root_ne_zero
  have hnu : ¬ IsSquare (algebraMap F ((w.under (𝓞 F)).adicCompletion F) u) := by
    intro h
    apply hwu
    have h' := h.map φ
    rwa [hφ] at h'
  have hnuδ : ¬ IsSquare (algebraMap F ((w.under (𝓞 F)).adicCompletion F) (u * δ)) := by
    intro h
    apply hwu
    have h' := h.map φ
    rw [hφ, map_mul, map_mul, ← hq.sq, map_pow] at h'
    obtain ⟨r, hr⟩ := h'
    refine ⟨r / algebraMap E (w.adicCompletion E) θ, ?_⟩
    rw [div_mul_div_comm, ← hr]
    field_simp
  have hval : ∀ x : F, Valued.v (algebraMap F ((w.under (𝓞 F)).adicCompletion F) x) =
      (w.under (𝓞 F)).valuation F x := fun x =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (w.under (𝓞 F)) x
  have h2 : Valued.v (2 : (w.under (𝓞 F)).adicCompletion F) = 1 := by
    rw [show (2 : (w.under (𝓞 F)).adicCompletion F) = algebraMap F _ 2 from (map_ofNat _ 2).symm,
      hval]
    simpa using hgood _ hvS (Units.mk0 (2 : F) two_ne_zero) (Finset.mem_insert_self _ _)
  have hvu : Valued.v (algebraMap F ((w.under (𝓞 F)).adicCompletion F) u) = 1 := by
    rw [hval]
    simpa using hgood _ hvS (Units.mk0 u hu)
      (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have hvuδ : Valued.v (algebraMap F ((w.under (𝓞 F)).adicCompletion F) (u * δ)) = 1 := by
    rw [hval]
    simpa using hgood _ hvS (Units.mk0 (u * δ) (mul_ne_zero hu hδ))
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
  obtain ⟨s, hs⟩ := isSquare_mul_of_nonsquare_units F (w.under (𝓞 F)) h2 _ _ hvu hvuδ hnu hnuδ
  have ha : algebraMap F ((w.under (𝓞 F)).adicCompletion F) u ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap F _).injective).mpr hu
  refine ⟨w.under (𝓞 F), fun h => hvS (hS₀ h), ⟨s / algebraMap F _ u, ?_⟩, hnu⟩
  rw [div_mul_div_comm, ← hs, map_mul]
  field_simp

end GlobalTheory.QNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsPlaceNotPowAdicCompletion
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem exists_not_mem_not_pow_completion :
    ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [IsTotallyComplex F] (ζ u : F) (S₀ : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → IsPrimitiveRoot ζ p → u ≠ 0 → (∀ r : F, r ^ p ≠ u) → ∃ v, v ∉ S₀ ∧ ∀ r : v.adicCompletion F, r ^ p ≠ algebraMap F (v.adicCompletion F) u := by
  classical
  intro p F _ _ _ ζ u S₀ hp hζ hu hns
  by_contra hcon
  push Not at hcon
  have hle : ∀ S, finNorm p F u S₀ ≤ finNorm p F u S := by
    intro S x hx
    rw [finNorm] at hx ⊢
    simp only [Subgroup.mem_iInf] at hx ⊢
    intro v _
    by_cases hv : v ∈ S₀
    · exact hx v hv
    · haveI : CharZero (v.adicCompletion F) :=
        charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
      obtain ⟨r, hr⟩ := hcon v hv
      rw [GlobalTheory.T.unitsLocalKummerNorms_eq_top_of_pow p F _ _ u r hp.pos hu hr]
      exact Subgroup.mem_top x
  have hidx := (GlobalTheory.T.pow_countPlacesNotLocalPower_le_index p F ζ u S₀ hp hζ).1
  haveI : (finNorm p F u S₀).FiniteIndex := ⟨hidx⟩
  haveI : Fintype (Fˣ ⧸ finNorm p F u S₀) := Fintype.ofFinite _
  obtain ⟨S₁, -, hS₁⟩ := exists_superset_mem_sUnits F
    (insert (Units.mk0 u hu)
      (Finset.univ.image (fun q : Fˣ ⧸ finNorm p F u S₀ => q.out))) S₀
  obtain ⟨S, hS, hadm⟩ := (GlobalTheory.T.exists_admissiblePlacesContainingPrime_superset_mono p F hp.pos).1 S₁
  have hX := hS₁ S hS
  refine GlobalTheory.T.sUnits_sup_localKummerNorms_ne_top p F ζ (Units.mk0 u hu) S hp hζ hadm
    (hX _ (Finset.mem_insert_self _ _)) hns ?_
  rw [eq_top_iff]
  intro x _
  have hy : (QuotientGroup.mk x : Fˣ ⧸ finNorm p F u S₀).out ∈ sUnits F S :=
    hX _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
  have hz : ((QuotientGroup.mk x : Fˣ ⧸ finNorm p F u S₀).out)⁻¹ * x ∈ finNorm p F u S₀ := by
    rw [← QuotientGroup.eq, QuotientGroup.out_eq']
  have hx : x = (QuotientGroup.mk x : Fˣ ⧸ finNorm p F u S₀).out *
      (((QuotientGroup.mk x : Fˣ ⧸ finNorm p F u S₀).out)⁻¹ * x) := by
    rw [mul_inv_cancel_left]
  rw [hx]
  exact Subgroup.mul_mem_sup hy (hle S hz)

end GlobalTheory.CNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteIntegralCosetsOfBoundedDenominator
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem adjugate_entry_mem_subring {ι : Type} [Fintype ι] [DecidableEq ι] {R : Type} [CommRing R]
    (R₀ : Subring R) (A : Matrix ι ι R) (hA : ∀ i j, A i j ∈ R₀) (i j : ι) : A.adjugate i j ∈ R₀ := by
  let B : Matrix ι ι R₀ := Matrix.of fun i j => ⟨A i j, hA i j⟩
  have hB : A = R₀.subtype.mapMatrix B := by
    ext i j; rfl
  rw [hB, ← RingHom.map_adjugate]
  exact (B.adjugate i j).2

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IdealCharacterLContinuationNeZeroOne
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory

open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical in
open scoped ContDiff nonZeroDivisors in
private theorem two_le_absNorm_heightOneSpectrum {K : Type} [Field K] [NumberField K]
    (P : HeightOneSpectrum (𝓞 K)) : 2 ≤ Ideal.absNorm P.asIdeal := by
  have h0 : Ideal.absNorm P.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr P.ne_bot
  have h1 : Ideal.absNorm P.asIdeal ≠ 1 := Ideal.absNorm_eq_one_iff.not.mpr P.isPrime.ne_top
  omega

open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical in
open scoped ContDiff nonZeroDivisors in
private theorem one_sub_mul_natCast_cpow_neg_ne_zero {c : ℂ} (hc : ‖c‖ ≤ 1) {n : ℕ} (hn : 2 ≤ n)
    {s : ℂ} (hs : 0 < s.re) : 1 - c * (n : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have h1 : c * (n : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h).symm
  have h2 : ‖(n : ℂ) ^ (-s)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (by omega : 1 < n)) (by linarith)
  have h3 := congrArg norm h1
  rw [norm_mul, norm_one] at h3
  nlinarith [norm_nonneg c, norm_nonneg ((n : ℂ) ^ (-s))]

open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical in
open scoped ContDiff nonZeroDivisors in

theorem _root_.GlobalTheory.idealCharacterL_continuation_ne_zero_one :
    ∀ (K : Type) [Field K] [NumberField K] (m : Ideal (𝓞 K)) (X : Ideal (𝓞 K) → ℂ)
    (φ : mixedSpace K → ℂ), m ≠ ⊥ → X ⊥ = 0 → (∀ I J, X (I * J) = X I * X J) →
    (∀ I, I ≠ ⊥ → I ⊔ m = ⊤ → ‖X I‖ = 1) → (∀ I, I ⊔ m ≠ ⊤ → X I = 0) →
    (∀ x y, φ (x * y) = φ x * φ y) → (∀ (t : ℝ) x, 0 < t → φ (t • x) = φ x) →
    ContDiffOn ℝ ∞ φ {x | mixedEmbedding.norm x ≠ 0} →
    (∀ x, mixedEmbedding.norm x ≠ 0 → ‖φ x‖ = 1) →
    (∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ m → X (Ideal.span {β}) = φ (mixedEmbedding K β)) →
    (∃ J, J ≠ ⊥ ∧ J ⊔ m = ⊤ ∧ X J ≠ 1) → ∀ c : HeightOneSpectrum (𝓞 K) → ℂ,
    (∀ P, ‖c P‖ ≤ 1) → (∀ P, ¬ m ≤ P.asIdeal → c P = X P.asIdeal) →
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L {s | 0 < s.re} ∧ (∀ s : ℂ, 1 < s.re →
      L s = Complex.exp (∑' P : HeightOneSpectrum (𝓞 K),
        -Complex.log (1 - c P * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s)))) ∧ L 1 ≠ 0 := by
  intro K _ _ m X φ hm hXbot hXmul hXnorm hXzero hφmul hφsmul hφsmooth hφnorm hXφ hJ c hc hcX
  have hXtop : X ⊤ = 1 := by
    have h1 := hXnorm ⊤ top_ne_bot (top_sup_eq m)
    have h2 : X ⊤ = X ⊤ * X ⊤ := by rw [← hXmul, Ideal.top_mul]
    have h3 : X ⊤ ≠ 0 := fun h => by rw [h, norm_zero] at h1; exact zero_ne_one h1
    exact mul_left_cancel₀ h3 (by rw [mul_one]; exact h2.symm)
  have hXle : ∀ I, ‖X I‖ ≤ 1 := by
    intro I
    by_cases hI : I = ⊥
    · rw [hI, hXbot, norm_zero]
      exact zero_le_one
    by_cases hIm : I ⊔ m = ⊤
    · rw [hXnorm I hI hIm]
    · rw [hXzero I hIm, norm_zero]
      exact zero_le_one
  obtain ⟨Z, hZd, hZ, hZ1⟩ := _root_.GlobalTheory.idealCharacter_LSeries_continuation K m X φ hm hXbot hXmul hXnorm
    hXzero hφmul hφsmul hφsmooth hφnorm hXφ
  have hZ0 := hZ1 hJ
  let LX : ℂ → ℂ := dslope Z 1
  have hLXd : Differentiable ℂ LX := by
    rw [← differentiableOn_univ]
    exact (Complex.differentiableOn_dslope Filter.univ_mem).mpr hZd.differentiableOn
  have hLX : ∀ s : ℂ, 1 < s.re → LX s = Complex.exp (∑' P : HeightOneSpectrum (𝓞 K),
      -Complex.log (1 - X P.asIdeal * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s))) := by
    intro s hs
    have hs1 : s ≠ 1 := fun h => by rw [h, Complex.one_re] at hs; exact lt_irrefl _ hs
    have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    rw [← _root_.GlobalTheory.tsum_ideal_mul_absNorm_cpow_eq_exp_tsum K X hXbot hXtop hXmul hXle s hs]
    simp only [LX, dslope_of_ne _ hs1, slope_def_field, hZ s hs, hZ0, sub_zero]
    field_simp
  obtain ⟨Zζ, hZζd, hZζ⟩ := _root_.GlobalTheory.dedekindZeta_eulerProduct_mul_sub_one_entire K
  have hsum : ∀ σ : ℝ, 1 < σ → Summable fun P : HeightOneSpectrum (𝓞 K) =>
      ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (-σ) :=
    fun σ hσ => ((_root_.GlobalTheory.countable_ideal_and_summable_absNorm_rpow K).2 σ hσ).2
  have hne : Nonempty (HeightOneSpectrum (𝓞 K)) := by
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 K)
    exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField K)⟩⟩
  have hLX1 : LX 1 ≠ 0 := _root_.GlobalTheory.eulerProduct_ne_zero_one_of_entire (HeightOneSpectrum (𝓞 K))
    (fun P => Ideal.absNorm P.asIdeal) (fun P => X P.asIdeal) two_le_absNorm_heightOneSpectrum
    (fun P => hXle _) hsum hne Zζ LX hZζd hLXd hZζ hLX
  have hfin : {P : HeightOneSpectrum (𝓞 K) | P.asIdeal ∣ m}.Finite := Ideal.finite_factors hm
  let S := hfin.toFinset
  have hmemS : ∀ P, P ∈ S ↔ m ≤ P.asIdeal := fun P => by simp [S, Ideal.dvd_iff_le]
  have hfac : ∀ (P : HeightOneSpectrum (𝓞 K)) (s : ℂ), 0 < s.re →
      1 - c P * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s) ≠ 0 :=
    fun P s hs => one_sub_mul_natCast_cpow_neg_ne_zero (hc P) (two_le_absNorm_heightOneSpectrum P) hs
  let F : ℂ → ℂ := ∏ P ∈ S, fun s => (1 - c P * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹
  have hF : ∀ s, F s = ∏ P ∈ S, (1 - c P * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹ :=
    fun s => by simp [F, Finset.prod_apply]
  refine ⟨fun s => LX s * F s, ?_, ?_, ?_⟩
  · apply hLXd.differentiableOn.mul
    apply DifferentiableOn.finset_prod
    intro P _
    refine DifferentiableOn.inv ?_ (fun s hs => hfac P s hs)
    refine DifferentiableOn.const_sub ?_ _
    refine DifferentiableOn.const_mul ?_ _
    intro s _
    refine DifferentiableAt.differentiableWithinAt ?_
    exact differentiableAt_id.neg.const_cpow
      (Or.inl (Nat.cast_ne_zero.mpr (by have := two_le_absNorm_heightOneSpectrum P; omega)))
  · intro s hs
    have hs0 : 0 < s.re := by linarith
    obtain ⟨hsa, -⟩ := (_root_.GlobalTheory.eulerProduct_eq_exp_and_pos (HeightOneSpectrum (𝓞 K))
      (fun P => Ideal.absNorm P.asIdeal) (fun P => X P.asIdeal) two_le_absNorm_heightOneSpectrum
      (fun P => hXle _) hsum).1 s hs
    have hsplit : ∀ P : HeightOneSpectrum (𝓞 K),
        -Complex.log (1 - c P * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s)) =
        -Complex.log (1 - X P.asIdeal * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s)) +
        (if P ∈ S then -Complex.log (1 - c P * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s))
          else 0) := by
      intro P
      by_cases hP : P ∈ S
      · rw [if_pos hP]
        have hXP : X P.asIdeal = 0 := hXzero _ (by
          rw [sup_eq_left.mpr ((hmemS P).mp hP)]
          exact P.isPrime.ne_top)
        rw [hXP, zero_mul, sub_zero, Complex.log_one, neg_zero, zero_add]
      · rw [if_neg hP, add_zero, hcX P (fun h => hP ((hmemS P).mpr h))]
    show LX s * F s = _
    rw [tsum_congr hsplit, hsa.tsum_add (summable_of_ne_finset_zero (s := S) fun P hP => if_neg hP),
      tsum_eq_sum (s := S) (fun P hP => if_neg hP), Complex.exp_add, ← hLX s hs, hF,
      Complex.exp_sum]
    congr 1
    refine Finset.prod_congr rfl fun P hP => ?_
    rw [if_pos hP, Complex.exp_neg, Complex.exp_log (hfac P s hs0)]
  · show LX 1 * F 1 ≠ 0
    rw [hF]
    exact mul_ne_zero hLX1 (Finset.prod_ne_zero_iff.mpr fun P _ => inv_ne_zero (hfac P 1 (by simp)))

end GlobalTheory
end

