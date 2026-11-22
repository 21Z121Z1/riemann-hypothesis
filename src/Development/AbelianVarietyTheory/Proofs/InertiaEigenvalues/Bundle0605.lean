import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0594
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0541
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0587
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0570
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0564
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0568
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0425
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0475
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0588
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0405
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0458
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0423
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0563
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0408
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0482
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0192

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MuPowSmulAcrisLatticeMemAcrisTensorStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mu_pow_smul_acrisLattice_mem_acrisTensor : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T) (α β : ℕ), (∀ m ∈ P.L, E K l e ^ α • m ∈ P.M) → (∀ m ∈ P.M, E K l e ^ β • m ∈ P.L) → ∀ (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T), IsCrisCmp I jB → ∀ ε : OCb l, IsEps ε → ∀ z : ι → OCr l O, ∃ w : TW (OCr l O) T, toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ α) • jB (fun i => toOB l O (z i)) = TWincl (toOB l O) T w := by
  first | exact @GlobalTheory.BKGal.CrisInt.mu_pow_smul_mem | exact GlobalTheory.BKGal.CrisInt.mu_pow_smul_mem | (intros; apply GlobalTheory.BKGal.CrisInt.mu_pow_smul_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MultisetProdMapProductEqProdProd
section
noncomputable section

namespace GlobalTheory.JSW

open Finset

theorem cauchy_local {m n : ℕ} (hmn : m ≤ n) (α : Fin n → ℂ) (β : Fin m → ℂ) (T : ℂ)
    (hs : Summable fun l : {l : Fin m → ℕ // Antitone l} =>
      ‖schurAt (padTo hmn l.1) α * schurAt l.1 β‖ * ‖T‖ ^ (∑ i, l.1 i)) :
    (∀ i j, 1 - α i * β j * T ≠ 0) ∧
    HasSum (fun l : {l : Fin m → ℕ // Antitone l} =>
      schurAt (padTo hmn l.1) α * schurAt l.1 β * T ^ (∑ i, l.1 i))
      (∏ i, ∏ j, (1 - α i * β j * T)⁻¹) := by
  set G : (Fin m → ℕ) → ℂ := fun l => schurAt (padTo hmn l) α * schurAt l β * T ^ (∑ i, l i) with hGdef
  have hG : Summable fun l : {l : Fin m → ℕ // Antitone l} => ‖G l.1‖ := by
    refine hs.congr fun l => ?_
    simp [G, norm_mul, norm_pow]
  obtain ⟨hsum, htrans⟩ := GlobalTheory.T.hasSum_regroup_antitonePartitions_by_degree G hG
  have hc : (fun d => ∑ l ∈ antiParts m d, G l) = fun d => T ^ d * ∑ k ∈ Finset.Nat.antidiagonalTuple m d,
      ∏ j, MvPolynomial.eval₂ (Int.castRingHom ℂ) α (MvPolynomial.hsymm (Fin n) ℤ (k j)) * β j ^ (k j) := by
    funext d
    rw [← GlobalTheory.T.cauchy_identity_schur_formal_degree hmn α β d, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    simp only [G]; rw [(mem_antiParts.1 hl).1]; ring
  have h5 := GlobalTheory.T.mk_sum_hsymm_mul_prod_one_sub_eq_one α β T
  rw [← hc] at h5
  obtain ⟨hne, hhas⟩ := GlobalTheory.T.eulerInverse_powerSeries_eval_one _ hsum (fun p : Fin n × Fin m => α p.1 * β p.2 * T) h5
  refine ⟨fun i j => ?_, ?_⟩
  · rw [Fintype.prod_prod_type] at hne
    exact Finset.prod_ne_zero_iff.1 (Finset.prod_ne_zero_iff.1 hne i (mem_univ _)) j (mem_univ _)
  · have := htrans _ hhas
    rw [← Finset.prod_inv_distrib, Fintype.prod_prod_type] at this
    exact this

theorem multiset_prod_map_product_eq_prod_prod {X Y : Type} (A : Multiset X) (B : Multiset Y) (f : X × Y → ℂ) :
    ((A ×ˢ B).map f).prod = (A.map fun a => (B.map fun b => f (a, b)).prod).prod := by
  induction A using Multiset.induction_on with
  | empty => simp
  | cons a A ih => simp [Multiset.cons_product, ih]

theorem locL_univ (q : ℕ) {m n : ℕ} (α : Fin n → ℂˣ) (β : Fin m → ℂˣ) (s : ℂ) :
    locL q (Finset.univ.val.map α) (Finset.univ.val.map β) s =
      ∏ i, ∏ j, (1 - (α i : ℂ) * β j * (q : ℂ) ^ (-s))⁻¹ := by
  rw [locL, multiset_prod_map_product_eq_prod_prod, Multiset.map_map]
  simp only [Multiset.map_map, Function.comp_def]
  rfl

theorem cauchy_locL {m n : ℕ} (hmn : m ≤ n) (α : Fin n → ℂˣ) (β : Fin m → ℂˣ) (q : ℕ) (s : ℂ)
    (hs : Summable fun l : {l : Fin m → ℕ // Antitone l} =>
      ‖schurAt (padTo hmn l.1) (fun i => (α i : ℂ)) * schurAt l.1 (fun j => (β j : ℂ))‖ *
        ‖(q : ℂ) ^ (-s)‖ ^ (∑ i, l.1 i)) :
    HasSum (fun l : {l : Fin m → ℕ // Antitone l} => schurAt (padTo hmn l.1) (fun i => (α i : ℂ)) *
      schurAt l.1 (fun j => (β j : ℂ)) * ((q : ℂ) ^ (-s)) ^ (∑ i, l.1 i))
      (locL q (Finset.univ.val.map α) (Finset.univ.val.map β) s) := by
  rw [locL_univ]; exact (cauchy_local hmn _ _ _ hs).2

end GlobalTheory.JSW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyBreuilKisinPrismCoproduct
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.EnvCop

section
variable {l : ℕ}

theorem map_eq_span {A C : Type} [CommRing A] [CommRing C] (f : A →+* C) (I : Ideal A) (d : A)
    (hI : I = Ideal.span {d}) : I.map f = Ideal.span {f d} := by
  subst hI; rw [Ideal.map_span, Set.image_singleton]

theorem map_sup_le {A C : Type} [CommRing A] [CommRing C] (f : A →+* C) (I : Ideal A) (I' : Ideal C)
    (h : ∀ a ∈ I, f a ∈ I') : (Ideal.span {(l : A)} ⊔ I).map f ≤ Ideal.span {(l : C)} ⊔ I' := by
  rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, map_natCast]
  exact sup_le_sup_left (Ideal.map_le_of_le_comap fun a ha => Ideal.mem_comap.2 (h a ha)) _

theorem eq_add_mul_of {R : Type} [CommRing R] {a b c v : R} (h : v * c = a - b) : a = b + c * v := by
  linear_combination -h

theorem map_span_mem {Q C : Type} [CommRing Q] [CommRing C] (h : Q →+* C) (q : Q) (I : Ideal C)
    (hq : h q ∈ I) : ∀ a ∈ Ideal.span {q}, h a ∈ I := by
  intro a ha
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
  rw [map_mul]; exact Ideal.mul_mem_left _ _ hq

theorem quot_eq_of {Q C : Type} [CommRing Q] [CommRing C] (h : Q →+* C) (I : Ideal C) (a b : Q) (c : C)
    (hb : h b = c) (e : h (a - b) ∈ I) : Ideal.Quotient.mk I (h a) = Ideal.Quotient.mk I c := by
  subst hb; rw [map_sub] at e; exact Ideal.Quotient.eq.2 e

theorem eval_lin {Q C : Type} [CommRing Q] [CommRing C] (h : Q →+* C) (x P D w : Q) (p d v : C)
    (hx : x = P + D * w) (hP : h P = p) (hD : h D = d) (hw : h w = v) : h x = p + d * v := by
  subst hx hP hD hw; rw [map_add, map_mul]

theorem cancel_of {C : Type} [CommRing C] {p d a v : C} (hd : d ∈ nonZeroDivisors C)
    (h : p + d * a = p + d * v) : a = v := by
  have e : d * (a - v) = 0 := by rw [mul_sub]; exact sub_eq_zero.2 (add_left_cancel h)
  exact sub_eq_zero.1 (hd.1 _ e)

theorem fg_sup_span {A : Type} [CommRing A] (I : Ideal A) (d : A) (hI : I = Ideal.span {d}) :
    (Ideal.span {(l : A)} ⊔ I).FG := by
  subst hI; exact (Submodule.fg_span_singleton _).sup (Submodule.fg_span_singleton _)
end

theorem comp_hf_X {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {P P' : Obj l ↥(OL K)} (h' : Hom P P')
    (g0 : Hom bk.prism P) (g : Hom bk.prism P') (h2 : h'.comp g0 = g) : h'.f (BK.hf g0 X) = BK.hf g X := by
  subst h2; rfl

section

variable {l : ℕ}

theorem quot_bdd_of_mem {A : Type} [CommRing A] (q : A) (N : ℕ)
    (h : ∀ (x : A) (m : ℕ), (l : A) ^ m * x ∈ Ideal.span {q} → (l : A) ^ N * x ∈ Ideal.span {q}) :
    ∀ x : A ⧸ Ideal.span {q}, (∃ m : ℕ, (l : A ⧸ Ideal.span {q}) ^ m * x = 0) →
      (l : A ⧸ Ideal.span {q}) ^ N * x = 0 := by
  rintro x ⟨m, hm⟩
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hm' : (l : A) ^ m * y ∈ Ideal.span {q} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_pow, map_natCast]; exact hm
  have h2 := h y m hm'
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_pow, map_natCast] at h2
  exact h2

theorem pow_mul_mem_of_pow_mul_mem {A : Type} [CommRing A] (I : Ideal A) (N : ℕ)
    (h : ∀ x : A ⧸ I, (∃ m : ℕ, (l : A ⧸ I) ^ m * x = 0) → (l : A ⧸ I) ^ N * x = 0) :
    ∀ (x : A) (m : ℕ), (l : A) ^ m * x ∈ I → (l : A) ^ N * x ∈ I := by
  intro x m hm
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_pow, map_natCast] at hm ⊢
  exact h _ ⟨m, hm⟩

theorem map_sup_span {A Q : Type} [CommRing A] [CommRing Q] (i : A →+* Q) (I : Ideal A) (d : A)
    (hI : I = Ideal.span {d}) :
    (Ideal.span {(l : A)} ⊔ I).map i = Ideal.span {(l : Q)} ⊔ Ideal.span {i d} := by
  subst hI
  rw [Ideal.map_sup, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton, map_natCast]

theorem le_comap_span {A Q : Type} [CommRing A] [CommRing Q] (i : A →+* Q) (I : Ideal A) (d : A)
    (hI : I = Ideal.span {d}) : I ≤ (Ideal.span {i d}).comap i := by
  subst hI
  intro x hx
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hx
  rw [Ideal.mem_comap, map_mul]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

end

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} {B : Obj l ↥(OL K)} {d p : B.A}

section
variable (hI : B.I = Ideal.span {d}) (En : EnvRing B.D (JJ B) d p)
include hI

theorem facts : ∃ N : ℕ, En.i d ∈ nonZeroDivisors En.Q ∧ ∀ (x : En.Q) (m : ℕ),
    (l : En.Q) ^ m * x ∈ Ideal.span {En.i d} → (l : En.Q) ^ N * x ∈ Ideal.span {En.i d} := by
  obtain ⟨N, hN⟩ := B.bdd
  have hnz : d ∈ nonZeroDivisors B.A := by
    have h := B.inv; rw [hI] at h; exact GlobalTheory.T.mem_nonZeroDivisors_of_invertible_span_singleton' _ d h
  have hb : ∀ (x : B.A) (m : ℕ), (l : B.A) ^ m * x ∈ Ideal.span {d} → (l : B.A) ^ N * x ∈ Ideal.span {d} := by
    rw [← hI]; exact pow_mul_mem_of_pow_mul_mem B.I N hN
  have tb : TopBasis En.i (Ideal.span {(l : B.A)} ⊔ Ideal.span {d}) (Digits l) := by
    rw [← hI]; exact En.tb
  exact ⟨N, GlobalTheory.T.regular_and_bounded_torsion_of_adicTopologicalBasis l B.A En.Q En.i d N (Digits l) hnz hb tb⟩

def strQ : ↥(OL K) →+* En.Q ⧸ Ideal.span {En.i d} :=
  (Ideal.quotientMap (Ideal.span {En.i d}) En.i (le_comap_span En.i B.I d hI)).comp B.str

theorem strQ_eq (r : ↥(OL K)) (b : B.A) (hb : Ideal.Quotient.mk B.I b = B.str r) :
    strQ hI En r = Ideal.Quotient.mk (Ideal.span {En.i d}) (En.i b) :=
  (congrArg (Ideal.quotientMap (Ideal.span {En.i d}) En.i (le_comap_span En.i B.I d hI)) hb).symm.trans
    Ideal.quotientMap_mk

abbrev obj : Obj l ↥(OL K) where
  A := En.Q
  D := En.DQ
  I := Ideal.span {En.i d}
  inv := invertible_span_singleton (facts hI En).choose_spec.1
  complete := by rw [← map_sup_span En.i B.I d hI]; exact En.tb.complete
  l_mem := En.DQ.l_mem_of_isUnit hl.out.pos (by rw [← En.i_δ d]; exact (GlobalTheory.T.isUnit_delta_of_prism_ideal_eq_span l _ B d hI).map En.i)
  bdd := ⟨(facts hI En).choose, quot_bdd_of_mem (En.i d) _ (facts hI En).choose_spec.2⟩
  str := strQ hI En

def inl : Hom B (obj hI En) where
  f := En.i
  f_δ := En.i_δ
  f_I a ha := le_comap_span En.i B.I d hI ha
  f_str r a h := Ideal.quotientMap_mk.symm.trans
    (congrArg (Ideal.quotientMap (Ideal.span {En.i d}) En.i (le_comap_span En.i B.I d hI)) h)

end

variable {bk : BK K} (En : EnvRing B.D (JJ B) d p)

theorem frame (hF : IsFrame bk B d p) : IsFrame bk (obj hF.1 En) (En.i d) (En.i p + En.i d * En.w) := by
  refine ⟨rfl, ?_⟩
  have e1 := congrArg (Ideal.quotientMap (Ideal.span {En.i d}) En.i (le_comap_span En.i B.I d hF.1)) hF.2
  have e2 : En.i p + En.i d * En.w - En.i p ∈ Ideal.span {En.i d} := by
    rw [add_sub_cancel_left]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  exact (Ideal.Quotient.eq.2 e2).trans (Ideal.quotientMap_mk.symm.trans e1)

theorem str_of (hI : B.I = Ideal.span {d}) {C : Obj l ↥(OL K)} (f : Hom B C) (h0 : En.Q →+* C.A)
    (h0a : ∀ a, h0 (En.i a) = f.f a) (hIQ : ∀ a ∈ Ideal.span {En.i d}, h0 a ∈ C.I) (r : ↥(OL K)) (a : En.Q)
    (ha : Ideal.Quotient.mk (Ideal.span {En.i d}) a = strQ hI En r) :
    Ideal.Quotient.mk C.I (h0 a) = C.str r := by
  have hsu : ∃ b : B.A, Ideal.Quotient.mk B.I b = B.str r := Ideal.Quotient.mk_surjective (B.str r)
  obtain ⟨b, hb⟩ := hsu
  have e1 : Ideal.Quotient.mk (Ideal.span {En.i d}) a = Ideal.Quotient.mk (Ideal.span {En.i d}) (En.i b) :=
    ha.trans (strQ_eq hI En r b hb)
  have hab : a - En.i b ∈ Ideal.span {En.i d} := Ideal.Quotient.eq.1 e1
  exact (quot_eq_of h0 C.I a (En.i b) (f.f b) (h0a b) (hIQ _ hab)).trans (f.f_str r b hb)

theorem I_of (hI : B.I = Ideal.span {d}) {C : Obj l ↥(OL K)} (f : Hom B C) (h0 : En.Q →+* C.A)
    (h0a : ∀ a, h0 (En.i a) = f.f a) : ∀ a ∈ Ideal.span {En.i d}, h0 a ∈ C.I :=
  map_span_mem h0 (En.i d) C.I ((congrArg (· ∈ C.I) (h0a d)).mpr
    (f.f_I d (by rw [hI]; exact Ideal.mem_span_singleton_self d)))

def lift (hI : B.I = Ideal.span {d}) {C : Obj l ↥(OL K)} (f : Hom B C) (h0 : En.Q →+* C.A)
    (h0δ : IsδMap En.DQ C.D h0) (h0a : ∀ a, h0 (En.i a) = f.f a) : Hom (obj hI En) C where
  f := h0
  f_δ := h0δ
  f_I := I_of En hI f h0 h0a
  f_str := str_of En hI f h0 h0a (I_of En hI f h0 h0a)

set_option maxHeartbeats 2000000 in

theorem univ (hF : IsFrame bk B d p) (g0 : Hom bk.prism (obj hF.1 En))
    (hg0 : BK.hf g0 X = En.i p + En.i d * En.w) (C : Obj l ↥(OL K)) (f : Hom B C)
    (g : Hom bk.prism C) : ∃! h : Hom (obj hF.1 En) C, h.comp (inl hF.1 En) = f ∧ h.comp g0 = g := by
  have hdI : d ∈ B.I := by rw [hF.1]; exact Ideal.mem_span_singleton_self d
  have hCI : C.I = Ideal.span {f.f d} :=
    (GlobalTheory.T.prism_hom_map_ideal_eq l _ B C f).symm.trans (map_eq_span f.f B.I d hF.1)
  have hnz : f.f d ∈ nonZeroDivisors C.A := by
    have h := C.inv; rw [hCI] at h; exact GlobalTheory.T.mem_nonZeroDivisors_of_invertible_span_singleton' _ _ h
  obtain ⟨hgδ, hgs⟩ := GlobalTheory.T.breuilKisinHom_image_X_delta_zero_lifts_uniformizer l K bk C g
  have hfp := f.f_str _ p hF.2
  have hmem : BK.hf g X - f.f p ∈ Ideal.span {f.f d} := by
    rw [← hCI]; exact Ideal.Quotient.eq.1 (hgs.trans hfp.symm)
  have hex : ∃ v', v' * f.f d = BK.hf g X - f.f p := Ideal.mem_span_singleton'.1 hmem
  obtain ⟨v', hv'⟩ := hex
  have hgX : BK.hf g X = f.f p + f.f d * v' := eq_add_mul_of hv'
  have hrel : C.D.δ (f.f p + f.f d * v') = 0 := (congrArg C.D.δ hgX).symm.trans hgδ
  have hJ : (JJ B).map f.f ≤ JJ C := map_sup_le f.f B.I C.I f.f_I
  have hlift : ∃ h : En.Q →+* C.A, IsδMap En.DQ C.D h ∧ h.comp En.i = f.f ∧ h En.w = v' :=
    En.lift C.A C.D (JJ C) C.complete f.f f.f_δ hJ v' hrel
  obtain ⟨h0, h0δ, h0i, h0w⟩ := hlift
  have h0a : ∀ a, h0 (En.i a) = f.f a := fun a => RingHom.congr_fun h0i a
  refine ⟨lift En hF.1 f h0 h0δ h0a, ⟨Hom.ext' h0i, GlobalTheory.T.breuilKisin_prism_hom_ext_of_X l K bk C _ _ ?_⟩, ?_⟩
  · exact (eval_lin h0 _ _ _ _ _ _ _ hg0 (h0a p) (h0a d) h0w).trans hgX.symm
  · rintro h' ⟨h1, h2⟩
    have e1 : h'.f.comp En.i = f.f := congrArg Hom.f h1
    have e1a : ∀ a, h'.f (En.i a) = f.f a := fun a => RingHom.congr_fun e1 a
    have e2 := comp_hf_X h' g0 g h2
    have e3 : h'.f En.w = v' :=
      cancel_of hnz ((eval_lin h'.f (BK.hf g0 X) (En.i p) (En.i d) En.w (f.f p) (f.f d) (h'.f En.w) hg0 (e1a p) (e1a d) rfl).symm.trans (e2.trans hgX))
    have hJ' : (JJ B).map (h'.f.comp En.i) ≤ JJ C := (congrArg (fun φ => (JJ B).map φ ≤ JJ C) e1).mpr hJ
    exact Hom.ext' (GlobalTheory.T.deltaRingHom_unique_of_adicTopologicalBasis l B.A En.Q C.A En.DQ C.D (JJ B) (JJ C) En.i En.w En.tb En.tb_b
      C.complete.toIsHausdorff h'.f h0 h'.f_δ h0δ hJ' (e1.trans h0i.symm) (e3.trans h0w.symm))

def env (hF : IsFrame bk B d p) : Env bk B d p :=
  have hex := GlobalTheory.T.exists_breuilKisinHom_of_uniformizerFrame l K bk (obj hF.1 En) (En.i d) (En.i p + En.i d * En.w) (frame En hF) En.rel
  { Q := obj hF.1 En
    inl := inl hF.1 En
    inr := hex.choose
    univ := univ En hF hex.choose hex.choose_spec
    w := En.w
    w_eq := hex.choose_spec
    I_eq := rfl
    tb := En.tb
    tb_b := En.tb_b }

end GlobalTheory.BSP.EnvCop

open GlobalTheory.BSP.EnvCop in

theorem GlobalTheory.BSP.nonempty_env : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K))
    (d p : B.A), IsFrame bk B d p → Nonempty (Env bk B d p) := by
  intro l _ K bk B d p hF
  have hd : d ∈ JJ B := Ideal.mem_sup_right (by rw [hF.1]; exact Ideal.mem_span_singleton_self d)
  have hEn : Nonempty (EnvRing B.D (JJ B) d p) :=
    GlobalTheory.T.nonempty_envRing l B.A B.D (JJ B) d p (fg_sup_span B.I d hF.1)
      (Ideal.mem_sup_left (Ideal.mem_span_singleton_self (l : B.A))) hd (GlobalTheory.T.isUnit_delta_of_prism_ideal_eq_span l _ B d hF.1) B.complete
  exact ⟨env hEn.some hF⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PosMApplyNeZero
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric.ColSplit

abbrev HiIx (a r k : ℕ) : Type := {t : UnipotentBlockColumnIndex a k k // r ≤ (t.1.1 : ℕ)}

abbrev LoIx (a r k : ℕ) : Type := {t : UnipotentBlockColumnIndex a k k // ¬ r ≤ (t.1.1 : ℕ)}

def colEquiv (a r k : ℕ) : HiIx a r k ⊕ LoIx a r k ≃ UnipotentBlockColumnIndex a k k := Equiv.sumCompl _

def blkEquiv (a r m : ℕ) (hr : r ≤ m + 1) : UnipotentBlockColumnIndex a r m ⊕ LoIx a r (m + 1) ≃ UnipotentBlockColumnIndex a r (m + 1) where
  toFun := Sum.elim (fun s : UnipotentBlockColumnIndex a r m => ⟨s.1, s.2.1, s.2.2.1, by have := s.2.2.2; omega⟩)
    (fun l : LoIx a r (m + 1) => ⟨l.1.1, by have := l.2; omega, by have := l.1.2; omega, by have := l.1.2; omega⟩)
  invFun := fun t => if h : (t.1.2 : ℕ) ≤ m then Sum.inl ⟨t.1, t.2.1, t.2.2.1, h⟩
    else Sum.inr ⟨⟨t.1, by have := t.2; omega, by have := t.2; omega, by have := t.2; omega⟩,
      show ¬ r ≤ (t.1.1 : ℕ) by have := t.2; omega⟩
  left_inv := by
    rintro (s | l)
    · simp [s.2.2.2]
    · have h1 := l.1.2
      have h2 : ¬ ((l.1.1.2 : ℕ) ≤ m) := by omega
      simp [h2]
  right_inv := by
    intro t
    by_cases h : (t.1.2 : ℕ) ≤ m
    · simp [h]
    · simp [h]

section Mat

variable {R : Type} [CommRing R] {a : ℕ}

theorem posM_apply_ne_zero {ι : Type} [Fintype ι] {p : ι → Fin a × Fin a} {x : ι → R} {i k : Fin a}
    (h : posM p x i k ≠ 0) : ∃ t, p t = (i, k) := by
  simp only [posM, Matrix.sum_apply] at h
  obtain ⟨t, -, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  refine ⟨t, ?_⟩
  rw [Matrix.single_apply] at ht
  split_ifs at ht with hc
  · exact Prod.ext hc.1 hc.2
  · exact absurd rfl ht

theorem posM_eq_of_support {ι : Type} [Fintype ι] {p : ι → Fin a × Fin a} (hp : Function.Injective p)
    (M : Matrix (Fin a) (Fin a) R) (hM : ∀ i k, M i k ≠ 0 → ∃ t, p t = (i, k)) :
    posM p (fun t => M (p t).1 (p t).2) = M := by
  ext i k
  simp only [posM, Matrix.sum_apply, Matrix.single_apply]
  by_cases h : ∃ t, p t = (i, k)
  · obtain ⟨t, ht⟩ := h
    rw [Finset.sum_eq_single t]
    · simp [ht]
    · intro t' _ ht'
      rw [if_neg]
      rintro ⟨e1, e2⟩
      exact ht' (hp (by rw [ht]; exact Prod.ext e1 e2))
    · simp
  · have h0 : M i k = 0 := by
      by_contra h1
      exact h (hM i k h1)
    rw [h0]
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [if_neg]
    rintro ⟨e1, e2⟩
    exact h ⟨t, Prod.ext e1 e2⟩

theorem posM_comp_symm {ι κ : Type} [Fintype ι] [Fintype κ] (p : ι → Fin a × Fin a) (τ : κ ≃ ι) (w : κ → R) :
    posM p (w ∘ τ.symm) = posM (p ∘ τ) w := by
  simp only [posM]
  exact (Fintype.sum_equiv τ.symm _ _ (fun t => by simp)).trans rfl

theorem posM_sumElim {ι κ : Type} [Fintype ι] [Fintype κ] (p : ι ⊕ κ → Fin a × Fin a) (z : ι → R) (y : κ → R) :
    posM p (Sum.elim z y) = posM (p ∘ Sum.inl) z + posM (p ∘ Sum.inr) y := by
  simp only [posM, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Function.comp]

theorem posM_sub {ι : Type} [Fintype ι] (p : ι → Fin a × Fin a) (x y : ι → R) :
    posM p (x - y) = posM p x - posM p y := by
  rw [eq_sub_iff_add_eq, ← posM_add, sub_add_cancel]

theorem posM_zero' {ι : Type} [Fintype ι] (p : ι → Fin a × Fin a) : posM p (0 : ι → R) = 0 := by
  simp [posM]

theorem posM_mul_eq_zero {ι κ : Type} [Fintype ι] [Fintype κ] {p : ι → Fin a × Fin a} {q : κ → Fin a × Fin a}
    (h : ∀ s t, (p s).2 ≠ (q t).1) (x : ι → R) (y : κ → R) : posM p x * posM q y = 0 := by
  simp only [posM, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun t _ => ?_
  exact Matrix.single_mul_single_of_ne _ _ _ _ (h _ _) _

def corr {r m : ℕ} (n : UnipotentBlockColumnIndex a r m → R) (z : HiIx a r (m + 1) → R) : LoIx a r (m + 1) → R := fun l =>
  (posM Subtype.val n * posM (fun t : HiIx a r (m + 1) => t.1.1) z) l.1.1.1 l.1.1.2

theorem posM_corr {r m : ℕ} (n : UnipotentBlockColumnIndex a r m → R) (z : HiIx a r (m + 1) → R) :
    posM (fun l : LoIx a r (m + 1) => l.1.1) (corr n z) =
      posM Subtype.val n * posM (fun t : HiIx a r (m + 1) => t.1.1) z := by
  refine posM_eq_of_support (fun l l' e => Subtype.ext (Subtype.ext e)) _ fun i k hik => ?_
  obtain ⟨l, hl⟩ : ∃ l, posM Subtype.val n i l * posM (fun t : HiIx a r (m + 1) => t.1.1) z l k ≠ 0 := by
    rw [Matrix.mul_apply] at hik
    obtain ⟨l, -, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero hik
    exact ⟨l, hl⟩
  obtain ⟨s, hs⟩ := posM_apply_ne_zero (left_ne_zero_of_mul hl)
  obtain ⟨t, ht⟩ := posM_apply_ne_zero (right_ne_zero_of_mul hl)
  have s2 := s.2
  have t2 := t.1.2
  rw [hs] at s2
  rw [ht] at t2
  simp only at s2 t2
  exact ⟨⟨⟨(i, k), show (i : ℕ) < m + 1 by omega, show m + 1 ≤ (k : ℕ) by omega, show (k : ℕ) ≤ m + 1 by omega⟩,
    show ¬ r ≤ (i : ℕ) by omega⟩, rfl⟩

end Mat

section Id

variable {R : Type} [CommRing R] {a : ℕ}

theorem blkU_col_mul_blkU {r m : ℕ} (hr : r ≤ m + 1) (n : UnipotentBlockColumnIndex a r m → R) (z : HiIx a r (m + 1) → R)
    (y : LoIx a r (m + 1) → R) :
    blkU (Sum.elim z y ∘ (colEquiv a r (m + 1)).symm) * blkU n =
      blkU (Sum.elim n (y - corr n z) ∘ (blkEquiv a r m hr).symm) *
        blkU (Sum.elim z 0 ∘ (colEquiv a r (m + 1)).symm) := by
  apply Units.ext
  change (1 + posM Subtype.val (Sum.elim z y ∘ (colEquiv a r (m + 1)).symm)) * (1 + posM Subtype.val n) =
    (1 + posM Subtype.val (Sum.elim n (y - corr n z) ∘ (blkEquiv a r m hr).symm)) *
      (1 + posM Subtype.val (Sum.elim z 0 ∘ (colEquiv a r (m + 1)).symm))
  simp only [posM_comp_symm, posM_sumElim, posM_sub, posM_zero', add_zero]
  have e1 : ((Subtype.val ∘ colEquiv a r (m + 1)) ∘ Sum.inl) = fun t : HiIx a r (m + 1) => t.1.1 := rfl
  have e2 : ((Subtype.val ∘ colEquiv a r (m + 1)) ∘ Sum.inr) = fun t : LoIx a r (m + 1) => t.1.1 := rfl
  have e3 : ((Subtype.val ∘ blkEquiv a r m hr) ∘ Sum.inl) = (Subtype.val : UnipotentBlockColumnIndex a r m → Fin a × Fin a) := rfl
  have e4 : ((Subtype.val ∘ blkEquiv a r m hr) ∘ Sum.inr) = fun t : LoIx a r (m + 1) => t.1.1 := rfl
  rw [e1, e2, e3, e4, posM_corr]
  set P := posM (fun t : HiIx a r (m + 1) => t.1.1) z
  set Q := posM (fun t : LoIx a r (m + 1) => t.1.1) y
  set N := posM (Subtype.val : UnipotentBlockColumnIndex a r m → Fin a × Fin a) n
  have hPN : P * N = 0 := posM_mul_eq_zero (fun s t => by
    have := s.1.2; have := t.2; omega) _ _
  have hQN : Q * N = 0 := posM_mul_eq_zero (fun s t => by
    have := s.1.2; have := t.2; omega) _ _
  have hQP : Q * P = 0 := posM_mul_eq_zero (fun s t => by
    have := s.1.2; have := t.1.2; omega) _ _
  have hNPP : N * P * P = 0 := by
    rw [mul_assoc, posM_mul_eq_zero (fun s t => by have := s.1.2; have := t.1.2; omega) z z, mul_zero]
  simp only [mul_add, add_mul, mul_one, one_mul, mul_sub, sub_mul, hPN, hQN, hQP, hNPP]
  abel

end Id

end GlobalTheory.CuspGeneric.ColSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowFiveOneOfCoefRingTakenAtLiveLocalisations
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.DesignFromSize

theorem main : GlobalTheory.TwSys.Cheb → ∀ D : D7, TakenAll D → Formalism.MainNotions.N.K.Rows.AllDesignConditions D := by
  intro hC D hT i _ _ r ρ π dc lenRow e' cB hr hA hπ
  obtain ⟨_, _, hG3, _, _, _, _, _, _, _, _, _, _, hDec, _⟩ := hA
  have hdec : ∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t := D.R.t) (r π) (ρ π) (D.nd.chi i) e := hDec
  have hpos : 0 < D.R.r := by
    have := D.R.two_le_m; have := D.R.m_add_three_le_k; unfold Ranks.r; omega
  have habs : AbsIrrSub (mapRep (IsLocalRing.residue (D.nd.O i)) (ρ π)) ⊤ :=
    GlobalTheory.Proof.AbsoluteIrreducibilitySpan.absIrr_of_span hpos _ _ (fun _ => 1) (fun g => by rw [one_smul]; rfl) hG3.2.2
  have hlive : Live D.nd i := ⟨π, hπ, r π, ρ π, hr π, hdec, habs⟩
  obtain ⟨r₀, ρ₀, hr₀, hw⟩ := hT i hlive
  obtain ⟨S, hS, _⟩ := GlobalTheory.T.exists_globalObjects_every_family_wild hC D.nd i r₀ ρ₀ hr₀ hw r ρ hr π hπ hdec
  exact ⟨S, hS⟩

end GlobalTheory.DesignFromSize
end

