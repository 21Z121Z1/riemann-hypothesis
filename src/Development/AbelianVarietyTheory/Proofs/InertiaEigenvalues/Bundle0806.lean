import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1484
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0025
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0803
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0016
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins
import GroundTheory.LocalFields.Bundle0003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsLocExtFinrankEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKummerField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0024
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0101
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0115
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0041
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0802
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0021

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEvalAtNeZero
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.GlueSpan

theorem glue_rules {K : Type} [Field K] {ι : Type} [Fintype ι]
    (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
    (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
      (S →ₐ[K] T) → pts S → pts T → Prop)
    (borR : ∀ {S : Type} [CommRing S] [Algebra K S], (ι → Sˣ) → pts S → pts S → Prop)
    (ea eb : ι → ℕ) {N : ℕ} (t g : Fin N → Rules pts)
    (ht : ∀ i, t i ∈ secW pts mapR borR eb)
    (hunit : ∀ (p : TRing K) (y : pts p.R), Ideal.span (Set.range fun i => t i p y) = ⊤)
    (hg : ∀ i, g i ∈ secW pts mapR borR (ea + eb)) (hc : ∀ i i', g i * t i' = g i' * t i) :
    ∃ h ∈ secW pts mapR borR ea, ∀ i, h * t i = g i := by
  classical
  have hs0 : ∀ (p : TRing K) (y : pts p.R), ∃ s : Fin N → p.R, ∑ i, s i * t i p y = 1 := by
    intro p y
    obtain ⟨s, hs⟩ := (Submodule.mem_span_range_iff_exists_fun _).1
      ((hunit p y).symm ▸ Submodule.mem_top (x := (1 : p.R)))
    exact ⟨s, by simpa [smul_eq_mul] using hs⟩
  choose s hs using hs0
  have hc' : ∀ (p : TRing K) (y : pts p.R) i i', g i p y * t i' p y = g i' p y * t i p y :=
    fun p y i i' => congrFun (congrFun (hc i i') p) y
  have indep : ∀ (p : TRing K) (y : pts p.R) (s' : Fin N → p.R), ∑ i, s' i * t i p y = 1 →
      ∑ i, s' i * g i p y = ∑ i, s p y i * g i p y := by
    intro p y s' h'
    calc ∑ i, s' i * g i p y = (∑ i, s' i * g i p y) * (∑ i', s p y i' * t i' p y) := by rw [hs, mul_one]
      _ = ∑ i, ∑ i', s' i * s p y i' * (g i p y * t i' p y) := by
          rw [Finset.sum_mul_sum]; refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => by ring
      _ = ∑ i, ∑ i', s' i * s p y i' * (g i' p y * t i p y) := by simp_rw [hc']
      _ = (∑ i', s p y i' * g i' p y) * (∑ i, s' i * t i p y) := by
          rw [Finset.sum_mul_sum, Finset.sum_comm]; refine Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun i _ => by ring
      _ = ∑ i, s p y i * g i p y := by rw [h', mul_one]
  let h : Rules pts := fun p y => ∑ i, s p y i * g i p y
  refine ⟨h, ⟨?_, ?_⟩, ?_⟩
  · intro p q φ y z hyz
    have e1 : ∑ i, φ (s p y i) * t i q z = 1 := by
      simp_rw [(ht _).1 p q φ y z hyz, ← map_mul, ← map_sum, hs, map_one]
    show ∑ i, s q z i * g i q z = φ (∑ i, s p y i * g i p y)
    rw [← indep q z _ e1, map_sum]
    simp_rw [(hg _).1 p q φ y z hyz, map_mul]
  · intro p u y y' hyy
    have hw : ∀ e : ι → ℕ, wchar e u = ((∏ i, u i ^ e i : (p.R)ˣ) : p.R) := by
      intro e; simp [wchar, Units.coe_prod]
    have hadd : wchar (ea + eb) u = wchar ea u * wchar eb u := by
      simp only [wchar, Pi.add_apply, pow_add, Finset.prod_mul_distrib]
    set v : (p.R)ˣ := ∏ i, u i ^ eb i with hv
    have e1 : ∑ i, (s p y i * ((v⁻¹ : (p.R)ˣ) : p.R)) * t i p y' = 1 := by
      simp_rw [(ht _).2 p u y y' hyy, hw eb, ← hv]
      rw [← hs p y]; refine Finset.sum_congr rfl fun i _ => ?_
      calc s p y i * ((v⁻¹ : (p.R)ˣ) : p.R) * ((v : p.R) * t i p y)
          = s p y i * t i p y * (((v⁻¹ : (p.R)ˣ) : p.R) * v) := by ring
        _ = s p y i * t i p y := by rw [Units.inv_mul, mul_one]
    show ∑ i, s p y' i * g i p y' = wchar ea u * ∑ i, s p y i * g i p y
    rw [← indep p y' _ e1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(hg _).2 p u y y' hyy, hadd, hw eb, ← hv]
    calc s p y i * ((v⁻¹ : (p.R)ˣ) : p.R) * (wchar ea u * (v : p.R) * g i p y)
        = wchar ea u * (s p y i * g i p y) * (((v⁻¹ : (p.R)ˣ) : p.R) * v) := by ring
      _ = wchar ea u * (s p y i * g i p y) := by rw [Units.inv_mul, mul_one]
  · intro i
    funext p y
    show (∑ i', s p y i' * g i' p y) * t i p y = g i p y
    calc (∑ i', s p y i' * g i' p y) * t i p y = ∑ i', s p y i' * (g i' p y * t i p y) := by
          rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun i' _ => by ring
      _ = ∑ i', s p y i' * (g i p y * t i' p y) := by simp_rw [hc']
      _ = g i p y * ∑ i', s p y i' * t i' p y := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i' _ => by ring
      _ = g i p y := by rw [hs, mul_one]

theorem glue_frPt : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (a b : (D.host.E →+* ℂ) × ℕ → ℕ) (n m N : ℕ)
    (t g : Fin N → Rul (T.Q.Xo j) T.Q.c), (∀ i, t i ∈ sec (T.Q.Xo j) T.Q.c b m) →
    (∀ (p : TRing T.Q.c.F) (y : FrPt (T.Q.Xo j) T.Q.c p.R), Ideal.span (Set.range fun i => t i p y) = ⊤) →
    (∀ i, g i ∈ sec (T.Q.Xo j) T.Q.c (a + b) (n + m)) → (∀ i i', g i * t i' = g i' * t i) →
    ∃ h ∈ sec (T.Q.Xo j) T.Q.c a n, ∀ i, h * t i = g i := by
  intro D T j a b n m N t g ht hunit hg hc
  have hg' : ∀ i, g i ∈ secW (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z)
      (fun t y y' => FrBor t y y') (ex (T.Q.Dw j) a n + ex (T.Q.Dw j) b m) := by
    intro i; have := hg i; unfold sec at this; rwa [ex_add] at this
  exact glue_rules (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z)
    (fun t y y' => FrBor t y y') (ex (T.Q.Dw j) a n) (ex (T.Q.Dw j) b m) t g ht hunit hg' hc

theorem exists_evalAt_ne_zero {K : Type} [Field K] (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
    (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
      (S →ₐ[K] T) → pts S → pts T → Prop)
    {N : ℕ} (t : Fin N → Rules pts)
    (hunit : ∀ (p : TRing K) (y : pts p.R), Ideal.span (Set.range fun i => t i p y) = ⊤)
    {S : Type} [CommRing S] [Nontrivial S] [Algebra K S] (y : pts S) (h : FromTest pts mapR y) :
    ∃ i, evalAt pts mapR (t i) y ≠ 0 := by
  unfold evalAt
  simp only [dif_pos h]
  obtain ⟨s, hs⟩ := (Submodule.mem_span_range_iff_exists_fun _).1
    ((hunit h.choose h.choose_spec.choose_spec.choose).symm ▸ Submodule.mem_top (x := (1 : h.choose.R)))
  by_contra hall
  push Not at hall
  have h1 := congrArg (fun r => h.choose_spec.choose r) hs
  simp only [map_sum, map_one, smul_eq_mul, map_mul, hall, mul_zero, Finset.sum_const_zero] at h1
  exact zero_ne_one h1

theorem exists_rdU_t_ne_zero : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ →
    ∀ (N : ℕ) (t : Fin N → Rul (T.Q.Xo j) T.Q.c),
    (∀ (p : TRing T.Q.c.F) (y : FrPt (T.Q.Xo j) T.Q.c p.R), Ideal.span (Set.range fun i => t i p y) = ⊤) →
    ∀ k x, x ∈ ((T.U j σ).X k).dom → ∃ i, rdU (T.U j σ) (t i) k x ≠ 0 := by
  intro D T hT j hj σ hσ N t hunit k x hx
  haveI : Nontrivial (CAt σ) := inferInstanceAs (Nontrivial ℂ)
  obtain ⟨i, hi⟩ := exists_evalAt_ne_zero (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S)
    (fun φ y z => FrMap φ y z) t hunit _ (hT.unTest j hj σ hσ k ⟨x, hx⟩)
  refine ⟨i, ?_⟩
  have e : rdU (T.U j σ) (t i) k x = toC (evR (T.Q.Xo j) T.Q.c (t i) ((T.U j σ).un k ⟨x, hx⟩)) := by
    classical
    exact dif_pos hx
  rw [e]
  exact hi

theorem span_of_products : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ (a b : (D.host.E →+* ℂ) × ℕ → ℕ) (n m N : ℕ) (t : Fin N → Rul (T.Q.Xo j) T.Q.c), Dom a n → Dom b m → (∀ i, t i ∈ sec (T.Q.Xo j) T.Q.c b m) → (∀ (p : TRing T.Q.c.F) (y : FrPt (T.Q.Xo j) T.Q.c p.R), Ideal.span (Set.range fun i => t i p y) = ⊤) → ∀ P ∈ offZero (T.U j σ).X, (∀ i, P * rdU (T.U j σ) (t i) ∈ Submodule.span ℂ (rdU (T.U j σ) '' (sec (T.Q.Xo j) T.Q.c (a + b) (n + m) : Set (Rul (T.Q.Xo j) T.Q.c)))) → P ∈ Submodule.span ℂ (rdU (T.U j σ) '' (sec (T.Q.Xo j) T.Q.c a n : Set (Rul (T.Q.Xo j) T.Q.c))) := by
  intro D T hT j hj σ hσ a b n m N t ha hb ht hunit P hP hPt

  have hrep : ∀ i, ∃ (L : ℕ) (cf : Fin L → ℂ) (g : Fin L → Rul (T.Q.Xo j) T.Q.c),
      (∀ l, g l ∈ sec (T.Q.Xo j) T.Q.c (a + b) (n + m)) ∧
      ∑ l, cf l • rdU (T.U j σ) (g l) = P * rdU (T.U j σ) (t i) := by
    intro i
    obtain ⟨L, cf, g, hg⟩ := Submodule.mem_span_set'.1 (hPt i)
    choose g' hg' hg'e using fun l => (g l).2
    exact ⟨L, cf, g', hg', by rw [← hg]; simp [hg'e]⟩
  choose L cf g hg hsum using hrep

  let κ := Σ i : Fin N, Fin (L i)
  let A : κ → Fin N × Fin N → Rul (T.Q.Xo j) T.Q.c := fun q e =>
    (if q.1 = e.1 then g q.1 q.2 * t e.2 else 0) - (if q.1 = e.2 then g q.1 q.2 * t e.1 else 0)
  have hA : ∀ q e, A q e ∈ sec (T.Q.Xo j) T.Q.c (a + b + b) (n + m + m) := by
    intro q e
    have hm : ∀ i', g q.1 q.2 * t i' ∈ sec (T.Q.Xo j) T.Q.c (a + b + b) (n + m + m) :=
      fun i' => sec_mul _ _ _ _ _ _ (hg q.1 q.2) (ht i')
    refine Submodule.sub_mem _ ?_ ?_ <;> split_ifs <;> first | exact hm _ | exact Submodule.zero_mem _
  have hdom : Dom (a + b + b) (n + m + m) :=
    ⟨fun τ => ((ha.1 τ).add (hb.1 τ)).add (hb.1 τ), (ha.2.add hb.2).add hb.2⟩

  have hrow : ∀ (z : κ → ℂ) (e : Fin N × Fin N), ∑ q, z q • rdU (T.U j σ) (A q e) =
      (∑ l, z ⟨e.1, l⟩ • rdU (T.U j σ) (g e.1 l)) * rdU (T.U j σ) (t e.2) -
      (∑ l, z ⟨e.2, l⟩ • rdU (T.U j σ) (g e.2 l)) * rdU (T.U j σ) (t e.1) := by
    intro z e
    have h1 : ∀ q : κ, z q • rdU (T.U j σ) (A q e) =
        (if q.1 = e.1 then z q • (rdU (T.U j σ) (g q.1 q.2) * rdU (T.U j σ) (t e.2)) else 0) -
        (if q.1 = e.2 then z q • (rdU (T.U j σ) (g q.1 q.2) * rdU (T.U j σ) (t e.1)) else 0) := by
      intro q
      simp only [A]
      split_ifs <;> simp [map_sub, rdU_mul, smul_sub]
    simp only [h1, Finset.sum_sub_distrib]
    congr 1
    · rw [Fintype.sum_sigma, Finset.sum_eq_single e.1 (fun i' _ hi' => by simp [hi']) (by simp)]
      simp [Finset.sum_mul, smul_mul_assoc]
    · rw [Fintype.sum_sigma, Finset.sum_eq_single e.2 (fun i' _ hi' => by simp [hi']) (by simp)]
      simp [Finset.sum_mul, smul_mul_assoc]
  let z : κ → ℂ := fun q => cf q.1 q.2
  have hz : ∀ e, ∑ q, z q • rdU (T.U j σ) (A q e) = 0 := by
    intro e
    rw [hrow]
    show (∑ l, cf e.1 l • rdU (T.U j σ) (g e.1 l)) * rdU (T.U j σ) (t e.2) -
      (∑ l, cf e.2 l • rdU (T.U j σ) (g e.2 l)) * rdU (T.U j σ) (t e.1) = 0
    rw [hsum, hsum]; ring
  have hzspan := GlobalTheory.T.linear_relation_sections_span_eq D T j σ (GlobalTheory.rdIndep_of_lawsM D T.toCore hT.toLawsM j hj σ hσ) _ _ hdom κ (Fin N × Fin N) A hA z hz

  let S := Submodule.span ℂ (rdU (T.U j σ) '' (sec (T.Q.Xo j) T.Q.c a n : Set (Rul (T.Q.Xo j) T.Q.c)))
  let Z : Submodule ℂ (κ → ℂ) :=
    { carrier := {z | ∃ Q ∈ S, ∀ i, Q * rdU (T.U j σ) (t i) = ∑ l, z ⟨i, l⟩ • rdU (T.U j σ) (g i l)}
      zero_mem' := ⟨0, S.zero_mem, fun i => by simp⟩
      add_mem' := by
        rintro z1 z2 ⟨Q1, hQ1, e1⟩ ⟨Q2, hQ2, e2⟩
        exact ⟨Q1 + Q2, S.add_mem hQ1 hQ2, fun i => by
          simp only [add_mul, e1, e2, Pi.add_apply, add_smul, Finset.sum_add_distrib]⟩
      smul_mem' := by
        rintro c z1 ⟨Q1, hQ1, e1⟩
        exact ⟨c • Q1, S.smul_mem c hQ1, fun i => by
          simp only [smul_mul_assoc, e1, Finset.smul_sum, Pi.smul_apply, smul_eq_mul, mul_smul]⟩ }
  have hle : Submodule.span ℂ ((fun c : κ → T.Q.c.F => fun k => σ (c k)) ''
      {c | ∀ e, ∑ k, c k • A k e = 0}) ≤ Z := by
    rw [Submodule.span_le]
    rintro _ ⟨c, hc, rfl⟩
    let g' : Fin N → Rul (T.Q.Xo j) T.Q.c := fun i => ∑ l, c ⟨i, l⟩ • g i l
    have hg' : ∀ i, g' i ∈ sec (T.Q.Xo j) T.Q.c (a + b) (n + m) :=
      fun i => Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hg i l)
    have hcomp : ∀ i i', g' i * t i' = g' i' * t i := by
      intro i i'
      have hrowR : ∑ q, c q • A q (i, i') = g' i * t i' - g' i' * t i := by
        have h1 : ∀ q : κ, c q • A q (i, i') =
            (if q.1 = i then c q • (g q.1 q.2 * t i') else 0) -
            (if q.1 = i' then c q • (g q.1 q.2 * t i) else 0) := by
          intro q
          simp only [A]
          split_ifs <;> simp [smul_sub]
        simp only [h1, Finset.sum_sub_distrib]
        congr 1
        · rw [Fintype.sum_sigma, Finset.sum_eq_single i (fun i'' _ hi'' => by simp [hi'']) (by simp)]
          simp [g', Finset.sum_mul, smul_mul_assoc]
        · rw [Fintype.sum_sigma, Finset.sum_eq_single i' (fun i'' _ hi'' => by simp [hi'']) (by simp)]
          simp [g', Finset.sum_mul, smul_mul_assoc]
      have := hc (i, i')
      rw [hrowR] at this
      exact sub_eq_zero.1 this
    obtain ⟨h, hh, hht⟩ := glue_frPt D T j a b n m N t g' ht hunit hg' hcomp
    refine ⟨rdU (T.U j σ) h, Submodule.subset_span ⟨h, hh, rfl⟩, fun i => ?_⟩
    rw [← rdU_mul, hht]
    simp [g', map_sum, map_smulₛₗ]
  obtain ⟨Q, hQ, hQe⟩ := hle hzspan

  have hQoff : Q ∈ offZero (T.U j σ).X := by
    refine (Submodule.span_le.2 ?_) hQ
    rintro _ ⟨f, _, rfl⟩
    exact rdU_mem_offZero _ f
  have hPQ : P = Q := by
    funext k x
    by_cases hx : x ∈ ((T.U j σ).X k).dom
    · obtain ⟨i, hi⟩ := exists_rdU_t_ne_zero D T hT j hj σ hσ N t hunit k x hx
      have e1 := congrFun (congrFun (hQe i) k) x
      have e2 := congrFun (congrFun (hsum i) k) x
      have : Q k x * rdU (T.U j σ) (t i) k x = P k x * rdU (T.U j σ) (t i) k x := by
        rw [show Q k x * rdU (T.U j σ) (t i) k x = (Q * rdU (T.U j σ) (t i)) k x from rfl, e1,
          show P k x * rdU (T.U j σ) (t i) k x = (P * rdU (T.U j σ) (t i)) k x from rfl, ← e2]
      exact (mul_right_cancel₀ hi this).symm
    · rw [hP k x hx, hQoff k x hx]
  rw [hPQ]; exact hQ

end GlobalTheory.GlueSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHalfOfAuxiliarySplitLevel
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.MainNotions.StandardLattice Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.CoverRead

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HalfCharacter

theorem exists_half_of_auxiliary_split_level : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ pd : ℕ, GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.IsAuxiliarySplitSquarefreeLevel D T.Q.l.M pd →
  ∃ I : Ideal (𝓞 D.host.E), I = Ideal.span {x | x ∈ I ∧ x ∈ Algebra.adjoin ℤ {T.Q.H.w0}} ∧
    I * I.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = Ideal.span {(pd : 𝓞 D.host.E)} ∧
    I ⊔ I.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = ⊤ := by
  intro D T hJ pd haux
  obtain ⟨hodd, -, hjac, -, -⟩ := haux
  have hH : T.Q.PinHost := hJ.toLawsM.pins.1
  have hw : T.Q.H.w0 = w0E D := by
    have h1 := T.Q.H.two_weight_eq_one_add_root
    have h3 : T.Q.H.rt = rtE D := RingOfIntegers.ext hH.2.1
    rw [h3, ← two_w0E D] at h1
    exact mul_left_cancel₀ two_ne_zero h1
  have hb : (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = bH D :=
    RingHom.ext fun a => RingOfIntegers.ext (T.Q.H.bar_eq a)
  have hsp : ∀ p ∈ pd.primeFactorsList, SplitOK D p := by
    intro p hp
    have hpr := Nat.prime_of_mem_primeFactorsList hp
    have hdvd := Nat.dvd_of_mem_primeFactorsList hp
    refine ⟨hpr, ?_, hjac p hpr hdvd⟩
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hdvd)
  have hpd0 : pd ≠ 0 := hodd.pos.ne'
  refine ⟨MbOf D pd.primeFactorsList, ?_, ?_, ?_⟩
  · rw [hw]; exact MbOf_fromK D _
  · rw [hb]
    have h := MbProd_of D pd.primeFactorsList hsp
    unfold MbProdLaw at h
    rw [h, Nat.prod_primeFactorsList hpd0]
  · rw [hb]; exact MbCop_of D _ hsp

end GlobalTheory.HalfCharacter
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHcharPrescribedTrivial
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocLanglands

namespace GlobalTheory.DelEps.Twist

section Local

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def filtSub (a : ℕ) : Subgroup kˣ where
  carrier := unitFilt k a
  one_mem' := ⟨by simp, by simp⟩
  mul_mem' := fun {x y} hx hy => ⟨by rw [Units.val_mul, map_mul, hx.1, hy.1, one_mul], by
    have e : ((x * y : kˣ) : k) - 1 = (x : k) * ((y : k) - 1) + ((x : k) - 1) := by rw [Units.val_mul]; ring
    rw [e]
    refine Valuation.map_add_le _ ?_ hx.2
    rw [map_mul, hx.1, one_mul]
    exact hy.2⟩
  inv_mem' := fun {x} hx => by
    have h1 : valuation k ((x⁻¹ : kˣ) : k) = 1 := by rw [Units.val_inv_eq_inv_val, map_inv₀, hx.1, inv_one]
    refine ⟨h1, ?_⟩
    have e : ((x⁻¹ : kˣ) : k) - 1 = -(((x⁻¹ : kˣ) : k) * ((x : k) - 1)) := by
      linear_combination x.inv_mul
    rw [e, Valuation.map_neg, map_mul, h1, one_mul]
    exact hx.2

theorem isOpen_filtSub (a : ℕ) : IsOpen (filtSub k a : Set kˣ) :=
  (GroundTheory.LocalField.isOpen_setOf_valuation_eq_one.inter (GroundTheory.LocalField.isOpen_setOf_valuation_sub_le (a := (1 : k))
    (pow_ne_zero a uniformizer_ne_zero))).preimage Units.continuous_val

theorem ord_zpow (p : kˣ) (n : ℤ) : ord k (p ^ n) = n * ord k p := by
  let f : kˣ →* Multiplicative ℤ :=
    { toFun := fun x => Multiplicative.ofAdd (ord k x)
      map_one' := by rw [ord_eq_zero (by simp)]; rfl
      map_mul' := fun x y => by rw [ord_mul]; rfl }
  have := congrArg Multiplicative.toAdd (map_zpow f p n)
  simpa [f] using this

end Local

section Global

open Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {k : Type} [Field k] [NumberField k]

def comp (w : HeightOneSpectrum (𝓞 k)) : Ideles k →* (w.adicCompletion k)ˣ :=
  Units.map
    { toFun := fun a : AdeleRing (𝓞 k) k => a.2 w
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

theorem continuous_comp (w : HeightOneSpectrum (𝓞 k)) : Continuous (comp w) :=
  Continuous.units_map _ ((RestrictedProduct.continuous_eval w).comp continuous_snd)

theorem comp_diag (w : HeightOneSpectrum (𝓞 k)) (x : kˣ) : comp w (diagUnits k x) = atFin w x := Units.ext rfl

theorem comp_local_self (w : HeightOneSpectrum (𝓞 k)) (x : (w.adicCompletion k)ˣ) : comp w (localIdele k w x) = x :=
  Units.ext (localIdele_snd_self k w x)

theorem comp_local_ne {w w' : HeightOneSpectrum (𝓞 k)} (h : w' ≠ w) (x : (w.adicCompletion k)ˣ) :
    comp w' (localIdele k w x) = 1 :=
  Units.ext ((localIdele_isSupportedAt k w x).2 w' h)

theorem comp_inf (w : HeightOneSpectrum (𝓞 k)) (u : InfinitePlace k) (x : (u.Completion)ˣ) : comp w (infIdele k u x) = 1 :=
  Units.ext rfl

theorem exists_hchar_prescribed (k : Type) [Field k] [NumberField k] (S : Finset (HeightOneSpectrum (𝓞 k)))
    (θ : ∀ w : HeightOneSpectrum (𝓞 k), (w.adicCompletion k)ˣ →* ℂˣ) (hs : ∀ w ∈ S, IsSmoothChar (θ w))
    (hf : ∀ w ∈ S, ∃ N : ℕ, 0 < N ∧ θ w ^ N = 1) :
    ∃ η : HChar k, (∃ n : ℕ, 0 < n ∧ η.OrderDvd n) ∧ (∀ u : InfinitePlace k, η.locInf u = 1) ∧ ∀ w ∈ S, η.loc w = θ w := by
  classical
  choose! N hN0 hN using hf
  have hm0 : 0 < ∏ w ∈ S, N w := Finset.prod_pos hN0
  have hm : ∀ w ∈ S, ∀ x, θ w x ^ (∏ w ∈ S, N w) = 1 := fun w hw x => by
    obtain ⟨d, hd⟩ := Finset.dvd_prod_of_mem N hw
    rw [hd, pow_mul, ← MonoidHom.pow_apply, hN w hw, MonoidHom.one_apply, one_pow]
  set m := ∏ w ∈ S, N w
  obtain ⟨T, hST, hT⟩ := GlobalTheory.ChevalleySUnits.exists_places k S m hm0
  let U : Subgroup (Ideles k) := GlobalTheory.LevelChars.levSub k T 1 ⊓ ⨅ w : S, (θ w).ker.comap (comp w.1)
  have hU : IsOpen (U : Set (Ideles k)) := by
    have h1 : IsOpen (GlobalTheory.LevelChars.levSub k T 1 : Set (Ideles k)) := by
      convert (GlobalTheory.Mem.UnitOpen.unit_open_and_congr_open k).2 T 1 using 1
      ext a
      exact ⟨fun h => ⟨fun v => (h v).1, fun v hv => (h v).2 hv⟩, fun h v => ⟨h.1 v, h.2 v⟩⟩
    rw [Subgroup.coe_inf, Subgroup.coe_iInf]
    exact h1.inter (isOpen_iInter_of_finite fun w => (hs w w.2).preimage (continuous_comp w.1))
  let β : (∀ w : S, (w.1.adicCompletion k)ˣ) →* Ideles k :=
    ∏ w : S, (localIdele k w.1).comp (Pi.evalMonoidHom (fun w : S => (w.1.adicCompletion k)ˣ) w)
  let γ : (∀ w : S, (w.1.adicCompletion k)ˣ) →* ℂˣ :=
    ∏ w : S, (θ w.1).comp (Pi.evalMonoidHom (fun w : S => (w.1.adicCompletion k)ˣ) w)
  have hβ : ∀ y, β y = ∏ w : S, localIdele k w.1 (y w) := fun y => MonoidHom.finsetProd_apply _ _ _
  have hγ : ∀ y, γ y = ∏ w : S, θ w.1 (y w) := fun y => MonoidHom.finsetProd_apply _ _ _
  have hβS : ∀ y (w : S), comp w.1 (β y) = y w := fun y w => by
    rw [hβ, map_prod, Finset.prod_eq_single w, comp_local_self]
    · exact fun w' _ h => comp_local_ne (fun e => h (Subtype.ext e.symm)) _
    · simp
  have hβn : ∀ y v, v ∉ S → comp v (β y) = 1 := fun y v hv => by
    rw [hβ, map_prod]
    exact Finset.prod_eq_one fun w _ => comp_local_ne (fun e : v = w.1 => hv (e ▸ w.2)) _
  obtain ⟨χ, hχ, -, hχU, hχα⟩ := GlobalTheory.exists_unitary_char_of_open_subgroup_and_hom (Ideles k)
    (kˣ × ∀ w : S, (w.1.adicCompletion k)ˣ) U hU ((diagUnits k).coprod β) ((1 : kˣ →* ℂˣ).coprod γ) 1 continuous_const
    (fun _ => by simp)
    (fun y => by
      have h1 : γ y.2 ^ m = 1 := by
        rw [hγ, ← Finset.prod_pow]
        exact Finset.prod_eq_one fun w _ => hm w w.2 _
      have h2 : ((γ y.2 : ℂˣ) : ℂ) ^ m = 1 := by rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
      simpa using Complex.norm_eq_one_of_pow_eq_one h2 hm0.ne')
    (by
      rintro ⟨x, y⟩ ⟨h1, h2⟩
      have hval : ∀ (v : HeightOneSpectrum (𝓞 k)) (z : k),
          Valued.v (algebraMap k (v.adicCompletion k) z) = v.valuation k z := fun v z =>
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v z
      have hc : ∀ v, v ∉ S → GlobalTheory.LevelChars.compAt k v ((diagUnits k).coprod β (x, y)) =
          algebraMap k (v.adicCompletion k) (x : k) := fun v hv => by
        have e : comp v ((diagUnits k).coprod β (x, y)) = atFin v x := by
          rw [MonoidHom.coprod_apply, map_mul, comp_diag, hβn _ v hv, mul_one]
        exact congrArg Units.val e
      obtain ⟨z, hz⟩ := hT x (fun v hv => by rw [← hval, ← hc v hv]; exact (h1 v).1) (fun t ht => by
        have h3 := (h1 t).2 ht
        rw [hc t (Finset.disjoint_right.1 hST ht), ← map_one (algebraMap k (t.adicCompletion k)), ← map_sub, hval] at h3
        refine h3.trans_lt ?_
        rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
        simp)
      have hz0 : z ≠ 0 := by
        rintro rfl
        exact x.ne_zero (by rw [← hz, zero_pow hm0.ne'])
      have hxz : x = Units.mk0 z hz0 ^ m := Units.ext (by simp [hz])
      rw [MonoidHom.coprod_apply, MonoidHom.one_apply, MonoidHom.one_apply, one_mul, hγ]
      refine Finset.prod_eq_one fun w _ => ?_
      have h4 : θ w.1 (comp w.1 ((diagUnits k).coprod β (x, y))) = 1 := Subgroup.mem_iInf.1 h2 w
      rwa [MonoidHom.coprod_apply, map_mul, comp_diag, hβS, map_mul, hxz, map_pow, map_pow, hm w w.2, one_mul] at h4)
  let η : HChar k := ⟨χ, hχ, fun x => by simpa using hχα (x, 1)⟩
  have hinf : ∀ u : InfinitePlace k, η.locInf u = 1 := fun u => by
    ext x
    refine congrArg Units.val (hχU (infIdele k u x) ⟨fun v => ⟨map_one _, fun _ => ?_⟩, Subgroup.mem_iInf.2 fun w => ?_⟩)
    · change Valued.v ((1 : v.adicCompletion k) - 1) ≤ _
      simp
    · rw [Subgroup.mem_comap, comp_inf]
      exact one_mem _
  refine ⟨η, GlobalTheory.Mem.FinOrder.finite_order_of_inf_eq_one k η fun x => ?_, hinf, fun w hw => ?_⟩
  · change χ (infDiag x) = 1
    rw [infDiag, MonoidHom.finsetProd_apply, map_prod]
    exact Finset.prod_eq_one fun u _ => DFunLike.congr_fun (hinf u) (atInf u x)
  · refine MonoidHom.ext fun x => ?_
    have h := hχα (1, Pi.mulSingle (⟨w, hw⟩ : S) x)
    rw [MonoidHom.coprod_apply, MonoidHom.coprod_apply, map_one, map_one, one_mul, one_mul] at h
    dsimp only at h
    rw [hβ, hγ, Finset.prod_eq_single (⟨w, hw⟩ : S), Finset.prod_eq_single (⟨w, hw⟩ : S), Pi.mulSingle_eq_same] at h
    · exact h
    · intro w' _ h'
      rw [Pi.mulSingle_eq_of_ne h', map_one]
    · simp
    · intro w' _ h'
      rw [Pi.mulSingle_eq_of_ne h', map_one]
    · simp

end Global

end GlobalTheory.DelEps.Twist

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniquePlaceBelowOfUnramifiedPlaceOverPrime
section
open NumberField IsDedekindDomain

namespace GlobalTheory.InertiaEigenvalues.UnramPlace

theorem exists_place_below : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] (φ : K →+* L) (l : ℕ), l.Prime → ∀ la : HeightOneSpectrum (𝓞 L), ((l : ℕ) : 𝓞 L) ∈ la.asIdeal → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.UnramAt φ {la} → ∃ p : HeightOneSpectrum (𝓞 K), GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.below φ {la} = {p} ∧ ((l : ℕ) : 𝓞 K) ∈ p.asIdeal ∧ ∀ x : K, la.valuation L (φ x) = p.valuation K x := by
  intro K L _ _ _ _ φ l _ la hl hun
  letI : Algebra K L := φ.toAlgebra
  have hmap : RingOfIntegers.mapRingHom φ = algebraMap (𝓞 K) (𝓞 L) := by
    ext x; rfl
  refine ⟨la.under (𝓞 K), ?_, ?_, ?_⟩
  · ext q
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.below, Set.mem_singleton_iff, exists_eq_left, Set.mem_setOf_eq]
    rw [hmap]
    exact ⟨fun h => HeightOneSpectrum.ext h, fun h => h ▸ rfl⟩
  · show ((l : ℕ) : 𝓞 K) ∈ la.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L))
    rw [Ideal.mem_comap, map_natCast]
    exact hl
  · intro x
    have hu := hun la rfl
    rw [hmap] at hu
    have : la.asIdeal.LiesOver (la.under (𝓞 K)).asIdeal := ⟨rfl⟩
    have he : (la.under (𝓞 K)).asIdeal.ramificationIdx' la.asIdeal = 1 := by
      refine Ideal.ramificationIdx'_spec ?_ ?_
      · rw [pow_one]; exact Ideal.map_comap_le
      · exact hu
    have h := HeightOneSpectrum.valuation_liesOver L (la.under (𝓞 K)) la x
    rw [he, pow_one] at h
    exact h.symm

end GlobalTheory.InertiaEigenvalues.UnramPlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaOperatorSemisimpleOfConclusionsStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gamma_operator_semisimple_of_conclusions : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), Formalism.MainNotions.DeltaInvariantLattices.DeltaInvariantNormBound D HW F Cm → Formalism.MainNotions.LiftingTheory.adm19 D HW F := by
  first | exact @GlobalTheory.dss_semisimple_of_used | exact GlobalTheory.dss_semisimple_of_used | (intros; apply GlobalTheory.dss_semisimple_of_used <;> assumption)
end

