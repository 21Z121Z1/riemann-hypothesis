import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0303
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0330
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgClosedTiltFieldAndValuationRing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0041
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsElementsSelmerFormsSmallCorank
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0331
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleRingImageAddEllPiAdicClosed
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

namespace GlobalTheory.Decompl

theorem powerSeries_exists_sum {O : Type} [CommRing O] (a : ℕ → PowerSeries O) :
    ∃ s : PowerSeries O, ∀ m, ∃ b,
      s = ∑ i ∈ Finset.range m, PowerSeries.X ^ i * a i + PowerSeries.X ^ m * b := by
  set s : PowerSeries O := PowerSeries.mk fun n =>
    PowerSeries.coeff (R := O) n (∑ i ∈ Finset.range (n + 1), PowerSeries.X ^ i * a i) with hs
  refine ⟨s, fun m => ?_⟩
  have hdvd : PowerSeries.X ^ m ∣ s - ∑ i ∈ Finset.range m, PowerSeries.X ^ i * a i := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro n hn
    rw [map_sub, hs, PowerSeries.coeff_mk, sub_eq_zero]

    have key : ∀ d, PowerSeries.coeff (R := O) n (∑ i ∈ Finset.range (n + 1 + d), PowerSeries.X ^ i * a i)
        = PowerSeries.coeff (R := O) n (∑ i ∈ Finset.range (n + 1), PowerSeries.X ^ i * a i) := by
      intro d
      induction d with
      | zero => rfl
      | succ d ih =>
        rw [show n + 1 + (d + 1) = n + 1 + d + 1 by omega, Finset.sum_range_succ, map_add, ih,
          PowerSeries.coeff_X_pow_mul', if_neg (by omega), add_zero]
    have := key (m - (n + 1))
    rw [show n + 1 + (m - (n + 1)) = m by omega] at this
    exact this.symm
  obtain ⟨b, hb⟩ := hdvd
  exact ⟨b, by rw [← hb]; ring⟩

theorem letA_exists_sum {O : Type} [CommRing O] {n : ℕ} (a : ℕ → LetA O n) :
    ∃ s : LetA O n, ∀ m, ∃ b, s = ∑ i ∈ Finset.range m, letπ ^ i * a i + letπ ^ m * b := by
  choose s hs using fun k : ZMod n => powerSeries_exists_sum (fun i => a i k)
  refine ⟨s, fun m => ?_⟩
  choose b hb using fun k => hs k m
  refine ⟨b, ?_⟩
  funext k
  rw [hb k]
  unfold letπ
  simp [Finset.sum_apply, Pi.pow_apply, Pi.mul_apply]

theorem near_closed_abstract {A E S R : Type} [CommRing A] [CommRing E] [CommRing S] [CommRing R]
    (j : A →+* E) (io : A →+* S) (ι : S →+* R) (f : E →+* R) (p : ℕ) (π : A) (t : R)
    (hext : ∀ a, f (j a) = ι (io a)) (ht : ι (io π) = t)
    (hsum : ∀ a : ℕ → A, ∃ s, ∀ m, ∃ b, s = ∑ i ∈ Finset.range m, π ^ i * a i + π ^ m * b)
    (hsep : ∀ x : R, (∀ m, Near ι p t m x) → ∃ r, x = (p : R) * r)
    (hE : ∀ m e, Near ι p t m (f e) → ∃ a e', e = j (π ^ m * a) + (p : E) * e')
    (x : R) (hx : ∀ m, ∃ e, Near ι p t m (x - f e)) : ∃ e r, x - f e = (p : R) * r := by
  unfold Near at hsep hE hx
  choose e he using hx

  have hD : ∀ i, ∃ a r, f (e (i + 1) - e i) = t ^ i * ι a + (p : R) * r := by
    intro i
    obtain ⟨a0, r0, h0⟩ := he i
    obtain ⟨a1, r1, h1⟩ := he (i + 1)
    refine ⟨a0 - io π * a1, r0 - r1, ?_⟩
    have hsplit : f (e (i + 1) - e i) = (x - f (e i)) - (x - f (e (i + 1))) := by
      rw [map_sub]; ring
    rw [hsplit, h0, h1, map_sub, map_mul, ht]
    ring
  choose a e' hae using fun i => hE i _ (hD i)
  obtain ⟨s, hs⟩ := hsum a
  have hsumD : ∀ m, e m = e 0 + j (∑ i ∈ Finset.range m, π ^ i * a i) +
      (p : E) * ∑ i ∈ Finset.range m, e' i := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, map_add]
      linear_combination hae k + ih
  refine ⟨e 0 + j s, hsep _ fun m => ?_⟩
  obtain ⟨b, hb⟩ := hs m
  obtain ⟨a0, r0, h0⟩ := he m
  refine ⟨a0 - io b, r0 + f (∑ i ∈ Finset.range m, e' i), ?_⟩
  have key : f (e 0 + j s) = f (e m) - (p : R) * f (∑ i ∈ Finset.range m, e' i) + t ^ m * ι (io b) := by
    rw [hsumD m, hb]
    simp only [map_add, map_mul, map_pow, map_natCast, hext, ht]
    ring
  rw [key, map_sub]
  linear_combination h0

set_option maxHeartbeats 1000000 in
private theorem ioE_closed_lemma (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l)
    (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : Wach P K LL) (E : EtSit P AI K s LL h W) (x : RW LL)
    (hx : ∀ m, ∃ e, NearPi AI LL s m (x - E.tie.ioE e)) : ∃ e r, x - E.tie.ioE e = (l : RW LL) * r := by
  obtain ⟨hsep, -⟩ := GlobalTheory.T.nearPi_sep_complete_alt l P AI LL s
  obtain ⟨hE, -⟩ := GlobalTheory.T.etaleComparison_piAdic_filtration_mod_ell l P AI K s LL h W E
  have hext : ∀ a, E.tie.ioE (algebraMap (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) W.EE a) =
      inclR LL (E.tie.io a) := by
    intro a
    exact E.tie.ioE_ext a
  have ht : inclR LL (E.tie.io letπ) = piR AI LL s := by
    rw [E.tie.io_π]
    rfl

  have hN : ∀ m y, NearPi AI LL s m y ↔ Near (inclR LL : RA LL →+* RW LL) l (piR AI LL s) m y :=
    fun _ _ => Iff.rfl
  simp only [hN] at hsep hE hx
  exact near_closed_abstract (algebraMap _ W.EE) (E.tie.io : _ →+* RA LL) (inclR LL : RA LL →+* RW LL)
    (E.tie.ioE : W.EE →+* RW LL) l letπ (piR AI LL s) hext ht letA_exists_sum hsep hE x hx

theorem ioE_closed : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : Wach P K LL) (E : EtSit P AI K s LL h W) (x : RW LL), (∀ m, ∃ e, NearPi AI LL s m (x - E.tie.ioE e)) → ∃ e r, x - E.tie.ioE e = (l : RW LL) * r := by
  intro l _ P AI K s LL h W E x hx
  exact ioE_closed_lemma l P AI K s LL h W E x hx

end GlobalTheory.Decompl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdicTopologicalBasisOfSpanOfStrict
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.TopBasisCons

variable {S A : Type} [CommRing S] [CommRing A] {s : S →+* A} {I : Ideal S} {ι : Type} {b : ι → A}

variable (s I b) in

def Approx (x : A) (f : ι → S) : Prop :=
  ∀ n : ℕ, ∃ F : Finset ι, (∀ i, i ∉ F → f i ∈ I ^ n) ∧ x - ∑ i ∈ F, s (f i) * b i ∈ (I ^ n).map s

theorem smodEq_iff (x y : S) (n : ℕ) : x ≡ y [SMOD (I ^ n • ⊤ : Submodule S S)] ↔ x - y ∈ I ^ n := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]

theorem sum_sub_sum_mem {f : ι → S} {n : ℕ} {F G : Finset ι} (hF : ∀ i, i ∉ F → f i ∈ I ^ n)
    (hG : ∀ i, i ∉ G → f i ∈ I ^ n) :
    ∑ i ∈ F, s (f i) * b i - ∑ i ∈ G, s (f i) * b i ∈ (I ^ n).map s := by
  classical
  rw [← Finset.sum_sdiff (Finset.inter_subset_left : F ∩ G ⊆ F),
    ← Finset.sum_sdiff (Finset.inter_subset_right : F ∩ G ⊆ G), add_sub_add_right_eq_sub]
  refine sub_mem (Ideal.sum_mem _ fun i hi => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem s (hG i fun h => ?_)))
    (Ideal.sum_mem _ fun i hi => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem s (hF i fun h => ?_)))
  · exact (Finset.mem_sdiff.1 hi).2 (Finset.mem_inter.2 ⟨(Finset.mem_sdiff.1 hi).1, h⟩)
  · exact (Finset.mem_sdiff.1 hi).2 (Finset.mem_inter.2 ⟨h, (Finset.mem_sdiff.1 hi).1⟩)

theorem Approx.approx {x : A} {f : ι → S} (h : Approx s I b x f) (n : ℕ) (F : Finset ι)
    (hF : ∀ i, i ∉ F → f i ∈ I ^ n) : x - ∑ i ∈ F, s (f i) * b i ∈ (I ^ n).map s := by
  obtain ⟨G, hG, hx⟩ := h n
  have := sub_mem hx (sum_sub_sum_mem (s := s) (b := b) hF hG)
  rwa [sub_sub_sub_cancel_right] at this

theorem Approx.finite {x : A} {f : ι → S} (h : Approx s I b x f) (n : ℕ) : {i | f i ∉ I ^ n}.Finite := by
  obtain ⟨F, hF, -⟩ := h n
  exact F.finite_toSet.subset fun i hi => by_contra fun h' => hi (hF i h')

theorem Approx.add {x y : A} {f g : ι → S} (hx : Approx s I b x f) (hy : Approx s I b y g) :
    Approx s I b (x + y) (f + g) := by
  classical
  intro n
  obtain ⟨F, hF, -⟩ := hx n
  obtain ⟨G, hG, -⟩ := hy n
  refine ⟨F ∪ G, fun i hi => ?_, ?_⟩
  · simp only [Finset.mem_union, not_or] at hi
    exact add_mem (hF i hi.1) (hG i hi.2)
  · have h1 := hx.approx n (F ∪ G) fun i hi => hF i fun h => hi (Finset.mem_union_left _ h)
    have h2 := hy.approx n (F ∪ G) fun i hi => hG i fun h => hi (Finset.mem_union_right _ h)
    convert add_mem h1 h2 using 1
    simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
    ring

theorem Approx.mul {x : A} {f : ι → S} (hx : Approx s I b x f) (a : S) :
    Approx s I b (s a * x) (fun i => a * f i) := by
  intro n
  obtain ⟨F, hF, h⟩ := hx n
  refine ⟨F, fun i hi => Ideal.mul_mem_left _ _ (hF i hi), ?_⟩
  convert Ideal.mul_mem_left _ (s a) h using 1
  simp only [map_mul, mul_sub, Finset.mul_sum, mul_assoc]

theorem approx_single [DecidableEq ι] (i : ι) : Approx s I b (b i) (Pi.single i 1) := by
  intro n
  refine ⟨{i}, fun j hj => ?_, by simp⟩
  rw [Pi.single_eq_of_ne (by simpa using hj)]
  exact zero_mem _

theorem Approx.eq_zero (hH : IsHausdorff I S)
    (hst : ∀ n : ℕ, ∃ m : ℕ, ∀ a : ι →₀ S, a.sum (fun i y => s y * b i) ∈ (I ^ m).map s → ∀ i, a i ∈ I ^ n)
    {h : ι → S} (hh : Approx s I b 0 h) : h = 0 := by
  classical
  funext i
  refine hH.haus (h i) fun n => ?_
  rw [smodEq_iff, sub_zero]
  obtain ⟨m, hm⟩ := hst n
  obtain ⟨F, hF, hs⟩ := hh (max n m)
  by_cases hi : i ∈ F
  · have key := hm (Finsupp.onFinset F (fun j => if j ∈ F then h j else 0)
      (fun j hj => by by_contra hj'; simp [hj'] at hj)) ?_ i
    · simpa [hi] using key
    · rw [Finsupp.onFinset_sum _ (fun j => by simp)]
      have e : ∑ j ∈ F, s (if j ∈ F then h j else 0) * b j = -(0 - ∑ j ∈ F, s (h j) * b j) := by
        rw [zero_sub, neg_neg]
        exact Finset.sum_congr rfl fun j hj => by rw [if_pos hj]
      rw [e]
      exact neg_mem (Ideal.map_mono (Ideal.pow_le_pow_right (le_max_right n m)) hs)
  · exact Ideal.pow_le_pow_right (le_max_left n m) (hF i hi)

end GlobalTheory.BSP.TopBasisCons

namespace GlobalTheory.BSP.TopBasisCons

variable {S A : Type} [CommRing S] [CommRing A] {s : S →+* A} {I : Ideal S} {ι : Type} {b : ι → A}

theorem exists_step (hsp : ∀ x : A, ∃ a : ι →₀ S, x - a.sum (fun i y => s y * b i) ∈ I.map s) (n : ℕ) (y : A)
    (hy : y ∈ (I ^ n).map s) : ∃ a : ι →₀ S, (∀ i, a i ∈ I ^ n) ∧
      y - a.sum (fun i c => s c * b i) ∈ (I ^ (n + 1)).map s := by
  classical
  let T : A → Prop := fun y => ∃ a : ι →₀ S, (∀ i, a i ∈ I ^ n) ∧
      y - a.sum (fun i c => s c * b i) ∈ (I ^ (n + 1)).map s
  have T0 : T 0 := ⟨0, fun _ => zero_mem _, by simp⟩
  have Tadd : ∀ y y', T y → T y' → T (y + y') := by
    rintro y y' ⟨a, ha, hy⟩ ⟨a', ha', hy'⟩
    refine ⟨a + a', fun i => add_mem (ha i) (ha' i), ?_⟩
    rw [Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by rw [map_add, add_mul])]
    convert add_mem hy hy' using 1
    ring
  have T1 : ∀ t ∈ I ^ n, ∀ w : A, T (s t * w) := by
    intro t ht w
    obtain ⟨a, ha⟩ := hsp w
    refine ⟨t • a, fun i => by rw [Finsupp.smul_apply, smul_eq_mul]; exact Ideal.mul_mem_right _ _ ht, ?_⟩
    rw [Finsupp.sum_smul_index (fun _ => by simp)]
    have e : s t * w - a.sum (fun i c => s (t * c) * b i) = s t * (w - a.sum (fun i c => s c * b i)) := by
      rw [mul_sub, Finsupp.mul_sum]
      simp only [map_mul, mul_assoc]
    rw [e, Ideal.map_pow, pow_succ]
    exact Ideal.mul_mem_mul (by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem s ht) ha
  have key : ∀ y' ∈ Submodule.span A (s '' ((I ^ n : Ideal S) : Set S)), ∀ z, T (z * y') := by
    intro y' hy'
    induction hy' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, ht, rfl⟩ := hx
      exact fun z => by rw [mul_comm]; exact T1 t ht z
    | zero => exact fun z => by rw [mul_zero]; exact T0
    | add x x' _ _ hx hx' => exact fun z => by rw [mul_add]; exact Tadd _ _ (hx z) (hx' z)
    | smul a x _ hx => exact fun z => by rw [smul_eq_mul, ← mul_assoc]; exact hx (z * a)
  simpa using key y hy 1

theorem exists_approx (hS : IsPrecomplete I S) (g : ℕ → A → ι →₀ S)
    (hg1 : ∀ n y, y ∈ (I ^ n).map s → ∀ i, g n y i ∈ I ^ n)
    (hg2 : ∀ n y, y ∈ (I ^ n).map s → y - (g n y).sum (fun i c => s c * b i) ∈ (I ^ (n + 1)).map s) (x : A) :
    ∃ f, Approx s I b x f := by
  classical
  let r : ℕ → A := fun n => Nat.rec x (fun k rk => rk - (g k rk).sum (fun i c => s c * b i)) n
  have hrs : ∀ k, r (k + 1) = r k - (g k (r k)).sum (fun i c => s c * b i) := fun k => rfl
  have hrm : ∀ k, r k ∈ (I ^ k).map s := by
    intro k
    induction k with
    | zero => simp [r, Ideal.map_top]
    | succ k ih => rw [hrs]; exact hg2 k _ ih
  let a : ℕ → ι →₀ S := fun k => g k (r k)
  have ha : ∀ k i, a k i ∈ I ^ k := fun k => hg1 k _ (hrm k)
  have hrx : ∀ N, r N = x - ∑ k ∈ Finset.range N, (a k).sum (fun i c => s c * b i) := by
    intro N
    induction N with
    | zero => simp [r]
    | succ N ih => rw [hrs, Finset.sum_range_succ, ← sub_sub, ← ih]
  let P : ℕ → ι → S := fun N i => ∑ k ∈ Finset.range N, a k i
  have hP : ∀ i m n, m ≤ n → P n i - P m i ∈ I ^ m := by
    intro i m n hmn
    rw [← Finset.sum_Ico_eq_sub _ hmn]
    exact Ideal.sum_mem _ fun k hk => Ideal.pow_le_pow_right (Finset.mem_Ico.1 hk).1 (ha k i)
  have hlim : ∀ i, ∃ L, ∀ N, P N i - L ∈ I ^ N := by
    intro i
    obtain ⟨L, hL⟩ := hS.prec (f := fun N => P N i) fun {m n} hmn => by
      rw [smodEq_iff, ← neg_sub]; exact neg_mem (hP i m n hmn)
    exact ⟨L, fun N => (smodEq_iff _ _ _).1 (hL N)⟩
  choose f hf using hlim
  refine ⟨f, fun n => ?_⟩
  let F : Finset ι := (Finset.range n).biUnion fun k => (a k).support
  have hPF : ∀ i, i ∉ F → P n i = 0 := fun i hi => Finset.sum_eq_zero fun k hk => by
    by_contra h
    exact hi (Finset.mem_biUnion.2 ⟨k, hk, Finsupp.mem_support_iff.2 h⟩)
  refine ⟨F, fun i hi => ?_, ?_⟩
  · have := neg_mem (hf i n)
    rwa [hPF i hi, zero_sub, neg_neg] at this
  · have hsum : ∑ k ∈ Finset.range n, (a k).sum (fun i c => s c * b i) = ∑ i ∈ F, s (P n i) * b i := by
      rw [Finset.sum_congr rfl fun k hk => Finsupp.sum_of_support_subset (a k) (s := F)
        (fun i hi => Finset.mem_biUnion.2 ⟨k, hk, hi⟩) (fun i c => s c * b i) (fun _ _ => by simp),
        Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [P, map_sum, Finset.sum_mul]
    have e : x - ∑ i ∈ F, s (f i) * b i = r n + ∑ i ∈ F, s (P n i - f i) * b i := by
      rw [hrx, hsum]
      simp only [map_sub, sub_mul, Finset.sum_sub_distrib]
      ring
    rw [e]
    exact add_mem (hrm n) (Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem s (hf i n)))

end GlobalTheory.BSP.TopBasisCons

open GlobalTheory.BSP.TopBasisCons in

theorem GlobalTheory.BSP.exists_topBasis_of_span_of_strict : ∀ (S A : Type) [CommRing S] [CommRing A] (s : S →+* A)
    (I : Ideal S) (ι : Type) (b : ι → A) (i₀ : ι), b i₀ = 1 → I.FG → IsAdicComplete I S →
    IsAdicComplete (I.map s) A → (∀ x : A, ∃ a : ι →₀ S, x - a.sum (fun i y => s y * b i) ∈ I.map s) →
    (∀ n : ℕ, ∃ m : ℕ, ∀ a : ι →₀ S, a.sum (fun i y => s y * b i) ∈ (I ^ m).map s → ∀ i, a i ∈ I ^ n) →
    ∃ TB : TopBasis s I ι, TB.b = b := by
  intro S A _ _ s I ι b i₀ hb0 _ hS hA hsp hst
  classical
  choose! g hg1 hg2 using exists_step (s := s) (I := I) (b := b) hsp
  have hex : ∀ x, ∃ f, Approx s I b x f := exists_approx hS.toIsPrecomplete g hg1 hg2
  choose coef hcoef using hex
  have huniq : ∀ {x : A} {f g : ι → S}, Approx s I b x f → Approx s I b x g → f = g := by
    intro x f g hf hg
    have h := hf.add (hg.mul (-1))
    have e : x + s (-1) * x = 0 := by simp
    rw [e] at h
    have := h.eq_zero hS.toIsHausdorff hst
    funext i
    have hi := congrFun this i
    simp only [Pi.add_apply, Pi.zero_apply, neg_one_mul] at hi
    exact sub_eq_zero.1 (by rw [sub_eq_add_neg]; exact hi)
  let c : ι → A →+ S := fun i =>
    AddMonoidHom.mk' (fun x => coef x i) fun x y => congrFun (huniq (hcoef (x + y)) ((hcoef x).add (hcoef y))) i
  refine ⟨⟨b, c, ?_, ?_, ?_, ?_, ?_, hA, i₀, hb0⟩, rfl⟩
  · intro i a x
    change coef (s a * x) i = a * coef x i
    rw [huniq (hcoef (s a * x)) ((hcoef x).mul a)]
  · intro i
    change coef (b i) i = 1
    rw [huniq (hcoef (b i)) (approx_single i)]
    simp
  · intro i j hij
    change coef (b j) i = 0
    rw [huniq (hcoef (b j)) (approx_single j)]
    exact Pi.single_eq_of_ne hij _
  · intro x n
    exact (hcoef x).finite n
  · intro x n F hF
    exact (hcoef x).approx n F hF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAinfUnitFrobeniusEqMul
section
noncomputable section

open Polynomial

namespace GlobalTheory.Per.LangUnit

open GlobalTheory.Cyc.FontW

theorem onto_of_cpl' {l : ℕ} {M : Type} [AddCommGroup M] (hM : Cpl l M) (f : M →+ M)
    (h : ∀ y, ∃ x z, f x - y = l • z) : Function.Surjective f := by
  intro y
  have hstep : ∀ (r : ℕ) (x : M), f x - y ∈ Dv l r M →
      ∃ x', f x' - y ∈ Dv l (r + 1) M ∧ x' - x ∈ Dv l r M := by
    intro r x hx
    obtain ⟨u, hu⟩ := mem_Dv.1 hx
    obtain ⟨a, z, haz⟩ := h (-u)
    refine ⟨x + l ^ r • a, mem_Dv.2 ⟨z, ?_⟩, mem_Dv.2 ⟨a, by abel⟩⟩
    rw [pow_succ, mul_smul, ← haz, map_add, map_nsmul, add_sub_right_comm, ← hu, sub_neg_eq_add,
      smul_add, add_comm]
  choose nx hnx using hstep
  let g : (r : ℕ) → {x // f x - y ∈ Dv l r M} := fun r =>
    Nat.rec ⟨0, mem_Dv.2 ⟨_, by rw [pow_zero, one_smul]⟩⟩
      (fun r b => ⟨nx r b.1 b.2, (hnx r b.1 b.2).1⟩) r
  obtain ⟨L, hL⟩ := hM.2 (fun r => (g r).1) fun r => (hnx r (g r).1 (g r).2).2
  refine ⟨L, sub_eq_zero.1 (hM.1 _ fun r => ?_)⟩
  have e : f L - y = f (L - (g r).1) + (f (g r).1 - y) := by rw [map_sub]; abel
  rw [e]
  exact add_mem (Dv_map f (hL r)) (g r).2

variable {p : ℕ} [hp : Fact p.Prime] {k : Type} [CommRing k] [CharP k p] [PerfectRing k p]

theorem eq_smul_of_coeff_zero {A : WittVector p k} (hA : A.coeff 0 = 0) : ∃ Z, A = p • Z := by
  have h0 : A ∈ Ideal.span {(p : WittVector p k)} := by
    rw [← WittVector.ker_constantCoeff, RingHom.mem_ker, WittVector.constantCoeff_apply]
    exact hA
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 h0
  exact ⟨u, by rw [← hu, nsmul_eq_mul, mul_comm]⟩

theorem coeff_zero_frob_sub (ω X : WittVector p k) :
    (WittVector.frobenius X - ω * X).coeff 0 = X.coeff 0 ^ p - ω.coeff 0 * X.coeff 0 := by
  simp only [← WittVector.constantCoeff_apply, map_sub, map_mul]
  rw [WittVector.constantCoeff_apply, WittVector.coeff_frobenius_charP]
  simp only [WittVector.constantCoeff_apply]

theorem lang_unit
    (hroot : ∀ f : k[X], f.Monic → 0 < f.natDegree → ∃ x, f.IsRoot x)
    (ω : WittVector p k) (hω : IsUnit ω) :
    ∃ η : WittVector p k, IsUnit η ∧ WittVector.frobenius η = ω * η := by
  have hp1 : 1 < p := hp.out.one_lt
  haveI : Nontrivial k := CharP.nontrivial_of_char_ne_one hp.out.ne_one
  set ω₀ := ω.coeff 0 with hω₀
  have hu0 : IsUnit ω₀ := by
    rw [hω₀, ← WittVector.constantCoeff_apply]; exact hω.map _
  let f : WittVector p k →+ WittVector p k :=
    (WittVector.frobenius : WittVector p k →+* WittVector p k).toAddMonoidHom -
      AddMonoidHom.mulLeft ω
  have hf : ∀ X, f X = WittVector.frobenius X - ω * X := fun X => rfl

  have hmod : ∀ Y, ∃ X Z, f X - Y = p • Z := by
    intro Y
    obtain ⟨x, hx⟩ := hroot (X ^ p - (C ω₀ * X + C (Y.coeff 0)))
      (monic_X_pow_sub (by
        refine (degree_add_le _ _).trans_lt (max_lt ?_ ?_)
        · exact (degree_C_mul_X_le _).trans_lt (by exact_mod_cast hp1)
        · exact (degree_C_le).trans_lt (by exact_mod_cast (by omega : 0 < p))))
      (by
        have hlow : (C ω₀ * X + C (Y.coeff 0)).natDegree < p := by
          refine (natDegree_add_le _ _).trans_lt (max_lt ?_ ?_)
          · exact ((natDegree_C_mul_le _ _).trans natDegree_X_le).trans_lt hp1
          · rw [natDegree_C]; omega
        rw [natDegree_sub_eq_left_of_natDegree_lt (by rwa [natDegree_X_pow]), natDegree_X_pow]
        omega)
    refine ⟨WittVector.teichmuller p x, eq_smul_of_coeff_zero ?_⟩
    have hx' : x ^ p - (ω₀ * x + Y.coeff 0) = 0 := by simpa using hx
    rw [← WittVector.constantCoeff_apply, map_sub, WittVector.constantCoeff_apply,
      WittVector.constantCoeff_apply, hf, coeff_zero_frob_sub, WittVector.teichmuller_coeff_zero,
      ← hω₀]
    rw [← hx']; ring

  obtain ⟨t₀, ht₀⟩ := hroot (X ^ (p - 1) - C ω₀) (monic_X_pow_sub_C _ (by omega))
    (by rw [natDegree_X_pow_sub_C]; omega)
  have ht₀' : t₀ ^ (p - 1) = ω₀ := by simpa [sub_eq_zero] using ht₀
  have hut : IsUnit t₀ := (isUnit_pow_iff (by omega : p - 1 ≠ 0)).1 (ht₀' ▸ hu0)
  have htp : t₀ ^ p = ω₀ * t₀ := by
    rw [← ht₀', ← pow_succ, Nat.sub_add_cancel hp.out.one_le]
  set t := WittVector.teichmuller p t₀ with ht
  obtain ⟨Y, hY⟩ := eq_smul_of_coeff_zero (A := f t) (by
    rw [hf, coeff_zero_frob_sub, ht, WittVector.teichmuller_coeff_zero, ← hω₀, htp, sub_self])
  obtain ⟨Z, rfl⟩ := onto_of_cpl' (cpl_witt p k) f hmod Y
  refine ⟨t - p • Z, ?_, ?_⟩
  · have hj : -(p • Z) ∈ (⊥ : Ideal (WittVector p k)).jacobson :=
      IsAdicComplete.le_jacobson_bot (Ideal.span {(p : WittVector p k)})
        (neg_mem (Ideal.mem_span_singleton'.2 ⟨Z, by rw [nsmul_eq_mul, mul_comm]⟩))
    obtain ⟨u, hu⟩ : IsUnit t := hut.map (WittVector.teichmuller p)
    have h1 := Ideal.mem_jacobson_bot.1 hj (↑u⁻¹)
    have e : t - p • Z = (-(p • Z) * ↑u⁻¹ + 1) * u := by
      rw [add_mul, mul_assoc, Units.inv_mul, mul_one, one_mul, hu]; abel
    rw [e]
    exact h1.mul u.isUnit
  · rw [← sub_eq_zero, ← hf, map_sub, map_nsmul, hY, sub_self]

end GlobalTheory.Per.LangUnit

namespace GlobalTheory.Per

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc

set_option synthInstance.maxHeartbeats 400000 in

theorem OCb_exists_root (l : ℕ) [Fact l.Prime] (f : (OCb l)[X]) (hf : f.Monic)
    (hd : 0 < f.natDegree) : ∃ x, f.IsRoot x := by
  haveI : IsAlgClosed (Cb l) := (GlobalTheory.TiltAlgClosed.isAlgClosed_tilt_and_valuationRing l).1
  haveI : ValuationRing (OCb l) := (GlobalTheory.TiltAlgClosed.isAlgClosed_tilt_and_valuationRing l).2
  haveI : IsIntegrallyClosed (OCb l) := inferInstance
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (f.map (algebraMap (OCb l) (Cb l))) (by
    rw [degree_map_eq_of_injective (IsFractionRing.injective (OCb l) (Cb l)),
      degree_eq_natDegree hf.ne_zero]
    exact_mod_cast hd.ne')
  have hint : IsIntegral (OCb l) z := ⟨f, hf, by rwa [IsRoot, eval_map_algebraMap] at hz⟩
  obtain ⟨x, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  refine ⟨x, IsFractionRing.injective (OCb l) (Cb l) ?_⟩
  rw [IsRoot, eval_map_algebraMap, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval] at hz
  rw [hz, map_zero]

theorem frobenius_eq_mul_solvable :
    ∀ (l : ℕ) [Fact l.Prime] (ω : (Ainf l)ˣ), ∃ η : (Ainf l)ˣ, WittVector.frobenius (η : Ainf l) = ω * η := by
  intro l _ ω
  obtain ⟨η, ⟨u, rfl⟩, h⟩ := GlobalTheory.Per.LangUnit.lang_unit (p := l) (k := OCb l)
    (OCb_exists_root l) (ω : Ainf l) ω.isUnit
  exact ⟨u, h⟩

end GlobalTheory.Per
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsElementsSelmerFormsSmallCorankStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_elements_selmerForms_small_corank : GlobalFiniteness → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw), (∀ s, GalHyp bkP i s → SpanOdd i s ∧ SpanTwo i s ∧ EqDim bkP i s) → ChooseH bkP i := by
  first | exact @GlobalTheory.ChooseForms.chooseH | exact GlobalTheory.ChooseForms.chooseH | (intros; apply GlobalTheory.ChooseForms.chooseH <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInitialSegmentNotInfLeFiltrationStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_initialSegment_not_inf_le_filtration : ∀ (G : Type) [Group G] (R : ℕ → Subgroup G) (A B : Subgroup G), Antitone R → (∃ m, R m = ⊥) → ∃ n : ℕ, ∀ t, t < n ↔ ¬ A ⊓ R t ≤ B := by
  first | exact @GlobalTheory.PMon.Ram.exists_initialSegment_not_inf_le | exact GlobalTheory.PMon.Ram.exists_initialSegment_not_inf_le | (intros; apply GlobalTheory.PMon.Ram.exists_initialSegment_not_inf_le <;> assumption)
end

