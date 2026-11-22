import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0416
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0289
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0425
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleRankR
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Formalism.PadicSubsetSums.StableGradedCounts.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0421
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0424

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MittagLefflerImageBreuilKisinModPow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.ImageTower

variable {S A : Type} [CommRing S] [CommRing A] (e : S →+* A) (p : ℕ) {d : ℕ} {d' : ℕ → ℕ}
  (R : ∀ n, Matrix (Fin d) (Fin (d' n)) A)

def Img (n m : ℕ) : Set (Fin d → A) :=
  {w | ∃ s : Fin (d' m) → S, ∀ i, (p : A) ^ n ∣ (w - R m *ᵥ fun j => e (s j)) i}

variable {e p R}

theorem mem_of_dvd {n m : ℕ} {w x : Fin d → A} (hw : w ∈ Img e p R n m)
    (h : ∀ i, (p : A) ^ n ∣ (x - w) i) : x ∈ Img e p R n m := by
  obtain ⟨s, hs⟩ := hw
  refine ⟨s, fun i => ?_⟩
  have : (x - R m *ᵥ fun j => e (s j)) i = (x - w) i + (w - R m *ᵥ fun j => e (s j)) i := by
    simp only [Pi.sub_apply]; ring
  rw [this]; exact dvd_add (h i) (hs i)

theorem add_mem {n m : ℕ} {w x : Fin d → A} (hw : w ∈ Img e p R n m) (hx : x ∈ Img e p R n m) :
    w + x ∈ Img e p R n m := by
  obtain ⟨s, hs⟩ := hw
  obtain ⟨t, ht⟩ := hx
  refine ⟨s + t, fun i => ?_⟩
  have he : (fun j => e ((s + t) j)) = (fun j => e (s j)) + fun j => e (t j) := by
    funext j; simp
  rw [he, mulVec_add]
  have : (w + x - ((R m *ᵥ fun j => e (s j)) + R m *ᵥ fun j => e (t j))) i =
      (w - R m *ᵥ fun j => e (s j)) i + (x - R m *ᵥ fun j => e (t j)) i := by
    simp only [Pi.sub_apply, Pi.add_apply]; ring
  rw [this]; exact dvd_add (hs i) (ht i)

theorem image_mem (n m : ℕ) (s : Fin (d' m) → S) : (R m *ᵥ fun j => e (s j)) ∈ Img e p R n m :=
  ⟨s, fun i => by simp⟩

theorem dvd_mulVec' {κ ι : Type} [Fintype ι] {q : A} (D : Matrix κ ι A) (h : ∀ i j, q ∣ D i j)
    (v : ι → A) (i : κ) : q ∣ (D *ᵥ v) i := by
  simp only [mulVec, dotProduct]
  exact Finset.dvd_sum fun j _ => dvd_mul_of_dvd_left (h i j) _

theorem img_succ_sub (Y : ∀ n, Matrix (Fin (d' n)) (Fin (d' (n + 1))) S)
    (h1 : ∀ n i j, (p : A) ^ n ∣ (R n * (Y n).map e - R (n + 1)) i j) {n m : ℕ} (hnm : n ≤ m) :
    Img e p R n (m + 1) ⊆ Img e p R n m := by
  rintro w ⟨s, hs⟩
  refine ⟨Y m *ᵥ s, fun i => ?_⟩
  have he : (fun j => e ((Y m *ᵥ s) j)) = (Y m).map e *ᵥ fun j => e (s j) := by
    funext j; exact RingHom.map_mulVec e (Y m) s j
  rw [he, mulVec_mulVec]
  have : (w - (R m * (Y m).map e) *ᵥ fun j => e (s j)) i =
      (w - R (m + 1) *ᵥ fun j => e (s j)) i -
        ((R m * (Y m).map e - R (m + 1)) *ᵥ fun j => e (s j)) i := by
    simp only [sub_mulVec, Pi.sub_apply]; ring
  rw [this]
  exact dvd_sub (hs i) ((pow_dvd_pow _ hnm).trans (dvd_mulVec' _ (h1 m) _ i))

theorem img_anti (Y : ∀ n, Matrix (Fin (d' n)) (Fin (d' (n + 1))) S)
    (h1 : ∀ n i j, (p : A) ^ n ∣ (R n * (Y n).map e - R (n + 1)) i j) {n m m' : ℕ} (hnm : n ≤ m)
    (hm : m ≤ m') : Img e p R n m' ⊆ Img e p R n m := by
  induction m', hm using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih => exact (img_succ_sub Y h1 (hnm.trans hk)).trans ih

theorem img_mod {k n m : ℕ} (hkn : k ≤ n) : Img e p R n m ⊆ Img e p R k m := by
  rintro w ⟨s, hs⟩; exact ⟨s, fun i => (pow_dvd_pow _ hkn).trans (hs i)⟩

theorem img_stable (u : S) (Y : ∀ n, Matrix (Fin (d' n)) (Fin (d' (n + 1))) S)
    (h1 : ∀ n i j, (p : A) ^ n ∣ (R n * (Y n).map e - R (n + 1)) i j)
    (n c : ℕ) [Finite (S ⧸ (Ideal.span {(p : S) ^ n} ⊔ Ideal.span {u ^ c}))]
    (hc : ∀ m, n ≤ m → ∀ s : Fin (d' n) → S, ∃ s' : Fin (d' m) → S, ∀ i,
      (p : A) ^ n ∣ ((R n *ᵥ fun j => e (u ^ c * s j)) - R m *ᵥ fun j => e (s' j)) i) :
    ∃ m₀, n ≤ m₀ ∧ ∀ m, m₀ ≤ m → Img e p R n m = Img e p R n m₀ := by
  let J : Ideal S := Ideal.span {(p : S) ^ n} ⊔ Ideal.span {u ^ c}
  let T : ℕ → Set (Fin (d' n) → S ⧸ J) := fun m =>
    {q | ∃ s : Fin (d' n) → S, (fun j => Ideal.Quotient.mk J (s j)) = q ∧
      (R n *ᵥ fun j => e (s j)) ∈ Img e p R n m}
  have key : ∀ m m', n ≤ m → n ≤ m' → T m ⊆ T m' → Img e p R n m ⊆ Img e p R n m' := by
    intro m m' hm hm' hT w hw
    obtain ⟨s, hs⟩ := img_anti Y h1 le_rfl hm hw
    have hRs : (R n *ᵥ fun j => e (s j)) ∈ Img e p R n m :=
      mem_of_dvd hw fun i => dvd_sub_comm.1 (hs i)
    obtain ⟨s', hq, hs'⟩ := hT ⟨s, rfl, hRs⟩
    have hj : ∀ j, ∃ a b : S, s j = s' j + (p : S) ^ n * a + u ^ c * b := by
      intro j
      have hqj : Ideal.Quotient.mk J (s' j) = Ideal.Quotient.mk J (s j) := congrFun hq j
      have hmem : s' j - s j ∈ J := Ideal.Quotient.eq.1 hqj
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hmem
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.1 hy
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.1 hz
      exact ⟨-a, -b, by linear_combination hyz⟩
    choose a b hab using hj
    obtain ⟨t, ht⟩ := hc m' hm' b
    have hsum : ((R n *ᵥ fun j => e (s' j)) + R n *ᵥ fun j => e (u ^ c * b j)) ∈ Img e p R n m' :=
      add_mem hs' (mem_of_dvd (image_mem n m' t) ht)
    have hRs' : (R n *ᵥ fun j => e (s j)) ∈ Img e p R n m' := by
      refine mem_of_dvd hsum fun i => ?_
      have hv : (fun j => e (s j)) = (fun j => e (s' j)) + (p : A) ^ n • (fun j => e (a j)) +
          fun j => e (u ^ c * b j) := by
        funext j; rw [hab j]; simp
      rw [hv, mulVec_add, mulVec_add, mulVec_smul]
      have : ((R n *ᵥ fun j => e (s' j)) + (p : A) ^ n • (R n *ᵥ fun j => e (a j)) +
          (R n *ᵥ fun j => e (u ^ c * b j)) - ((R n *ᵥ fun j => e (s' j)) +
            R n *ᵥ fun j => e (u ^ c * b j))) i = (p : A) ^ n * (R n *ᵥ fun j => e (a j)) i := by
        simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
      rw [this]; exact dvd_mul_right _ _
    exact mem_of_dvd hRs' hs
  have hanti : Antitone fun k => T (n + k) := by
    rintro k k' hkk q ⟨s, rfl, hs⟩
    exact ⟨s, rfl, img_anti Y h1 (Nat.le_add_right n k) (by omega) hs⟩
  obtain ⟨k₀, hk₀⟩ := WellFoundedLT.antitone_chain_condition hanti
  refine ⟨n + k₀, by omega, fun m hm => le_antisymm (img_anti Y h1 (by omega) hm) ?_⟩
  have hTe : T (n + k₀) = T m := by
    have := hk₀ (m - n) (by omega)
    rwa [Nat.add_sub_cancel' (by omega : n ≤ m)] at this
  exact key _ _ (by omega) (by omega) hTe.le

theorem ml (u : S) (Y : ∀ n, Matrix (Fin (d' n)) (Fin (d' (n + 1))) S)
    (h1 : ∀ n i j, (p : A) ^ n ∣ (R n * (Y n).map e - R (n + 1)) i j)
    (hfin : ∀ n c, Finite (S ⧸ (Ideal.span {(p : S) ^ n} ⊔ Ideal.span {u ^ c})))
    [IsAdicComplete (Ideal.span {(p : A)}) A]
    (h2 : ∀ n, ∃ c : ℕ, ∀ m, n ≤ m → ∀ s : Fin (d' n) → S, ∃ s' : Fin (d' m) → S, ∀ i,
      (p : A) ^ n ∣ ((R n *ᵥ fun j => e (u ^ c * s j)) - R m *ᵥ fun j => e (s' j)) i) :
    ∀ n, ∃ m, n ≤ m ∧ ∀ s : Fin (d' m) → S, ∃ v : Fin d → A,
      (∀ i, (p : A) ^ n ∣ (v - R m *ᵥ fun j => e (s j)) i) ∧
      ∀ k, ∃ s' : Fin (d' k) → S, ∀ i, (p : A) ^ k ∣ (v - R k *ᵥ fun j => e (s' j)) i := by
  have hst : ∀ n, ∃ m₀, n ≤ m₀ ∧ ∀ m, m₀ ≤ m → Img e p R n m = Img e p R n m₀ := fun n => by
    obtain ⟨c, hc⟩ := h2 n
    haveI := hfin n c
    exact img_stable u Y h1 n c hc
  choose m₀ hnm₀ hm₀ using hst
  have lift : ∀ n x, x ∈ Img e p R n (m₀ n) →
      ∃ y, y ∈ Img e p R (n + 1) (m₀ (n + 1)) ∧ ∀ i, (p : A) ^ n ∣ (y - x) i := by
    intro n x hx
    rw [← hm₀ n (max (m₀ n) (m₀ (n + 1))) (le_max_left _ _)] at hx
    obtain ⟨s, hs⟩ := hx
    refine ⟨_, ?_, fun i => dvd_sub_comm.1 (hs i)⟩
    rw [← hm₀ (n + 1) (max (m₀ n) (m₀ (n + 1))) (le_max_right _ _)]
    exact image_mem _ _ s
  choose! L hL hLd using lift
  intro n
  refine ⟨m₀ n, hnm₀ n, fun s => ?_⟩
  set x₀ := R (m₀ n) *ᵥ fun j => e (s j) with hx₀def
  have hx₀ : x₀ ∈ Img e p R n (m₀ n) := image_mem _ _ s
  let w : ℕ → Fin d → A := fun k => Nat.rec x₀ (fun k y => L (n + k) y) k
  have hw0 : w 0 = x₀ := rfl
  have hws : ∀ k, w (k + 1) = L (n + k) (w k) := fun _ => rfl
  have hmem : ∀ k, w k ∈ Img e p R (n + k) (m₀ (n + k)) := by
    intro k; induction k with
    | zero => exact hx₀
    | succ k ih => rw [hws]; exact hL _ _ ih
  have htel : ∀ k j i, (p : A) ^ (n + k) ∣ (w (k + j) - w k) i := by
    intro k j; induction j with
    | zero => intro i; simp
    | succ j ih =>
      intro i
      have : (w (k + (j + 1)) - w k) i = (w (k + j + 1) - w (k + j)) i + (w (k + j) - w k) i := by
        rw [← add_assoc]; simp only [Pi.sub_apply]; ring
      rw [this, hws]
      exact dvd_add ((pow_dvd_pow _ (by omega)).trans (hLd _ _ (hmem _) i)) (ih i)
  have hcau : ∀ i, ∃ v : A, ∀ k, (p : A) ^ k ∣ w k i - v := by
    intro i
    obtain ⟨v, hv⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete (Ideal.span {(p : A)}) A) (f := fun k => w k i) (by
      intro a b hab
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hab
      have h' : (p : A) ^ a ∣ w (a + j) i - w a i := (pow_dvd_pow _ (by omega)).trans (htel a j i)
      exact dvd_sub_comm.1 h')
    refine ⟨v, fun k => ?_⟩
    have := hv k
    rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] at this
  choose V hV using hcau
  refine ⟨V, fun i => ?_, fun k => ?_⟩
  · have h1' := htel 0 n i
    rw [Nat.add_zero, Nat.zero_add, hw0] at h1'
    have : (V - x₀) i = (V i - w n i) + (w n - x₀) i := by simp only [Pi.sub_apply]; ring
    rw [this]; exact dvd_add (dvd_sub_comm.1 (hV i n)) h1'
  · have hk : w k ∈ Img e p R k k :=
      img_anti Y h1 le_rfl (le_trans (by omega) (hnm₀ (n + k))) (img_mod (by omega) (hmem k))
    exact mem_of_dvd hk fun i => dvd_sub_comm.1 (hV i k)

end GlobalTheory.ImageTower

theorem GlobalTheory.ImageTower.perfectRing_Cb' (l : ℕ) [Fact l.Prime] : PerfectRing (Cb l) l := by
  refine PerfectRing.ofSurjective _ _ fun x => ?_
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := OCb l) x
  obtain ⟨a, rfl⟩ := (bijective_frobenius (OCb l) l).2 a
  obtain ⟨b, rfl⟩ := (bijective_frobenius (OCb l) l).2 b
  exact ⟨algebraMap _ _ a / algebraMap _ _ b, by simp [frobenius_def]⟩

theorem GlobalTheory.BKLim.mittagLeffler_image : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (d' : ℕ → ℕ) (R : ∀ n, Matrix (Fin d) (Fin (d' n)) (WCb l)) (Y : ∀ n, Matrix (Fin (d' n)) (Fin (d' (n + 1))) (bk.S)), (∀ n i j, (l : WCb l) ^ n ∣ (R n * (Y n).map bk.evW - R (n + 1)) i j) → (∀ n, ∃ c : ℕ, ∀ m, n ≤ m → ∀ s : Fin (d' n) → bk.S, ∃ s' : Fin (d' m) → bk.S, ∀ i, (l : WCb l) ^ n ∣ ((R n *ᵥ fun j => bk.evW (X ^ c * s j)) - R m *ᵥ fun j => bk.evW (s' j)) i) → ∀ n, ∃ m, n ≤ m ∧ ∀ s : Fin (d' m) → bk.S, ∃ v : Fin d → WCb l, (∀ i, (l : WCb l) ^ n ∣ (v - R m *ᵥ fun j => bk.evW (s j)) i) ∧ ∀ k, ∃ s' : Fin (d' k) → bk.S, ∀ i, (l : WCb l) ^ k ∣ (v - R k *ᵥ fun j => bk.evW (s' j)) i := by
  intro l _ K bk d d' R Y h1 h2
  haveI : PerfectRing (Cb l) l := GlobalTheory.ImageTower.perfectRing_Cb' l
  haveI : IsAdicComplete (Ideal.span {(l : WCb l)}) (WCb l) := WittVector.isAdicCompleteIdealSpanP
  exact GlobalTheory.ImageTower.ml (e := bk.evW) (p := l) (R := R) X Y h1 (fun n c => GlobalTheory.T.finite_breuilKisin_quotient_prime_pow_X_pow l K bk n c) h2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormInertiaPowPrimePowSubLe
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.InertiaMove

theorem fixed_apply {l : ℕ} [Fact l.Prime] {H : Subgroup (GQ l)} (hH : H.Normal) (σ : GQ l)
    {x : Om l} (hx : ∀ g ∈ H, g x = x) : ∀ g ∈ H, g (σ x) = σ x := by
  intro g hg
  have h := hx _ (hH.conj_mem' g hg σ)
  have h2 : σ ((σ⁻¹ * g * σ) x) = g (σ x) := by
    rw [← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply]
    congr 1
    group
  rw [← h2, h]

def fixedAdd {l : ℕ} [Fact l.Prime] (H : Subgroup (GQ l)) : AddSubgroup (Om l) where
  carrier := {x | ∀ g ∈ H, g x = x}
  add_mem' := fun {a b} ha hb g hg => by rw [map_add, ha g hg, hb g hg]
  zero_mem' := fun g _ => map_zero g
  neg_mem' := fun {a} ha g hg => by rw [map_neg, ha g hg]

theorem norm_natCast_le_one (l : ℕ) [Fact l.Prime] : ‖((l : ℕ) : Om l)‖ ≤ 1 :=
  IsUltrametricDist.norm_natCast_le_one _ _

theorem norm_pow_sub_le : ∀ (l : ℕ) [Fact l.Prime] (γ : GQ l), γ ∈ (MaximalUnramifiedExtension l).fixingSubgroup → ∀ (H : Subgroup (GQ l)), H.Normal → H.index ≠ 0 → ∀ m n : ℕ, H.index ≤ l ^ m → γ ^ l ^ n ∈ H → ∀ j ≤ m, ∀ x : Om l, (∀ g ∈ H, g x = x) → ‖(γ ^ l ^ j) x - x‖ ≤ ‖((l : ℕ) : Om l)‖ ^ ((1 : ℝ) / (l : ℝ) ^ (m - j)) * ‖x‖ := by
  intro l hl γ hγ H hH hi m n hm hn j
  have hτ0 : 0 ≤ ‖((l : ℕ) : Om l)‖ := norm_nonneg _
  have hτ1 := norm_natCast_le_one l
  have hl0 : l ≠ 0 := hl.out.ne_zero
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl.out.pos
  have hτpos : 0 < ‖((l : ℕ) : Om l)‖ := by
    rw [norm_pos_iff]
    exact_mod_cast hl0
  induction j with
  | zero =>
    intro _ x hx
    by_cases hx0 : x = 0
    · simp [hx0]
    have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
    have hlt := GlobalTheory.WildMove.norm_sub_lt l γ hγ n x hx0 (hx _ hn)
    set z : Om l := (γ x - x) / x with hz
    have hzfix : ∀ g ∈ H, g z = z := by
      intro g hg
      rw [hz, map_div₀, map_sub, fixed_apply hH γ hx g hg, hx g hg]
    have hzn : ‖z‖ = ‖γ x - x‖ / ‖x‖ := norm_div _ _
    have hz1 : ‖z‖ < 1 := by rw [hzn, div_lt_one hxpos]; exact hlt
    have hv := GlobalTheory.Per.norm_pow_index_le_of_fixed l H hi z hzfix hz1
    have h1 : ‖z‖ ^ (l ^ m) ≤ ‖((l : ℕ) : Om l)‖ :=
      (pow_le_pow_of_le_one (norm_nonneg _) hz1.le hm).trans hv
    have h2 : ‖z‖ ≤ ‖((l : ℕ) : Om l)‖ ^ ((1 : ℝ) / (l : ℝ) ^ m) := by
      have h3 := Real.rpow_le_rpow (by positivity) h1
        (show (0 : ℝ) ≤ ((l ^ m : ℕ) : ℝ)⁻¹ by positivity)
      rw [Real.pow_rpow_inv_natCast (norm_nonneg _) (pow_ne_zero _ hl0)] at h3
      rw [one_div]
      exact_mod_cast h3
    rw [hzn, div_le_iff₀ hxpos] at h2
    simpa using h2
  | succ j ih =>
    intro hj x hx
    have ih' := ih (by omega)
    obtain ⟨k, hk⟩ : ∃ k, m - j = k + 1 := ⟨m - j - 1, by omega⟩
    have hk' : m - (j + 1) = k := by omega
    rw [hk] at ih'
    rw [hk']
    set s : ℝ := ‖((l : ℕ) : Om l)‖ ^ ((1 : ℝ) / (l : ℝ) ^ (k + 1)) with hs
    have hs0 : 0 ≤ s := Real.rpow_nonneg hτ0 _
    have hs1 : s ≤ 1 := Real.rpow_le_one hτ0 hτ1 (by positivity)
    have h := (GlobalTheory.MemLoc.norm_geom_sum_galois_le l (γ ^ l ^ j) (fixedAdd H) s hs0 hs1
      (fun y hy => fixed_apply hH _ hy) (fun y hy => ih' y hy) x hx).2
    rw [← pow_mul, ← pow_succ] at h
    have hsl : s ^ l = ‖((l : ℕ) : Om l)‖ ^ ((1 : ℝ) / (l : ℝ) ^ k) := by
      rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hτ0]
      congr 1
      field_simp
      ring
    have hτs : ‖((l : ℕ) : Om l)‖ ≤ s ^ (l - 1) := by
      have h1 : s ^ l ≤ s ^ (l - 1) := pow_le_pow_of_le_one hs0 hs1 (by omega)
      refine le_trans ?_ h1
      rw [hsl]
      have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl.out.pos
      have h2 : (1 : ℝ) / (l : ℝ) ^ k ≤ 1 := by
        rw [div_le_one (by positivity)]
        exact one_le_pow₀ hl1
      have h3 := Real.rpow_le_rpow_of_exponent_ge hτpos hτ1 h2
      rwa [Real.rpow_one] at h3
    rw [max_eq_left hτs, ← pow_succ, Nat.sub_add_cancel hl.out.pos, hsl] at h
    exact h

end GlobalTheory.InertiaMove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicValNatPowSubOneLe
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules

namespace GlobalTheory.TypePrimeEta

theorem sum_two_mul_Icc (r : ℕ) : ∑ a ∈ Finset.Icc 1 r, 2 * a = r * (r + 1) := by
  induction r with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih]; ring

theorem padicValNat_pow_sub_one_le (g g' a : ℕ) (hg : g.Prime) (hg' : 2 ≤ g') (hgg : g' ≤ g ^ 2)
    (ha : 1 ≤ a) : padicValNat g (g' ^ a - 1) ≤ 2 * a := by
  haveI : Fact g.Prime := ⟨hg⟩
  have h1 : 1 < g' ^ a := Nat.one_lt_pow (by omega) (by omega)
  have hpos : 0 < g' ^ a - 1 := by omega
  have hle : g ^ padicValNat g (g' ^ a - 1) ≤ g' ^ a - 1 := Nat.le_of_dvd hpos pow_padicValNat_dvd
  have hlt : g ^ padicValNat g (g' ^ a - 1) < g ^ (2 * a) := by
    calc g ^ padicValNat g (g' ^ a - 1) ≤ g' ^ a - 1 := hle
      _ < g' ^ a := by omega
      _ ≤ (g ^ 2) ^ a := Nat.pow_le_pow_left hgg a
      _ = g ^ (2 * a) := by rw [← pow_mul]
  by_contra h
  have h := Nat.lt_of_not_le h
  have := Nat.pow_le_pow_right hg.pos h.le
  omega

theorem val_card_le (g g' r f : ℕ) (hg : g.Prime) (hg' : g'.Prime) (hne : g ≠ g')
    (hgg : g' ≤ g ^ 2) :
    padicValNat g (Nat.card (Matrix.GeneralLinearGroup (Fin r) (ZMod g)) ^ f *
      Nat.card (Matrix.GeneralLinearGroup (Fin r) (ZMod g')) ^ f) ≤ 2 * f * r ^ 2 := by
  haveI : Fact g.Prime := ⟨hg⟩
  haveI : Fact g'.Prime := ⟨hg'⟩
  have h0 : ∀ q : ℕ, [Fact q.Prime] → Nat.card (Matrix.GeneralLinearGroup (Fin r) (ZMod q)) ≠ 0 :=
    fun q _ => Nat.card_pos.ne'
  obtain ⟨h1, h2⟩ := Formalism.IrreducibleCountingLemmas.WindowSums.padicValCardGeneralLinear g g' r hne
  rw [padicValNat.mul (pow_ne_zero _ (h0 g)) (pow_ne_zero _ (h0 g')), padicValNat.pow,
    padicValNat.pow, h1, h2]
  have hs : ∑ a ∈ Finset.Icc 1 r, padicValNat g (g' ^ a - 1) ≤ r * (r + 1) := by
    rw [← sum_two_mul_Icc]
    exact Finset.sum_le_sum fun a ha =>
      padicValNat_pow_sub_one_le g g' a hg hg'.two_le hgg (Finset.mem_Icc.1 ha).1
  have hd : r * (r - 1) / 2 ≤ r * (r - 1) := Nat.div_le_self _ _
  have he : r * (r - 1) + r * (r + 1) = 2 * r ^ 2 := by
    cases r with
    | zero => simp
    | succ n => simp only [Nat.add_sub_cancel]; ring
  calc f * (r * (r - 1) / 2) + f * ∑ a ∈ Finset.Icc 1 r, padicValNat g (g' ^ a - 1)
      ≤ f * (r * (r - 1)) + f * (r * (r + 1)) :=
        Nat.add_le_add (Nat.mul_le_mul_left _ hd) (Nat.mul_le_mul_left _ hs)
    _ = 2 * f * r ^ 2 := by rw [← mul_add, he]; ring

theorem val_cardG0g_le (D : D7) (k k' : Fin 2) (hkk : k ≠ k')
    (hlog : Real.log (D.host.g k' : ℝ) ≤ 2 * Real.log (D.host.g k : ℝ)) :
    padicValNat (D.host.g k) D.what₂.restRowsFiniteGroupCard ≤ 2 * D.R.f * D.R.r ^ 2 := by
  have hg := D.host.g_prime k
  have hg' := D.host.g_prime k'
  have hgg : D.host.g k' ≤ D.host.g k ^ 2 := by
    have h1 : (0 : ℝ) < D.host.g k' := by exact_mod_cast hg'.pos
    have h0 : (0 : ℝ) < (D.host.g k : ℝ) ^ 2 := pow_pos (by exact_mod_cast hg.pos) 2
    have h2 : Real.log (D.host.g k' : ℝ) ≤ Real.log ((D.host.g k : ℝ) ^ 2) := by
      rw [Real.log_pow]; push_cast; linarith
    have := (Real.log_le_log_iff h1 h0).1 h2
    exact_mod_cast this
  have hk : (k = 0 ∧ k' = 1) ∨ (k = 1 ∧ k' = 0) := by
    fin_cases k <;> fin_cases k' <;> simp_all
  rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [D.nd.restN_card_levelGroup_eq, Fin.prod_univ_two]
    exact val_card_le _ _ _ _ hg hg' D.host.g_ne hgg
  · rw [D.nd.restN_card_levelGroup_eq, Fin.prod_univ_two, mul_comm]
    exact val_card_le _ _ _ _ hg hg' D.host.g_ne.symm hgg

theorem first_le (f r t CT N r' e n : ℕ) (C : ℝ) (hC : 8 * (CT : ℝ) ≤ C) (hN2 : 2 ≤ N)
    (hN : N ≤ n + 1) (hr4 : 4 * r' ≤ N ^ 2) (hn : r + t = n) :
    ((f * (2 * ((2 * r + t * 2) * (CT * (N * r' + (e + t + 1) * (N + r'))))) : ℕ) : ℝ) ≤
      4 * (f : ℝ) * n * (C * (n : ℝ) ^ 2 * ((n : ℝ) + e + t)) := by
  have hn1 : (1 : ℝ) ≤ n := by have : 1 ≤ n := by omega
                               exact_mod_cast this
  have hnR : (n : ℝ) = r + t := by rw [← hn]; push_cast; ring
  have a1 : (4 : ℝ) * r' ≤ (N : ℝ) ^ 2 := by exact_mod_cast hr4
  have a2 : (N : ℝ) ≤ 2 * n := by
    have : N ≤ 2 * n := by omega
    exact_mod_cast this
  have a0 : (0 : ℝ) ≤ N := by positivity
  have a3 : (N : ℝ) ^ 2 ≤ (2 * n) ^ 2 := pow_le_pow_left₀ a0 a2 2
  have hNr : 4 * ((N : ℝ) * r') ≤ 4 * (2 * (n : ℝ) ^ 3) := by
    calc 4 * ((N : ℝ) * r') = N * (4 * r') := by ring
      _ ≤ N * N ^ 2 := mul_le_mul_of_nonneg_left a1 a0
      _ = N ^ 3 := by ring
      _ ≤ (2 * n) ^ 3 := pow_le_pow_left₀ a0 a2 3
      _ = 4 * (2 * (n : ℝ) ^ 3) := by ring
  have hs : (N : ℝ) + r' ≤ 3 * (n : ℝ) ^ 2 := by nlinarith
  have he0 : (0 : ℝ) ≤ e := by positivity
  have ht0 : (0 : ℝ) ≤ t := by positivity
  have hr0 : (0 : ℝ) ≤ r' := by positivity
  have hm : ((e : ℝ) + t + 1) * (N + r') ≤ ((e : ℝ) + t + n) * (3 * (n : ℝ) ^ 2) :=
    mul_le_mul (by linarith) hs (by positivity) (by positivity)
  have hX : (N : ℝ) * r' + ((e : ℝ) + t + 1) * (N + r') ≤ 5 * ((n : ℝ) ^ 2 * ((n : ℝ) + e + t)) := by
    nlinarith [pow_nonneg (show (0:ℝ) ≤ n by linarith) 2]
  have hY : (0 : ℝ) ≤ (n : ℝ) ^ 2 * ((n : ℝ) + e + t) := by positivity
  have hCT : (0 : ℝ) ≤ CT := by positivity
  have hCX : (CT : ℝ) * ((N : ℝ) * r' + ((e : ℝ) + t + 1) * (N + r')) ≤
      C * ((n : ℝ) ^ 2 * ((n : ℝ) + e + t)) := by
    nlinarith [mul_le_mul_of_nonneg_left hX hCT, mul_le_mul_of_nonneg_right hC hY]
  calc ((f * (2 * ((2 * r + t * 2) * (CT * (N * r' + (e + t + 1) * (N + r'))))) : ℕ) : ℝ)
      = 4 * (f : ℝ) * n * ((CT : ℝ) * ((N : ℝ) * r' + ((e : ℝ) + t + 1) * (N + r'))) := by
        push_cast; rw [hnR]; ring
    _ ≤ 4 * (f : ℝ) * n * (C * ((n : ℝ) ^ 2 * ((n : ℝ) + e + t))) :=
        mul_le_mul_of_nonneg_left hCX (by positivity)
    _ = 4 * (f : ℝ) * n * (C * (n : ℝ) ^ 2 * ((n : ℝ) + e + t)) := by ring

end GlobalTheory.TypePrimeEta

namespace GlobalTheory

theorem typePrimeBound_of_etaBound : ∀ (D : D7) (C : ℝ) (CT : ℕ), 8 * (CT : ℝ) ≤ C →
    CongruenceAtTypePrimes (D := D) CT (EtaBound CT) → PairedCharacterCondition.aux₃ (D := D) C CT := by
  intro D C CT hC hQ i k k' hkk hl r ρ hr hadm eta s S sg U h1 h2 h3 h4 h5 h6 h7 h8
  obtain ⟨c, hη, hL⟩ := hQ i k k' hkk hl r ρ hr hadm eta s S sg U h1 h2 h3 h4 h5 h6 h7 h8
  have hv : (padicValNat (D.host.g k) D.what₂.restRowsFiniteGroupCard : ℝ) ≤ 2 * D.R.f * (D.R.r : ℝ) ^ 2 := by
    exact_mod_cast TypePrimeEta.val_cardG0g_le D k k' hkk h2
  have key : ∀ π ∈ D.nd.Zgood i,
      (c π : ℝ) + (padicValNat (D.host.g k) D.what₂.restRowsFiniteGroupCard : ℝ) ≤ rhs C eta i ρ π := by
    intro π hπ
    obtain ⟨N, r', hN2, hN, hr1, hr4, hc⟩ := hL π hπ
    have hA := TypePrimeEta.first_le D.R.f D.R.r D.R.t CT N r' eta D.R.nV C hC hN2 hN hr4 rfl
    unfold rhs eT
    linarith
  have hη' : (D.nd.etaLoc i : ℝ) ≤ ∑ π ∈ D.nd.Zgood i,
      (D.nd.mult i π : ℝ) * ((c π : ℝ) + (padicValNat (D.host.g k) D.what₂.restRowsFiniteGroupCard : ℝ)) := by
    exact_mod_cast hη
  exact hη'.trans (Finset.sum_le_sum fun π hπ => mul_le_mul_of_nonneg_left (key π hπ) (Nat.cast_nonneg _))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismHomMapIdealEq
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.Prism.Rigid

theorem φ_mem_of_mem {l : ℕ} (hl : 0 < l) {A : Type} [CommRing A] (D : Delta l A) {m : Ideal A}
    (hlm : (l : A) ∈ m) {x : A} (hx : x ∈ m) : D.φ x ∈ m := by
  rw [D.φ_eq]
  exact Ideal.add_mem _ (Ideal.pow_mem_of_mem _ hx _ hl) (Ideal.mul_mem_right _ _ hlm)

theorem φ_mem_sq {l : ℕ} (hl : 0 < l) {A : Type} [CommRing A] (D : Delta l A) {m : Ideal A}
    (hlm : (l : A) ∈ m) {x : A} (hx : x ∈ m ^ 2) : D.φ x ∈ m ^ 2 := by
  have h : (m ^ 2).map D.φ ≤ m ^ 2 := by
    rw [Ideal.map_pow, sq, sq]
    have hm : m.map D.φ ≤ m := Ideal.map_le_iff_le_comap.2 fun y hy => φ_mem_of_mem hl D hlm hy
    exact Ideal.mul_mono hm hm
  exact h (Ideal.mem_map_of_mem _ hx)

theorem map_I_eq (l : ℕ) [hl : Fact l.Prime] (R : Type) [CommRing R] (B B' : Obj l R) (f : Hom B B') :
    B.I.map f.f = B'.I := by
  have hl0 : 0 < l := hl.out.pos
  have hNI : B.I.map f.f ≤ B'.I := Ideal.map_le_iff_le_comap.2 fun a ha => f.f_I a ha
  refine GlobalTheory.T.eq_of_le_invertible_of_not_le_maximal_mul B'.A B'.I (B.I.map f.f) B'.inv hNI ?_
  intro m hm hN

  have hjac : Ideal.span {(l : B'.A)} ⊔ B'.I ≤ m := by
    haveI := B'.complete
    refine le_trans (IsAdicComplete.le_jacobson_bot (Ideal.span {(l : B'.A)} ⊔ B'.I)) ?_
    exact sInf_le ⟨bot_le, hm⟩
  have hlm : (l : B'.A) ∈ m := hjac (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))
  have hIm : B'.I ≤ m := le_trans le_sup_right hjac
  have hN2 : B.I.map f.f ≤ m ^ 2 := by
    rw [sq]; exact le_trans hN (Ideal.mul_mono_right hIm)

  have hmap : B.I ⊔ B.I.map B.D.φ ≤ (m ^ 2).comap f.f := by
    refine sup_le (fun a ha => hN2 (Ideal.mem_map_of_mem _ ha)) ?_
    refine Ideal.map_le_iff_le_comap.2 fun a ha => ?_
    show f.f (B.D.φ a) ∈ m ^ 2
    rw [f.f_φ]
    exact φ_mem_sq hl0 B'.D hlm (hN2 (Ideal.mem_map_of_mem _ ha))
  have hl2 : (l : B'.A) ∈ m ^ 2 := by
    have := hmap B.l_mem
    simpa [map_natCast] using this
  exact (GlobalTheory.T.prime_not_mem_sq_and_delta_not_mem l B'.A B'.D m hm.ne_top hlm).1 hl2

end GlobalTheory.Prism.Rigid
end
end

