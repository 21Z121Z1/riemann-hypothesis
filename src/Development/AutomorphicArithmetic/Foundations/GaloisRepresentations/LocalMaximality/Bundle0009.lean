import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ProjectiveLineTwo
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

namespace UpperTheory.Gal.productCup_of_system.ProjectiveLineTwo

variable {E : Type} [AddCommGroup E] [Module ℂ E]

private lemma mem_acxC {σ : Type} [LinearOrder σ] (A : Finset σ → Submodule ℂ E) (w : σ → Module.End ℂ E)
    (n : ℤ) (c : Finset σ → E) :
    c ∈ (acx A w).C n ↔ ∀ s, c s ∈ (if (s.card : ℤ) = n then A s else ⊥ : Submodule ℂ E) := by
  show c ∈ Submodule.pi Set.univ _ ↔ _
  simp only [Submodule.mem_pi, Set.mem_univ, true_implies]

private lemma val_zero {σ : Type} [LinearOrder σ] {A : Finset σ → Submodule ℂ E} {w : σ → Module.End ℂ E}
    {n : ℤ} {c : Finset σ → E} (h : c ∈ (acx A w).C n) (s : Finset σ) (hs : (s.card : ℤ) ≠ n) : c s = 0 := by
  have := (mem_acxC A w n c).1 h s
  rw [if_neg hs] at this
  simpa using this

private lemma val_mem {σ : Type} [LinearOrder σ] {A : Finset σ → Submodule ℂ E} {w : σ → Module.End ℂ E}
    {n : ℤ} {c : Finset σ → E} (h : c ∈ (acx A w).C n) (s : Finset σ) (hs : (s.card : ℤ) = n) : c s ∈ A s := by
  have := (mem_acxC A w n c).1 h s
  rwa [if_pos hs] at this

private lemma wd_apply' {σ : Type} [LinearOrder σ] (w : σ → Module.End ℂ E) (c : Finset σ → E) (t : Finset σ) :
    wd w c t = ∑ i ∈ t, (GlobalTheory.cubeSign t i : ℤ) • w i (c (t.erase i)) := by
  simp [wd, LinearMap.sum_apply]

private lemma wd_congr' {σ : Type} [LinearOrder σ] (w : σ → Module.End ℂ E) (c c' : Finset σ → E) (t : Finset σ)
    (h : ∀ i ∈ t, c (t.erase i) = c' (t.erase i)) : wd w c t = wd w c' t := by
  rw [wd_apply', wd_apply']
  exact Finset.sum_congr rfl fun i hi => by rw [h i hi]

private lemma wd_zero' {σ : Type} [LinearOrder σ] (c : Finset σ → E) (t : Finset σ) :
    wd (fun _ => (0 : Module.End ℂ E)) c t = 0 := by
  rw [wd_apply']
  simp

private lemma inter_card {β κ : Type} [LinearOrder β] [LinearOrder κ] [Fintype κ] (s : Finset (β ⊕ₗ κ)) :
    (s ∩ Finset.univ.map (inrE : κ ↪o β ⊕ₗ κ).toEmbedding).card = (rgt s).card := by
  have h : s ∩ Finset.univ.map (inrE : κ ↪o β ⊕ₗ κ).toEmbedding = (rgt s).map (inrE : κ ↪o β ⊕ₗ κ).toEmbedding := by
    ext t
    obtain ⟨t, rfl⟩ := toLex.surjective t
    rcases t with t | t <;> simp [rgt, inrE]
  rw [h, Finset.card_map]

end UpperTheory.Gal.productCup_of_system.ProjectiveLineTwo

open UpperTheory.Gal.productCup_of_system.ProjectiveLineTwo in
theorem UpperTheory.Gal.productCup_of_system.localTwo_of_gl2 :
    FiltrationCocycleLiftCriterion → ColQEx → WdUni → L2 := by
  intro hG hC hU β κ E _ _ _ _ _ _ A w d n hW hK c0 hZ hB
  classical
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = Finset.univ.map (inrE : κ ↪o β ⊕ₗ κ).toEmbedding := ⟨_, rfl⟩
  have hQex : QEx A w Q d := by rw [hQ]; exact hC β κ E A w d hK
  have hcap : ∀ s : Finset (β ⊕ₗ κ), (s ∩ Q).card = (rgt s).card := fun s => by rw [hQ]; exact inter_card s
  have hinl : ∀ i : β, (inlE i : β ⊕ₗ κ) ∉ Q := fun i => by simp [hQ, inlE, inrE]
  have hinr : ∀ l : κ, (inrE l : β ⊕ₗ κ) ∈ Q := fun l => by simp [hQ]
  have hl : ∀ (b : Finset β) (L : Finset κ), lft (uni b L) = b := fun b L => (hU β κ E w 0 b L).2.1
  have hr : ∀ (b : Finset β) (L : Finset κ), rgt (uni b L) = L := fun b L => (hU β κ E w 0 b L).2.2.1
  have hcd : ∀ (b : Finset β) (L : Finset κ), (uni b L).card = b.card + L.card :=
    fun b L => (hU β κ E w 0 b L).2.2.2.1
  have hs : ∀ s : Finset (β ⊕ₗ κ), uni (lft s) (rgt s) = s := (hU β κ E w 0 ∅ ∅).2.2.2.2
  have hsc : ∀ s : Finset (β ⊕ₗ κ), s.card = (lft s).card + (rgt s).card := fun s => by
    conv_lhs => rw [← hs s]
    exact hcd _ _
  have wdQ : ∀ (c : Finset (β ⊕ₗ κ) → E) (b : Finset β) (L : Finset κ), wd (wOn Q w) c (uni b L) =
      ((-1 : ℤ) ^ b.card) • wd (fun l => w (inrE l)) (fun L' => c (uni b L')) L := by
    intro c b L
    rw [(hU β κ E (wOn Q w) c b L).1]
    have h1 : (fun i => wOn Q w (inlE i)) = fun _ => (0 : Module.End ℂ E) := by
      funext i; simp [wOn, hinl]
    have h2 : (fun l => wOn Q w (inrE l)) = fun l => w (inrE l) := by
      funext l; simp [wOn, hinr]
    rw [h1, h2, wd_zero', zero_add]
  have wdQc : ∀ (c : Finset (β ⊕ₗ κ) → E) (b : Finset β) (L : Finset κ), wd (wOn Qᶜ w) c (uni b L) =
      wd (fun i => w (inlE i)) (fun b' => c (uni b' L)) b := by
    intro c b L
    rw [(hU β κ E (wOn Qᶜ w) c b L).1]
    have h1 : (fun i => wOn Qᶜ w (inlE i)) = fun i => w (inlE i) := by
      funext i; simp [wOn, hinl]
    have h2 : (fun l => wOn Qᶜ w (inrE l)) = fun _ => (0 : Module.End ℂ E) := by
      funext l; simp [wOn, hinr]
    rw [h1, h2, wd_zero', smul_zero, add_zero]
  have hc0 : ∀ (b : Finset β) (L : Finset κ), (b.card : ℤ) = n - d → (L.card : ℤ) ≠ d → c0 b L = 0 :=
    fun b L hb hL => val_zero (Submodule.mem_inf.1 (hZ b hb)).1 L hL
  have hc0m : ∀ (b : Finset β) (L : Finset κ), (b.card : ℤ) = n - d → (L.card : ℤ) = d → c0 b L ∈ A (uni b L) :=
    fun b L hb hL => val_mem (Submodule.mem_inf.1 (hZ b hb)).1 L hL
  let c' : Finset (β ⊕ₗ κ) → E := fun s => if ((lft s).card : ℤ) = n - d then c0 (lft s) (rgt s) else 0
  have hcu : ∀ (b : Finset β) (L : Finset κ), c' (uni b L) = if (b.card : ℤ) = n - d then c0 b L else 0 := by
    intro b L; simp only [c', hl, hr]
  have hc'C : c' ∈ (acx A w).C n := by
    rw [mem_acxC]
    intro s
    have hcs := hsc s
    by_cases hsn : (s.card : ℤ) = n
    · rw [if_pos hsn]
      simp only [c']
      split_ifs with hb
      · have := hc0m (lft s) (rgt s) hb (by omega)
        rwa [hs] at this
      · exact zero_mem _
    · rw [if_neg hsn]
      simp only [c']
      split_ifs with hb
      · rw [hc0 _ _ hb (by omega)]; exact zero_mem _
      · exact zero_mem _
  have hc'L : Lev Q (· = d) c' := by
    intro s hs'
    rw [hcap] at hs'
    simp only [c']
    split_ifs with hb
    · exact hc0 _ _ hb hs'
    · rfl
  have hQ0 : wd (wOn Q w) c' = 0 := by
    funext s
    obtain ⟨b, L, rfl⟩ : ∃ b L, s = uni b L := ⟨_, _, (hs s).symm⟩
    rw [wdQ]
    simp only [hcu]
    by_cases hb : (b.card : ℤ) = n - d
    · simp only [if_pos hb]
      have h0 : wd (fun l => w (inrE l)) (c0 b) = 0 := (Submodule.mem_inf.1 (hZ b hb)).2
      have h1 : (fun L' => c0 b L') = c0 b := rfl
      rw [h1, h0]; simp
    · simp only [if_neg hb]
      have h1 : (fun _ : Finset κ => (0 : E)) = 0 := rfl
      rw [h1, map_zero]; simp
  have hy : ∀ b : Finset β, ∃ y : Finset κ → E, (b.card : ℤ) = n - d + 1 →
      y ∈ (colA A w b).C (d - 1) ∧
        wd (fun l => w (inrE l)) y = fun L => wd (fun i => w (inlE i)) (fun b' => c0 b' L) b := by
    intro b
    by_cases hb : (b.card : ℤ) = n - d + 1
    · obtain ⟨y, hy1, hy2⟩ := hB b hb
      exact ⟨y, fun _ => ⟨hy1, hy2⟩⟩
    · exact ⟨0, fun h => absurd h hb⟩
  choose yb hyb using hy
  let y : Finset (β ⊕ₗ κ) → E := fun s =>
    if ((lft s).card : ℤ) = n - d + 1 then ((-1 : ℤ) ^ (lft s).card) • yb (lft s) (rgt s) else 0
  have hyu : ∀ (b : Finset β) (L : Finset κ), y (uni b L) =
      if (b.card : ℤ) = n - d + 1 then ((-1 : ℤ) ^ b.card) • yb b L else 0 := by
    intro b L; simp only [y, hl, hr]
  have hyz : ∀ (b : Finset β) (L : Finset κ), (b.card : ℤ) = n - d + 1 → (L.card : ℤ) ≠ d - 1 → yb b L = 0 :=
    fun b L hb hL => val_zero (hyb b hb).1 L hL
  have hym : ∀ (b : Finset β) (L : Finset κ), (b.card : ℤ) = n - d + 1 → (L.card : ℤ) = d - 1 →
      yb b L ∈ A (uni b L) := fun b L hb hL => val_mem (hyb b hb).1 L hL
  have hyC : y ∈ (acx A w).C n := by
    rw [mem_acxC]
    intro s
    have hcs := hsc s
    by_cases hsn : (s.card : ℤ) = n
    · rw [if_pos hsn]
      simp only [y]
      split_ifs with hb
      · have := hym (lft s) (rgt s) hb (by omega)
        rw [hs] at this
        exact (A s).smul_of_tower_mem _ this
      · exact zero_mem _
    · rw [if_neg hsn]
      simp only [y]
      split_ifs with hb
      · rw [hyz _ _ hb (by omega), smul_zero]; exact zero_mem _
      · exact zero_mem _
  have hyL : Lev Q (· = d - 1) y := by
    intro s hs'
    rw [hcap] at hs'
    simp only [y]
    split_ifs with hb
    · rw [hyz _ _ hb hs', smul_zero]
    · rfl
  have hyE : wd (wOn Q w) y = wd (wOn Qᶜ w) c' := by
    funext s
    obtain ⟨b, L, rfl⟩ : ∃ b L, s = uni b L := ⟨_, _, (hs s).symm⟩
    rw [wdQ, wdQc]
    by_cases hb : (b.card : ℤ) = n - d + 1
    · have h1 : (fun L' => y (uni b L')) = ((-1 : ℤ) ^ b.card) • yb b := by
        funext L'; rw [hyu, if_pos hb]; rfl
      rw [h1, map_zsmul, Pi.smul_apply, smul_smul, (hyb b hb).2, ← mul_pow]
      simp only [neg_mul, one_mul, neg_neg, one_pow, one_smul]
      refine wd_congr' _ _ _ _ fun i hi => ?_
      rw [hcu, if_pos]
      rw [Finset.card_erase_of_mem hi]
      have : 0 < b.card := Finset.card_pos.2 ⟨i, hi⟩
      omega
    · have h1 : (fun L' => y (uni b L')) = 0 := by
        funext L'; rw [hyu, if_neg hb]; rfl
      rw [h1, map_zero, Pi.zero_apply, smul_zero]
      symm
      have h2 : wd (fun i => w (inlE i)) (fun b' => c' (uni b' L)) b = wd (fun i => w (inlE i)) 0 b := by
        refine wd_congr' _ _ _ _ fun i hi => ?_
        rw [hcu, if_neg, Pi.zero_apply]
        rw [Finset.card_erase_of_mem hi]
        have : 0 < b.card := Finset.card_pos.2 ⟨i, hi⟩
        omega
      rw [h2, map_zero, Pi.zero_apply]
  obtain ⟨c, hcZ, hcl⟩ := hG (β ⊕ₗ κ) E A w Q d n hW hQex c' hc'C hc'L hQ0 ⟨y, hyC, hyL, hyE⟩
  have hcC : c ∈ (acx A w).C n := (Submodule.mem_inf.1 hcZ).1
  have hlev : ∀ (b : Finset β) (L : Finset κ), d ≤ (L.card : ℤ) → c (uni b L) = c' (uni b L) := by
    intro b L hL
    have := hcl (uni b L) (by
      intro h
      beta_reduce at h
      have h' : (((uni b L ∩ Q).card : ℕ) : ℤ) < d := by convert h
      rw [hcap, hr] at h'
      omega)
    exact sub_eq_zero.1 this
  refine ⟨c, hcZ, ?_, ?_⟩
  · intro b hb
    funext L
    show c (uni b L) = c0 b L
    by_cases hL : d ≤ (L.card : ℤ)
    · rw [hlev b L hL, hcu, if_pos hb]
    · rw [val_zero hcC _ (by rw [hcd]; push_cast; omega), hc0 b L hb (by omega)]
  · intro b L hL
    rw [hlev b L hL.le, hcu]
    split_ifs with hb
    · exact hc0 b L hb (by omega)
    · rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.WdUniImpliesMJ
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma wd_at {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E]
    (w : ι → Module.End ℂ E) (c : Finset ι → E) (t : Finset ι) :
    wd w c t = ∑ i ∈ t, (GlobalTheory.cubeSign t i : ℤ) • w i (c (t.erase i)) := by
  simp [wd, LinearMap.sum_apply]

private lemma wd_act {ι S E : Type} [LinearOrder ι] [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
    (act : S →ₐ[ℂ] Module.End ℂ E) (u : ι → S) (f : Finset ι → S) (m : E) (t : Finset ι) :
    wd (fun i => act (u i)) (fun t => act (f t) m) t =
      act (wd (fun i => Algebra.lmul ℂ S (u i)) f t) m := by
  rw [wd_at, wd_at, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [map_zsmul, Module.End.mul_apply]

private lemma wd_one {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E]
    (g : E →ₗ[ℂ] E) (b : Finset ι → E) (t : Finset ι) :
    wd (fun _ => (1 : Module.End ℂ E)) (fun t => g (b t)) t = g (deltaL ℂ ι E b t) := by
  rw [wd_at]
  change _ = g (∑ i ∈ t, GlobalTheory.cubeSign t i • b (t.erase i))
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [map_zsmul]

private lemma lft_uni' (h : WdUni) {β κ : Type} [LinearOrder β] [LinearOrder κ] (b : Finset β) (L : Finset κ) :
    lft (uni b L) = b := (h β κ ℂ (fun _ => 0) (fun _ => 0) b L).2.1

private lemma rgt_uni' (h : WdUni) {β κ : Type} [LinearOrder β] [LinearOrder κ] (b : Finset β) (L : Finset κ) :
    rgt (uni b L) = L := (h β κ ℂ (fun _ => 0) (fun _ => 0) b L).2.2.1

private lemma uni_lr (h : WdUni) {β κ : Type} [LinearOrder β] [LinearOrder κ] (s : Finset (β ⊕ₗ κ)) :
    uni (lft s) (rgt s) = s := (h β κ ℂ (fun _ => 0) (fun _ => 0) ∅ ∅).2.2.2.2 s

private lemma mj_uni (h : WdUni) {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
    (T : Sys d S E) {κ : Type} [LinearOrder κ] (p : ℕ) (θ : Finset (Fin (d + 1) ⊕ₗ κ) → S)
    (b : Finset (Fin (d + 1)) → E) (I J : Finset (Fin (d + 1))) (L : Finset κ) :
    T.mj p θ b (uni (uni I J) L) = T.act (θ (uni I L)) (((-1 : ℤ) ^ ((p + 1) * L.card)) • b J) := by
  simp only [Sys.mj, lft_uni' h, rgt_uni' h, map_zsmul]

theorem UpperTheory.Gal.productCup_of_system.mJ_of :
    WdUni → MJ := by
  intro h d S E _ _ _ _ T κ _ _ z p θ b hθ hb hJ
  funext s
  obtain ⟨I, J, L, rfl⟩ : ∃ I J L, s = uni (uni I J) L :=
    ⟨lft (lft s), rgt (lft s), rgt s, by rw [uni_lr h, uni_lr h]⟩
  have hw2 : ∀ l : κ, T.wt z (inrE l) = T.act (z l) := fun _ => rfl
  have hw3 : ∀ i : Fin (d + 1), T.wt z (inlE (inlE i)) = 1 := fun _ => rfl
  have hw4 : ∀ i : Fin (d + 1), T.wt z (inlE (inrE i)) = 1 := fun _ => rfl
  have e1 := (h (Two d) κ E (T.wt z) (T.mj p θ b) (uni I J) L).1
  have e2 := (h (Fin (d + 1)) (Fin (d + 1)) E (fun i => T.wt z (inlE i))
    (fun b' => T.mj p θ b (uni b' L)) I J).1
  have e3 := (h (Fin (d + 1)) κ S (fun t => Algebra.lmul ℂ S (app (fun _ => 1) z t)) θ I L).1
  rw [hθ] at e3
  have hcard : (uni I J).card = I.card + J.card := (h _ _ ℂ (fun _ => 0) (fun _ => 0) I J).2.2.2.1
  set P : S := wd (fun i => Algebra.lmul ℂ S (1 : S)) (fun b' => θ (uni b' L)) I with hP
  set Q : S := wd (fun l => Algebra.lmul ℂ S (z l)) (fun L' => θ (uni I L')) L with hQ
  have hPQ : P + ((-1 : ℤ) ^ I.card) • Q = 0 := e3.symm

  have tA : wd (fun i => T.wt z (inlE (inlE i))) (fun b' => T.mj p θ b (uni (uni b' J) L)) I =
      T.act P (((-1 : ℤ) ^ ((p + 1) * L.card)) • b J) := by
    rw [hP, ← wd_act]
    simp only [mj_uni h, hw3, map_one]

  have tB : wd (fun j => T.wt z (inlE (inrE j))) (fun J' => T.mj p θ b (uni (uni I J') L)) J = 0 := by
    have : (fun J' => T.mj p θ b (uni (uni I J') L)) = fun J' =>
        (((-1 : ℤ) ^ ((p + 1) * L.card)) • T.act (θ (uni I L))) (b J') := by
      funext J'
      simp only [mj_uni h, map_zsmul, LinearMap.smul_apply]
    simp only [this, hw4]
    rw [wd_one, hb]
    simp

  have tC : wd (fun l => T.wt z (inrE l)) (fun L' => T.mj p θ b (uni (uni I J) L')) L =
      T.act Q (((-1 : ℤ) ^ ((p + 1) * (L.card + 1))) • b J) := by
    rw [hQ, ← wd_act, wd_at, wd_at]
    refine Finset.sum_congr rfl fun l hl => ?_
    have hc : (L.erase l).card + 1 = L.card := Finset.card_erase_add_one hl
    have hs : ((-1 : ℤ) ^ ((p + 1) * (L.erase l).card)) = (-1 : ℤ) ^ ((p + 1) * (L.card + 1)) := by
      rw [← hc, show (p + 1) * ((L.erase l).card + 1 + 1) = (p + 1) * (L.erase l).card + 2 * (p + 1) by ring,
        pow_add, pow_mul]
      simp
    rw [mj_uni h, hs, hw2]
  have main : wd (T.wt z) (T.mj p θ b) (uni (uni I J) L) =
      T.act P (((-1 : ℤ) ^ ((p + 1) * L.card)) • b J) +
        ((-1 : ℤ) ^ (I.card + J.card)) • T.act Q (((-1 : ℤ) ^ ((p + 1) * (L.card + 1))) • b J) := by
    rw [e1, e2, hcard, tA, tB, tC]
    simp
  rw [main]
  change _ = (0 : E)
  by_cases hJc : J.card = p + 1
  · have hsgn : ((-1 : ℤ) ^ (I.card + J.card)) * ((-1 : ℤ) ^ ((p + 1) * (L.card + 1))) =
        ((-1 : ℤ) ^ I.card) * ((-1 : ℤ) ^ ((p + 1) * L.card)) := by
      rw [hJc, pow_add, show (p + 1) * (L.card + 1) = (p + 1) * L.card + (p + 1) by ring, pow_add]
      have : ((-1 : ℤ) ^ (p + 1)) * ((-1 : ℤ) ^ (p + 1)) = 1 := by
        rw [← mul_pow]; simp
      linear_combination ((-1 : ℤ) ^ I.card * (-1 : ℤ) ^ ((p + 1) * L.card)) * this
    have hPQ' : T.act P + ((-1 : ℤ) ^ I.card) • T.act Q = 0 := by
      rw [← map_zsmul, ← map_add, hPQ, map_zero]
    have := congrArg (fun f : Module.End ℂ E => f (((-1 : ℤ) ^ ((p + 1) * L.card)) • b J)) hPQ'
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.zero_apply] at this
    simp only [map_zsmul, smul_smul] at this ⊢
    rw [hsgn]
    simpa [smul_smul, mul_comm] using this
  · rw [hJ J hJc]
    simp
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.WeightInverseContinuity
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma card_img {κ : Type} [LinearOrder κ] {d : ℕ} (e : Fin d ↪o κ) : (img e).card = d := by
  simp [img]

private lemma detC_img {S κ : Type} [CommRing S] [LinearOrder κ] {d : ℕ} (ρ : κ → Fin d → S) (e : Fin d ↪o κ)
    (A : Matrix (Fin d) (Fin d) S) (hA : ∀ a, ρ (e a) = A a) : detC ρ (img e) = A.det := by
  have h := card_img e
  have hu : e = (img e).orderEmbOfFin h :=
    Finset.orderEmbOfFin_unique' h (fun x => by simp [img])
  rw [detC, dif_pos h]
  congr 1
  ext a b
  simp only [Matrix.of_apply]
  rw [← hu, hA]

private lemma detC_mem {S κ : Type} [CommRing S] [Algebra ℂ S] [LinearOrder κ] {d : ℕ} (R : Subalgebra ℂ S)
    (ρ : κ → Fin d → S) (h : ∀ l b, ρ l b ∈ R) (s : Finset κ) : detC ρ s ∈ R := by
  unfold detC
  split_ifs with hs
  · rw [Matrix.det_apply']
    exact R.sum_mem fun σ _ => R.mul_mem (intCast_mem R _) (R.prod_mem fun i _ => h _ _)
  · exact R.zero_mem

private lemma core (hDet : Det) (hK2 : KoszulBoundaryOfComponentMemIdeal) (hKS : KSub) (hWB : WdBasic)
    {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (act : S →ₐ[ℂ] Module.End ℂ E)
    {κ κ0 : Type} [LinearOrder κ] [Fintype κ] [LinearOrder κ0] [Fintype κ0]
    (R : Subalgebra ℂ S) (M : Submodule ℂ E) (r : κ → S) {d : ℕ} (ι : κ0 ↪o κ) (e0 e0' : Fin d ↪o κ0)
    (N : Matrix (Fin d) (Fin d) S) (ρ : κ0 → Fin d → S)
    (h1 : ∀ j, ρ (e0 j) = Pi.single j 1) (h2 : ∀ a, ρ (e0' a) = N a) (hρ : ∀ l b, ρ l b ∈ R)
    (hrel : ∀ l, r (ι l) = ∑ b, ρ l b * r (ι (e0 b)))
    (hSt : Stab act R M) (hr : ∀ l, r l ∈ R)
    (hKE : KE (kos act M fun j => r (ι (e0 j))) d) (c : Finset κ → E) (hc : c ∈ (kos act M r).Z d) :
    c ((img e0').map ι.toEmbedding) - act N.det (c ((img e0).map ι.toEmbedding)) ∈
      sm act M (Set.range fun j => r (ι (e0 j))) := by
  have hcC : ∀ s : Finset κ, c s ∈ (if (s.card : ℤ) = (d : ℤ) then M else ⊥) := fun s =>
    (Submodule.mem_inf.1 hc).1 s (Set.mem_univ _)
  have hcD : wd (fun l => act (r l)) c = 0 := (Submodule.mem_inf.1 hc).2
  obtain ⟨m, hm⟩ : ∃ m, m = c ((img e0).map ι.toEmbedding) := ⟨_, rfl⟩
  rw [← hm]
  have hmM : m ∈ M := by
    have := hcC ((img e0).map ι.toEmbedding)
    rw [if_pos (by simp [card_img])] at this
    rwa [hm]
  have hZ0 : (fun t : Finset κ0 => c (t.map ι.toEmbedding)) ∈ (kos act M fun l => r (ι l)).Z d := by
    refine Submodule.mem_inf.2 ⟨fun s _ => ?_, ?_⟩
    · have := hcC (s.map ι.toEmbedding)
      simpa using this
    · show wd (fun l => act (r (ι l))) (fun t : Finset κ0 => c (t.map ι.toEmbedding)) = 0
      funext s
      have := (hWB κ E (fun _ => M) (fun l => act (r l))).2.2.2.2.2 κ0 ι c s
      rw [this, hcD]; rfl
  have hZ' : (fun s : Finset κ0 => act (detC ρ s) m) ∈ (kos act M fun l => r (ι l)).Z d := by
    refine Submodule.mem_inf.2 ⟨fun s _ => ?_, ?_⟩
    · show act (detC ρ s) m ∈ (if (s.card : ℤ) = (d : ℤ) then M else ⊥)
      split_ifs with hs
      · exact hSt _ (detC_mem R ρ hρ s) m hmM
      · have : s.card ≠ d := fun h => hs (by rw [h])
        simp [detC, this]
    · show wd (fun l => act (r (ι l))) (fun s : Finset κ0 => act (detC ρ s) m) = 0
      have := hDet S E act κ0 d ρ (fun b => r (ι (e0 b))) m
      rwa [show (fun l => act (∑ b, ρ l b * r (ι (e0 b)))) = fun l => act (r (ι l)) from
        funext fun l => by rw [hrel l]] at this
  have hB := hK2 S E act κ0 R M (fun l => r (ι l)) d e0 hSt (fun l => hr _) hKE _
    (Submodule.sub_mem _ hZ0 hZ') (by
      have h1' : detC ρ (img e0) = 1 := by
        rw [detC_img ρ e0 1 (fun a => by rw [h1 a]; ext b; simp [Matrix.one_apply, Pi.single_apply, eq_comm])]
        simp
      simp only [Pi.sub_apply, h1', map_one, Module.End.one_apply, ← hm, sub_self]
      exact Submodule.zero_mem _)
  have hval := (hKS S E act κ0 R M (fun l => r (ι l)) hSt (fun l => hr _)).2 d _ hB (img e0')
  have hdet : detC ρ (img e0') = N.det := detC_img ρ e0' N h2
  simp only [Pi.sub_apply, hdet] at hval
  refine (?_ : sm act M (Set.range fun l => r (ι l)) ≤ sm act M (Set.range fun j => r (ι (e0 j)))) hval
  unfold sm
  refine iSup₂_le ?_
  rintro _ ⟨l, rfl⟩ _ ⟨x, hx, rfl⟩
  show act (r (ι l)) x ∈ _
  rw [hrel l, map_sum, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun b _ => ?_
  rw [mul_comm, map_mul, Module.End.mul_apply]
  exact (le_iSup₂_of_le (f := fun (t : S) (_ : t ∈ Set.range fun j => r (ι (e0 j))) => M.map (act t))
    (r (ι (e0 b))) ⟨b, rfl⟩ le_rfl) (Submodule.mem_map_of_mem (hSt _ (hρ l b) x hx))

theorem UpperTheory.Gal.productCup_of_system.koszulThree_of_det :
    Det → KoszulBoundaryOfComponentMemIdeal → KSub → WdBasic → K3 := by
  intro hDet hK2 hKS hWB S E _ _ _ _ act κ _ _ R M r d e e' N hSt hr hN hrel hdis hKE c hc
  classical
  have hmemL : ∀ j, e j ∈ img e ∪ img e' := fun j => Finset.mem_union_left _ (by simp [img])
  have hmemR : ∀ j, e' j ∈ img e ∪ img e' := fun j => Finset.mem_union_right _ (by simp [img])
  let ι : {l // l ∈ img e ∪ img e'} ↪o κ := OrderEmbedding.subtype _
  let e0 : Fin d ↪o {l // l ∈ img e ∪ img e'} :=
    OrderEmbedding.ofStrictMono (fun j => ⟨e j, hmemL j⟩) fun a b h => e.strictMono h
  let e0' : Fin d ↪o {l // l ∈ img e ∪ img e'} :=
    OrderEmbedding.ofStrictMono (fun j => ⟨e' j, hmemR j⟩) fun a b h => e'.strictMono h
  let ρ : {l // l ∈ img e ∪ img e'} → Fin d → S := fun l =>
    if h : ∃ j, e j = l.1 then Pi.single h.choose 1 else if h' : ∃ a, e' a = l.1 then N h'.choose else 0
  have h1 : ∀ j, ρ (e0 j) = Pi.single j 1 := fun j => by
    have hex : ∃ i, e i = (e0 j).1 := ⟨j, rfl⟩
    have : hex.choose = j := e.injective hex.choose_spec
    simp only [ρ]
    rw [dif_pos hex, this]
  have h2 : ∀ a, ρ (e0' a) = N a := fun a => by
    have hn : ¬ ∃ j, e j = (e0' a).1 := fun ⟨j, hj⟩ => hdis a j hj.symm
    have hex : ∃ i, e' i = (e0' a).1 := ⟨a, rfl⟩
    have : hex.choose = a := e'.injective hex.choose_spec
    simp only [ρ]
    rw [dif_neg hn, dif_pos hex, this]
  have hρ : ∀ l b, ρ l b ∈ R := fun l b => by
    simp only [ρ]
    split_ifs with h h'
    · rw [Pi.single_apply]
      split_ifs
      · exact R.one_mem
      · exact R.zero_mem
    · exact hN _ _
    · exact R.zero_mem
  have hrel' : ∀ l, r (ι l) = ∑ b, ρ l b * r (ι (e0 b)) := fun l => by
    obtain ⟨l, hl⟩ := l
    rcases Finset.mem_union.1 hl with h | h
    · obtain ⟨j, -, rfl⟩ := Finset.mem_map.1 h
      have := h1 j
      change r (e j) = ∑ b, ρ (e0 j) b * r (e b)
      rw [this]
      simp [Pi.single_apply]
    · obtain ⟨a, -, rfl⟩ := Finset.mem_map.1 h
      have := h2 a
      change r (e' a) = ∑ b, ρ (e0' a) b * r (e b)
      rw [this]
      exact hrel a
  have key := core hDet hK2 hKS hWB act R M r ι e0 e0' N ρ h1 h2 hρ hrel' hSt hr hKE c hc
  have hi : (img e0).map ι.toEmbedding = img e := by
    ext x; simp [img, ι, e0]
  have hi' : (img e0').map ι.toEmbedding = img e' := by
    ext x; simp [img, ι, e0']
  rw [hi, hi'] at key
  exact key
end

