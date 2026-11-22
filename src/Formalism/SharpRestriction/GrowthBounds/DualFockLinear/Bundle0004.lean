import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.DgFalseDiag
import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.ThAllMonomial
import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.Bundle0003

-- bundled from Formalism.SharpRestriction.GrowthBounds.DualFockLinear.Imports
section

end

-- bundled from Formalism.SharpRestriction.GrowthBounds.DualFockLinear.SubstSPtrue
section
noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.G.WittFrameLocaliserOrders MvPolynomial

section Inj

variable {n' r : ℕ} [NeZero n']

private theorem fr_lt_fr_of_lt {r : ℕ} (f : ℕ → ℤ) (h : ∀ i, i + 1 < r → f i < f (i + 1)) {a b : ℕ}
    (hab : a < b) (hb : b < r) : f a < f b := by
  induction b with
  | zero => omega
  | succ b ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hab with h1 | h1
    · exact lt_trans (ih h1 (by omega)) (h b (by omega))
    · subst h1
      exact h a (by omega)

private theorem fr_le_fr_of_le {r : ℕ} (f : ℕ → ℤ) (h : ∀ i, i + 1 < r → f i < f (i + 1)) {a b : ℕ}
    (hab : a ≤ b) (hb : b < r) : f a ≤ f b := by
  rcases hab.lt_or_eq with h1 | h1
  · exact (fr_lt_fr_of_lt f h h1 hb).le
  · rw [h1]

theorem fr_pos_inj {TT : Finset (Fin n')} {L₁ L₂ N₁ G' : ℕ} {F : Frames n' r} (hF : FramesOK TT L₁ L₂ N₁ G' F)
    (hG : G' ≤ n') (j : ℤ) : Function.Injective (fun l : Fin r => posOf n' (F.fr j l.val)) := by
  intro a b hab
  have hV := hF.2.1
  have ha := a.2
  have hb := b.2
  have hmono := hV.2.2.1 j
  have hprev : F.fr (j - 1) (r - 1) < F.fr j 0 := by
    have := hV.2.2.2.1 (j - 1)
    simpa using this
  have hprev0 : F.fr (j - 1) 0 ≤ F.fr (j - 1) (r - 1) :=
    fr_le_fr_of_le (F.fr (j - 1)) (hV.2.2.1 (j - 1)) (Nat.zero_le _) (by omega)
  have hwid := hF.2.2.1 j
  have hlo : ∀ l : Fin r, F.fr j 0 ≤ F.fr j l.val := fun l => fr_le_fr_of_le (F.fr j) hmono (Nat.zero_le _) l.2
  have hhi : ∀ l : Fin r, F.fr j l.val ≤ F.fr j (r - 1) := fun l => fr_le_fr_of_le (F.fr j) hmono (by omega) (by omega)
  have heq : F.fr j a.val = F.fr j b.val := by
    refine residue_position_injective_window n' (F.fr j 0) _ _ ⟨hlo a, ?_⟩ ⟨hlo b, ?_⟩ hab
    · have := hhi a
      omega
    · have := hhi b
      omega
  apply Fin.ext
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h1 | h1
  · exact absurd heq (ne_of_lt (fr_lt_fr_of_lt (F.fr j) hmono h1 b.2))
  · exact absurd heq (ne_of_gt (fr_lt_fr_of_lt (F.fr j) hmono h1 a.2))

private theorem emod_eq_of_posOf_eq (n' : ℕ) [NeZero n'] {x y : ℤ} (h : posOf n' x = posOf n' y) :
    x % n' = y % n' := by
  have hpos : (0:ℤ) < n' := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n')
  simp only [posOf, Fin.mk.injEq] at h
  have hx0 := Int.emod_nonneg x hpos.ne'
  have hx1 := Int.emod_lt_of_pos x hpos
  have hy0 := Int.emod_nonneg y hpos.ne'
  have hy1 := Int.emod_lt_of_pos y hpos
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h
  omega

private theorem posOf_sub_mul_eq_and_even_iff (n' : ℕ) [NeZero n'] (hn : Even n') (x q : ℤ) :
    posOf n' (x - n' * q) = posOf n' x ∧ (Even (x - n' * q) ↔ Even x) := by
  have hn' : Even (n' : ℤ) := by exact_mod_cast hn
  constructor
  · simp [posOf, Int.sub_emod]
  · simp [Int.even_sub, Int.even_mul, hn']

private theorem arow_lt_self_of_valid {n' r : ℕ} [NeZero n'] {F : Frames n' r} {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁)
    (hn : Even n') (hr : 1 ≤ r) (s : ℤ) (l : ℕ) (hl : l < r) : Arow F s l < s := by
  rw [symbolGeneratorData.dv_Arow_get hV hn hr s l hl]
  generalize_proofs hp
  have hm := List.getElem_mem hp
  simp only [evensBefore, List.mem_reverse, Finset.mem_sort, Finset.mem_filter, Finset.mem_Ico] at hm
  exact hm.1.2

theorem arow_pos_inj {TT : Finset (Fin n')} {L₁ L₂ N₁ G' : ℕ} {F : Frames n' r} (hF : FramesOK TT L₁ L₂ N₁ G' F)
    (hn : Even n') (hG : G' ≤ n') (s : ℤ) : Function.Injective (fun l : Fin r => posOf n' (Arow F s l.val)) := by
  rcases Nat.eq_zero_or_pos r with hr0 | hr0
  · subst hr0
    intro a
    exact a.elim0
  have hV := hF.2.1
  have h1 := fr_pos_inj hF hG 0
  have hpos : (0:ℤ) < n' := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n')
  have key : ∀ l l' : ℕ, l < l' → l' < r →
      posOf n' (Arow F s l) = posOf n' (Arow F s l') → False := by
    intro l l' hll hl' heq
    have hbc : Arow F s l' < Arow F s l := symbolGeneratorData.dv_Arow_anti hV hn hr0 s l l' hll hl'
    have hmod := emod_eq_of_posOf_eq n' heq
    have hdvd : (n' : ℤ) ∣ Arow F s l - Arow F s l' := Int.ModEq.dvd hmod.symm
    have hcb : (n' : ℤ) ≤ Arow F s l - Arow F s l' := Int.le_of_dvd (by omega) hdvd
    have hcs := arow_lt_self_of_valid hV hn hr0 s l (by omega)
    have hex : ∀ i : Fin r, ∃ m : Fin l', posOf n' (Arow F s m.val) = posOf n' (F.fr 0 i.val) := by
      intro i
      set b := Arow F s l'
      set x := F.fr 0 i.val
      have hq1 := Int.mul_ediv_add_emod (x - b - 1) n'
      have hq2 := Int.emod_nonneg (x - b - 1) hpos.ne'
      have hq3 := Int.emod_lt_of_pos (x - b - 1) hpos
      obtain ⟨hp1, hp2⟩ := posOf_sub_mul_eq_and_even_iff n' hn x ((x - b - 1) / n')
      have hTT := hV.2.2.2.2.1 0 i.val i.2
      have hlo : b < x - n' * ((x - b - 1) / n') := by
        generalize (n' : ℤ) * ((x - b - 1) / n') = m at hq1 ⊢
        generalize (x - b - 1) % (n' : ℤ) = e at hq1 hq2 hq3
        omega
      have hhi : x - n' * ((x - b - 1) / n') < s := by
        generalize (n' : ℤ) * ((x - b - 1) / n') = m at hq1 ⊢
        generalize (x - b - 1) % (n' : ℤ) = e at hq1 hq2 hq3
        omega
      obtain ⟨m, hm, hy⟩ := symbolGeneratorData.dv_Arow_newer hV hn hr0 s l' hl' (x - n' * ((x - b - 1) / n'))
        ⟨hp1 ▸ hTT.1, hp2.mpr hTT.2⟩ hhi hlo
      exact ⟨⟨m, hm⟩, by rw [← hy, hp1]⟩
    choose ψ hψ using hex
    have hinj : Function.Injective ψ := by
      intro i i' hii
      apply h1
      show posOf n' (F.fr 0 i.val) = posOf n' (F.fr 0 i'.val)
      rw [← hψ i, ← hψ i', hii]
    have := Fintype.card_le_of_injective ψ hinj
    simp at this
    omega
  intro a b hab
  apply Fin.ext
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h2 | h2
  · exact key a b h2 b.2 hab
  · exact key b a h2 a.2 hab.symm

end Inj

def SPR (R : Type) [CommRing R] (p : ℕ) {n' r k : ℕ} [NeZero n'] (F : Frames n' r) (hrk : r ≤ k) (c' Q : ℕ) :
    MvPolynomial (TV n' k) R :=
  (∏ j ∈ Finset.range F.J,
      (pmat R hrk (fun l => posOf n' (F.fr (j : ℤ) l.val)) (fun l => p ^ (zF F (j : ℤ) - F.fr (j : ℤ) l.val).toNat)).det ^
        alpha p F k (j : ℤ)) ^ c' *
    (∏ j ∈ Finset.range F.J,
      (pmat R hrk (fun l => posOf n' (F.fr (j : ℤ) l.val)) (fun l => p ^ (zF F (j : ℤ) - F.fr (j : ℤ) l.val).toNat)).det ^
        c') *
    ∏ s ∈ F.TT, (pmat R hrk (fun l => posOf n' (Arow F (s.val : ℤ) l.val))
      (fun l => p ^ ((s.val : ℤ) - Arow F (s.val : ℤ) l.val).toNat)).det ^ ((2 * Q + 3) * c' + k * Q)

theorem SPR_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (p : ℕ) {n' r k : ℕ} [NeZero n']
    (F : Frames n' r) (hrk : r ≤ k) (c' Q : ℕ) : map f (SPR R p F hrk c' Q) = SPR R' p F hrk c' Q := by
  unfold SPR
  simp only [map_mul, map_pow, map_prod, pmat_map]

theorem SPR_ne (R : Type) [CommRing R] [IsDomain R] (p : ℕ) (hp : p ≠ 0) {n' r k : ℕ} [NeZero n']
    {TT : Finset (Fin n')} {L₁ L₂ N₁ G' : ℕ} {F : Frames n' r} (hF : FramesOK TT L₁ L₂ N₁ G' F)
    (hn : Even n') (hG : G' ≤ n') (hrk : r ≤ k) (c' Q : ℕ) : SPR R p F hrk c' Q ≠ 0 := by
  unfold SPR
  refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ ?_) ?_) ?_
  · exact Finset.prod_ne_zero_iff.2 fun j _ =>
      pow_ne_zero _ (pmat_ne R hrk _ _ (fr_pos_inj hF hG _) fun l => pow_ne_zero _ hp)
  · exact Finset.prod_ne_zero_iff.2 fun j _ =>
      pow_ne_zero _ (pmat_ne R hrk _ _ (fr_pos_inj hF hG _) fun l => pow_ne_zero _ hp)
  · exact Finset.prod_ne_zero_iff.2 fun s _ =>
      pow_ne_zero _ (pmat_ne R hrk _ _ (arow_pos_inj hF hn hG _) fun l => pow_ne_zero _ hp)

theorem subst_SPtrue {p n' : ℕ} [Fact p.Prime] [NeZero n'] {O : Type} [CommRing O] [IsDomain O] [Algebra (WF p n') O]
    {r k : ℕ} (w : O) (F : Frames n' r) {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (hn : Even n') (hr : 1 ≤ r) (hrk : r ≤ k)
    {g : Matrix (Fin k) (Fin k) (WF p n')} (hg : IsGLW g) (c' Q : ℕ) :
    subst p n' O w n' r g (SPtrue p n' O F hrk g c' Q) = map (algebraMap O (KK O)) (SPR O p F hrk c' Q) := by
  unfold SPtrue SPR R0 DtopProd
  simp only [map_mul, map_pow, map_prod, subst_Del w F hV hn hrk hg, subst_Dtop' w F hV hn hr hrk hg]

theorem spStep (C : ℝ) : SPStep C := by
  intro p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ hφ hrk F hF
    g hg
  letI : Algebra (WF p n') O := algOfIdent j φ
  intro c' Q
  have hn : Even n' := hSet.1.even
  have hr : 1 ≤ r := by have := H.2.1; omega
  have hG : goodG' r de h x ≤ n' := by have := H.2.2.1.2.2.2; omega
  refine ⟨SPR O p F hrk c' Q, subst_SPtrue w F hF.2.1 hn hr hrk hg c' Q, ?_⟩
  rw [SPR_map]
  exact SPR_ne _ p (Fact.out : p.Prime).ne_zero hF hn hG hrk c' Q

private theorem weight_single_eq_multideg {n' k : ℕ} (m : Fin n' × Fin k →₀ ℕ) :
    Finsupp.weight (fun v : Fin n' × Fin k => (Pi.single v.1 1 : Fin n' → ℕ)) m = fun i => multideg m i := by
  funext i
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp [multideg, Finset.sum_apply, Pi.single_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp

private theorem mem_Pol_iff_isWeightedHomogeneous {R : Type} [CommRing R] {n' k : ℕ} (d : Fin n' → ℕ)
    (F : MvPolynomial (Fin n' × Fin k) R) :
    F ∈ Pol R k d ↔ IsWeightedHomogeneous (fun v : Fin n' × Fin k => (Pi.single v.1 1 : Fin n' → ℕ)) F d := by
  simp only [Pol, mem_restrictSupport_iff, IsWeightedHomogeneous, weight_single_eq_multideg]
  constructor
  · intro h m hm
    funext i
    exact h (mem_support_iff.mpr hm) i
  · intro h m hm i
    exact congrFun (h (mem_support_iff.mp hm)) i

private theorem isWeightedHomogeneous_aeval_of_homogeneous {σ K M : Type} [CommRing K] [AddCommMonoid M] (w : σ → M)
    (f : σ → MvPolynomial σ K) (hf : ∀ v, IsWeightedHomogeneous w (f v) (w v)) {P : MvPolynomial σ K} {e : M}
    (hP : IsWeightedHomogeneous w P e) : IsWeightedHomogeneous w (aeval f P) e := by
  classical
  rw [P.as_sum, map_sum]
  apply IsWeightedHomogeneous.sum
  intro m hm
  rw [aeval_monomial, MvPolynomial.algebraMap_eq]
  apply IsWeightedHomogeneous.C_mul
  have hme : Finsupp.weight w m = e := hP (mem_support_iff.mp hm)
  rw [← hme, Finsupp.weight_apply]
  exact IsWeightedHomogeneous.prod _ _ _ fun v _ => (hf v).pow _

theorem substPol : SubstPol := by
  intro p n' _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w hS φ hφ k r d g hg F hF
  rw [mem_Pol_iff_isWeightedHomogeneous] at hF ⊢
  simp only [subst, liftSubst]
  refine isWeightedHomogeneous_aeval_of_homogeneous _ _ ?_ hF
  intro v
  have hX : ∀ b : Fin k, IsWeightedHomogeneous (fun v : Fin n' × Fin k => (Pi.single v.1 1 : Fin n' → ℕ))
      (X (v.1, b) : MvPolynomial (TV n' k) (KK O)) (Pi.single v.1 1) :=
    fun b => isWeightedHomogeneous_X (KK O) _ (v.1, b)
  have hmC : ∀ {P : MvPolynomial (TV n' k) (KK O)} (c : KK O),
      IsWeightedHomogeneous (fun v : Fin n' × Fin k => (Pi.single v.1 1 : Fin n' → ℕ)) P (Pi.single v.1 1) →
      IsWeightedHomogeneous (fun v : Fin n' × Fin k => (Pi.single v.1 1 : Fin n' → ℕ)) (P * C c)
        (Pi.single v.1 1) := by
    intro P c hP
    simpa using hP.mul (isWeightedHomogeneous_C _ c)
  split_ifs
  · apply IsWeightedHomogeneous.sum
    intro b _
    apply hmC
    split_ifs
    · exact (hX b).C_mul _
    · exact hX b
  · apply IsWeightedHomogeneous.sum
    intro b _
    apply hmC
    split_ifs
    · exact (hX b).C_mul _
    · exact hX b

end Formalism.MainNotions.TestSideCounting
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.DualFockLinear.TransStep
section
noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 MvPolynomial
open Formalism.L2.G.Model
open Formalism.MainNotions.G.LatticeSystems (la_tw lb_D la_tw_det lb_D_det H0_eq_twisted_nabla la_indep)

section

variable {p n' : ℕ} [Fact p.Prime] {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}

theorem tr_theta (hS : HidaSetting p n' W Qq O Kf ι σ j w) (φ : WF p n' ≃+* W) (hφ : IsWittIdent σ φ) (m r : ℕ)
    (hm : 1 ≤ m) (d : Fin n' → ℕ) (hmat : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hh : IsUnit hmat.det)
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')) (hg : IsGLW g)
    (P : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) (hP : P ∈ Pol (KK O) (m + 1) d)
    (Q : MvPolynomial (Fin n' × Fin (m + 1)) O) :
    letI : Algebra (WF p n') O := algOfIdent j φ
    subst p n' O w n' r g P = map (algebraMap O (KK O)) Q →
    (algebraMap O Kf w ^ (Avec (vecE n') d)) •
      ((∏ s, (Mx ι σ w φ r (fun x : Fin n' => x) hmat g s).det ^ (letterWt m (d s) (vecE n' s) (Fin.last m))) •
        blockAct Kf (Mx ι σ w φ r (fun x : Fin n' => x) hmat g)
          (thF hS m (vecE n') (fun x => la_tw ι σ x.val hmat) P)) =
      map (algebraMap O Kf) (Th0 O m (vecE n') Q) := by
  letI : Algebra (WF p n') O := algOfIdent j φ
  intro hPQ
  have hw := w_ne hS
  set c := algebraMap O Kf w with hc
  have hP' := (pol_iff hS _ _ _).1 hP
  have hM := Mx_det (ι := ι) (σ := σ) hw φ r (fun x : Fin n' => x) hmat hh g hg
  unfold thF
  rw [tr_multi_twist Kf m hm (vecE n') d _ hM _ (Lin_Pol _ _ hP'), Lin_comp]
  have h1 := lift_eq hS φ hφ r (LLT n') (fun x : Fin n' => x) (fun _ => rfl) g hg P
  have hB : Bm ι σ w φ r (LLT n').vec (fun x : Fin n' => x) g = fun x => (if (LLT n').vec x then c else 1) •
      (Aa ((LLT n').vec x) (la_tw ι σ x.val hmat)⁻¹ *
        Aa ((LLT n').vec x) (Mx ι σ w φ r (fun x : Fin n' => x) hmat g x)) :=
    funext fun x => Bm_eq hw φ r (LLT n').vec (fun x : Fin n' => x) hmat hh g hg x
  rw [hB, Lin_smul _ _ _ hP'] at h1
  have hprod : ∏ x, (if (LLT n').vec x then c else 1) ^ d x = c ^ Avec (vecE n') d := by
    unfold Avec
    rw [← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_congr rfl
    intro x _
    show (if vecE n' x then c else 1) ^ d x = _
    split_ifs <;> simp
  rw [hprod] at h1
  have h2 : map (kapR hS) (liftSubst p n' O w r (LLT n') g P) = map (algebraMap O Kf) Q := by
    have : liftSubst p n' O w r (LLT n') g P = map (algebraMap O (KK O)) Q := hPQ
    rw [this, map_map]
    have hk : (kapR hS).comp (algebraMap O (KK O)) = algebraMap O Kf := RingHom.ext fun x => kapR_alg hS x
    rw [hk]
  rw [map_letter_substitution, ← h2, h1, map_smul]
  rfl

end

theorem transStep : TransStep := by
  intro p n' _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w hS φ hφ m r hm hr1 hr2 d rest lam0 hlam hrest e he hmat g hh hg hbasis
  letI : Algebra (WF p n') O := algOfIdent j φ
  intro Θ hΘ I _ sO hsO
  have hfrac := hS.frac_O
  have hinj : Function.Injective (algebraMap O Kf) := IsFractionRing.injective O Kf
  have hw := w_ne hS
  set c := algebraMap O Kf w with hc
  set M : Fin n' → Matrix (Fin (m + 1)) (Fin (m + 1)) Kf := Mx ι σ w φ r (fun x : Fin n' => x) hmat g with hMdef
  have hM : ∀ s, IsUnit (M s).det := Mx_det hw φ r _ hmat hh g hg
  have hH : ∀ lam : Fin n' → Fin (m + 1) → ℤ, IsDominant lam →
      Hten O lam (fun s => LeAt p ι σ w s.val e) = tensorLat O Kf (fun s => nablaLTw O Kf m (lamAt lam s) (M s)) := by
    intro lam hl
    unfold Hten
    congr 1
    funext s
    show H0 O m _ (LeAt p ι σ w s.val e) = _
    rw [(edgeLat_of hS m r e _ hbasis).2.1]
    show H0 O m _ (colSpan O (M s)) = _
    rw [H0_eq_twisted_nabla (la_indep hinj) _ _ (lamAt_antitone' lam hl s) _ (hM s)]
  have hV : ∀ lam : Fin n' → Fin (m + 1) → ℤ, IsDominant lam →
      Vsp Kf lam = tensorLat Kf Kf (fun s => dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt lam s))) := by
    intro lam hl
    unfold Vsp
    congr 1
    funext s
    rw [if_pos (lamAt_antitone' lam hl s)]
  have hfl : IsDominant (flW (m := m) d) := flW_dom d
  have hl0 : IsDominant lam0 := by rw [hlam]; exact isDominant_add hfl hrest
  let dt : (Fin n' → Fin (m + 1) → ℤ) → Kf := fun lam => ∏ s, (M s).det ^ (lamAt lam s (Fin.last m))
  have hdt : dt lam0 = dt (flW d) * dt rest := by
    show ∏ s, _ = (∏ s, _) * ∏ s, _
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [hlam, lamAt_add, Pi.add_apply, zpow_add₀ (hM s).ne_zero]
  have hAr : Ar r lam0 = Ar r (flW (m := m) d) + Ar r rest := by rw [hlam, Ar_add]
  have h1 := fun i => tr_tens_lift O Kf m (fun s => lamAt rest s) M hM (sO i) (hsO i)
  choose y hy1 hy2 using h1
  have hyV : ∀ i, y i ∈ Vsp Kf rest := by
    intro i
    rw [hV rest hrest]
    exact tr_tens_le O Kf m _ M hM _ (hy1 i)
  refine ⟨fun i => c ^ (-Ar r rest) • (⟨y i, hyV i⟩ : Vsp Kf rest), ?_, ?_⟩
  · intro i
    refine ⟨⟨y i, hyV i⟩, ?_, rfl⟩
    show y i ∈ Hten O rest (fun s => LeAt p ι σ w s.val e)
    rw [hH rest hrest]
    exact hy1 i
  · intro P Q hPQ v hv hvmem
    obtain ⟨y0, hy0, hvy⟩ := (mem_scale2 (O := O) (Vsp Kf lam0) (Hten O lam0 fun s => LeAt p ι σ w s.val e)
      (c ^ (1 : ℤ)) (c ^ (-Ar r lam0)) (zpow_ne_zero _ hw) (zpow_ne_zero _ hw) v).1 hvmem
    rw [hH lam0 hl0] at hy0
    obtain ⟨R0, hR0⟩ := tr_tens_int O Kf m (fun s => lamAt lam0 s) M hM y0 hy0
    refine ⟨R0, ?_⟩
    apply map_injective _ hinj
    have way1 : (c ^ (Ar r lam0) * dt lam0) • blockAct Kf M (v : MvPolynomial _ Kf) =
        map (algebraMap O Kf) (C w * R0) := by
      rw [hvy, map_smul, smul_smul, map_mul, map_C, ← hR0, ← smul_eq_C_mul, smul_smul]
      congr 1
      have hcc : c ^ Ar r lam0 * c ^ (-Ar r lam0) = 1 := by rw [← zpow_add₀ hw, add_neg_cancel, zpow_zero]
      show c ^ Ar r lam0 * dt lam0 * (c ^ (1 : ℤ) * c ^ (-Ar r lam0)) = c * dt lam0
      rw [zpow_one]
      linear_combination (dt lam0 * c) * hcc
    have hA : Ar r (flW (m := m) d) = (Avec (vecE n') d : ℤ) :=
      flat_Ar r hr1 hr2 (vecE n') d (flW d) (isFlat_flW d)
    have hdfl : dt (flW d) = ∏ s, (M s).det ^ (letterWt m (d s) (vecE n' s) (Fin.last m)) := by
      refine Finset.prod_congr rfl fun s _ => ?_
      rw [flat_lam (vecE n') d (flW d) (isFlat_flW d) s]
    have way2 : (c ^ (Ar r lam0) * dt lam0) • blockAct Kf M (v : MvPolynomial _ Kf) =
        map (algebraMap O Kf) (∑ i, thAll O n' m (vecE n') (Q i) * sO i) := by
      rw [hv, map_sum, map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have t1 := tr_theta hS φ hφ m r (by omega) d hmat hh g hg (P i).1 (P i).2 (Q i) (hPQ i)
      rw [map_mul, map_mul, ← hy2 i]
      have e1 : map (algebraMap O Kf) (thAll O n' m (vecE n') (Q i)) = map (algebraMap O Kf) (Th0 O m (vecE n') (Q i)) :=
        rfl
      rw [e1, ← t1, hΘ (P i), hAr, hdt, hdfl, hA, zpow_add₀ hw, zpow_natCast]
      show _ • (_ * blockAct Kf M (c ^ (-Ar r rest) • y i)) = _
      rw [map_smul]
      simp only [smul_eq_C_mul, map_mul, map_pow]
      have hcc : (C (c ^ Ar r rest) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) * C (c ^ (-Ar r rest)) = 1 := by
        rw [← C_mul, ← zpow_add₀ hw, add_neg_cancel, zpow_zero, C_1]
      linear_combination (C c ^ Avec (vecE n') d * C (∏ s, (M s).det ^ (letterWt m (d s) (vecE n' s) (Fin.last m))) *
        C (dt rest) * blockAct Kf M (thF hS m (vecE n') (fun x => la_tw ι σ x.val hmat) (P i).1) *
        blockAct Kf M (y i)) * hcc
    rw [← way2, way1]

end Formalism.MainNotions.TestSideCounting
end
end

