import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0009

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.CoordinateSystemDegreeOneOfUniversalDerivation
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma acx_eq_zero {σ E : Type} [LinearOrder σ] [AddCommGroup E] [Module ℂ E]
    (A : Finset σ → Submodule ℂ E) (w : σ → Module.End ℂ E) (n : ℤ) (c : Finset σ → E)
    (hc : c ∈ (acx A w).C n) (s : Finset σ) (hs : A s = ⊥) : c s = 0 := by
  have h : c s ∈ (if (s.card : ℤ) = n then A s else ⊥) :=
    Submodule.mem_pi.1 (show c ∈ Submodule.pi Set.univ
      (fun s : Finset σ => if (s.card : ℤ) = n then A s else ⊥) from hc) s (Set.mem_univ _)
  rw [hs, ite_self, Submodule.mem_bot] at h
  exact h

theorem UpperTheory.Gal.productCup_of_system.coordinateSystem_degree_one_of_universalDerivation :
    L1 → SysOk → WdUni → CechKoszulSystemBoundaryCriterion := by
  intro hL hOk hU
  intro d S E _ _ _ _ T κ _ _ n z N hG hAdm hKE c hc hbig hcol
  obtain ⟨hW, -, -⟩ := hOk d S E T κ n z hG hAdm
  set A : Finset (Two d ⊕ₗ κ) → Submodule ℂ E := fun s => mixF (fun I J =>
    Submodule.map (T.act ↑(∏ l ∈ rgt s, T.u n (pk I) (pk J) l)) (T.M I J)) (lft s) with hA
  have hu := fun (b : Finset (Two d)) (L : Finset κ) => hU (Two d) κ E (T.wt z) (fun _ => 0) b L
  have hcolA : ∀ b : Finset (Two d), (lft b).Nonempty → (rgt b).Nonempty →
      colA A (T.wt z) b = T.colCx n z (lft b) (rgt b) := by
    intro b h1 h2
    simp only [colA, Sys.colCx, kosT]
    congr 1
    funext L
    simp only [hA, (hu b L).2.1, (hu b L).2.2.1, mixF, if_pos (And.intro h1 h2)]
  have hbot : ∀ b : Finset (Two d), ¬ ((lft b).Nonempty ∧ (rgt b).Nonempty) → ∀ L, A (uni b L) = ⊥ := by
    intro b h L
    simp only [hA, (hu b L).2.1, mixF, if_neg h]
  have hcC : c ∈ (acx A (T.wt z)).C N := hc.1
  refine hL (Two d) κ E A (T.wt z) (d : ℤ) N hW ?_ c hc ?_ ?_
  · intro b
    by_cases h : (lft b).Nonempty ∧ (rgt b).Nonempty
    · rw [hcolA b h.1 h.2]
      exact hKE _ _ h.1 h.2
    · intro m _ x hx
      have hx1 : x ∈ (colA A (T.wt z) b).C m := hx.1
      have hx0 : x = 0 := funext fun L =>
        acx_eq_zero (fun L => A (uni b L)) (fun l => T.wt z (inrE l)) m x hx1 L (hbot b h L)
      rw [hx0]
      exact Submodule.zero_mem _
  · intro b L hlt
    exact hbig b L (by exact_mod_cast hlt)
  · intro b hb
    by_cases h : (lft b).Nonempty ∧ (rgt b).Nonempty
    · rw [hcolA b h.1 h.2]
      have hU2 := hU (Fin (d + 1)) (Fin (d + 1)) E (fun _ => 0) (fun _ => 0) (lft b) (rgt b)
      have hs : uni (lft b) (rgt b) = b := hU2.2.2.2.2 b
      have := hcol (lft b) (rgt b) h.1 h.2 (by rw [← hb, ← hU2.2.2.2.1, hs])
      rw [hs] at this
      exact this
    · have h0 : col c b = 0 := funext fun L => acx_eq_zero A (T.wt z) N c hcC (uni b L) (hbot b h L)
      rw [h0]
      exact Submodule.zero_mem _
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.CoordinateSystemDegreeTwoOfUniversalDerivation
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private theorem wd_single' {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E]
    (w : ι → Module.End ℂ E) (f : Finset ι → E) (i : ι) : wd w f {i} = w i (f ∅) := by
  have s1 : GlobalTheory.cubeSign ({i} : Finset ι) i = 1 := GlobalTheory.cubeSign_singleton i
  simp [wd, s1]

private theorem wd_pair' {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E]
    (w : ι → Module.End ℂ E) (f : Finset ι → E) {i i' : ι} (h : i < i') :
    wd w f {i, i'} = w i (f {i'}) - w i' (f {i}) := by
  have hne : i ≠ i' := ne_of_lt h
  have s1 : GlobalTheory.cubeSign {i, i'} i = 1 := by
    apply GlobalTheory.cubeSign_eq_one_of_forall_le
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact le_rfl
    · rw [Finset.mem_singleton.mp hj]; exact le_of_lt h
  have s2 : GlobalTheory.cubeSign {i, i'} i' = -1 := by
    have : ({x ∈ ({i, i'} : Finset _) | x < i'}) = {i} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl, hx⟩
        · rfl
        · exact absurd hx (lt_irrefl _)
      · rintro rfl; exact ⟨Or.inl rfl, h⟩
    simp [GlobalTheory.cubeSign, this]
  have e1 : ({i, i'} : Finset _).erase i = {i'} := by
    rw [Finset.erase_insert (by simpa using hne)]
  have e2 : ({i, i'} : Finset _).erase i' = {i} := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hx, rfl | rfl⟩
      · rfl
      · exact absurd rfl hx
    · rintro rfl; exact ⟨hne, Or.inl rfl⟩
  simp only [wd, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.proj_apply]
  rw [Finset.sum_pair hne, s1, s2, e1, e2, one_smul, neg_one_smul, sub_eq_add_neg]

private theorem pair_lt' {ι : Type} [LinearOrder ι] {s : Finset ι} (h : s.card = 2) :
    ∃ x y, x < y ∧ s = {x, y} := by
  obtain ⟨x, y, hne, rfl⟩ := Finset.card_eq_two.1 h
  rcases lt_or_gt_of_ne hne with h' | h'
  · exact ⟨x, y, h', rfl⟩
  · exact ⟨y, x, h', Finset.pair_comm _ _⟩

theorem UpperTheory.Gal.productCup_of_system.coordinateSystem_degree_two_of_universalDerivation :
    L2 → SysOk → WdUni → CechKoszulSystemCocycleGluing := by
  intro hL2 hOk h d S E _ _ _ _ T κ _ _ n z hG hAd hKE c0 hZ hB1 hB2
  obtain ⟨hW, -, -⟩ := hOk d S E T κ n z hG hAd
  have lu1 : ∀ (b : Finset (Two d)) (L : Finset κ), lft (uni b L) = b :=
    fun b L => (h (Two d) κ ℂ 0 0 b L).2.1
  have ru1 : ∀ (b : Finset (Two d)) (L : Finset κ), rgt (uni b L) = L :=
    fun b L => (h (Two d) κ ℂ 0 0 b L).2.2.1
  have lu2 : ∀ (I J : Finset (Fin (d + 1))), lft (uni I J) = I :=
    fun I J => (h (Fin (d + 1)) (Fin (d + 1)) ℂ 0 0 I J).2.1
  have ru2 : ∀ (I J : Finset (Fin (d + 1))), rgt (uni I J) = J :=
    fun I J => (h (Fin (d + 1)) (Fin (d + 1)) ℂ 0 0 I J).2.2.1
  have cu2 : ∀ (I J : Finset (Fin (d + 1))), (uni I J).card = I.card + J.card :=
    fun I J => (h (Fin (d + 1)) (Fin (d + 1)) ℂ 0 0 I J).2.2.2.1
  have ul2 : ∀ (s : Finset (Two d)), uni (lft s) (rgt s) = s :=
    fun s => (h (Fin (d + 1)) (Fin (d + 1)) ℂ 0 0 ∅ ∅).2.2.2.2 s
  set A : Finset (Two d ⊕ₗ κ) → Submodule ℂ E := fun s ↦ mixF (fun I J ↦
    Submodule.map (T.act ↑(∏ l ∈ rgt s, T.u n (pk I) (pk J) l)) (T.M I J)) (lft s) with hAdef
  have hcol : ∀ I J : Finset (Fin (d + 1)), I.Nonempty → J.Nonempty →
      colA A (T.wt z) (uni I J) = T.colCx n z I J := by
    intro I J hI hJ
    simp only [colA, Sys.colCx, kosT]
    congr 1
    funext L
    simp only [A, mixF, lu1, ru1, lu2, ru2, hI, hJ, and_self, if_true]
  have hbot : ∀ b : Finset (Two d), ¬ ((lft b).Nonempty ∧ (rgt b).Nonempty) → ∀ L,
      A (uni b L) = ⊥ := by
    intro b hb L
    simp only [A, mixF, lu1, ru1]
    rw [if_neg hb]
  set c0' : Finset (Two d) → Finset κ → E := fun b =>
    if (lft b).card = 1 ∧ (rgt b).card = 1 then c0 (pk (lft b)) (pk (rgt b)) else 0 with hc0'
  have pk1 : ∀ i : Fin (d + 1), pk ({i} : Finset (Fin (d + 1))) = i := by
    intro i; simp [pk]
  have c0ij : ∀ i j : Fin (d + 1), c0' (uni {i} {j}) = c0 i j := by
    intro i j; simp [c0', lu2, ru2, pk1]
  have cv : ∀ I' J' : Finset (Fin (d + 1)), c0' (uni I' J') =
      if I'.card = 1 ∧ J'.card = 1 then c0 (pk I') (pk J') else 0 := by
    intro I' J'; simp only [hc0', lu2, ru2]
  have hKEA : ∀ b : Finset (Two d), KE (colA A (T.wt z) b) d := by
    intro b
    by_cases hb : (lft b).Nonempty ∧ (rgt b).Nonempty
    · rw [← ul2 b, hcol _ _ hb.1 hb.2]
      exact hKE _ _ hb.1 hb.2
    · intro m _ x hx
      have hx0 : x = 0 := by
        funext L
        have h1 := (Submodule.mem_inf.mp hx).1
        have h2 := (Submodule.mem_pi.mp h1) L (Set.mem_univ _)
        simpa [hbot b hb L] using h2
      rw [hx0]
      exact zero_mem _
  have hZA : ∀ b : Finset (Two d), (b.card : ℤ) = (d : ℤ) + 2 - d →
      c0' b ∈ (colA A (T.wt z) b).Z d := by
    intro b hbc
    by_cases h11 : (lft b).card = 1 ∧ (rgt b).card = 1
    · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h11.1
      obtain ⟨j, hj⟩ := Finset.card_eq_one.mp h11.2
      have hb' : b = uni {i} {j} := by rw [← hi, ← hj, ul2]
      subst hb'
      rw [c0ij, hcol _ _ (Finset.singleton_nonempty i) (Finset.singleton_nonempty j)]
      exact hZ i j
    · have h0 : c0' b = 0 := by simp only [hc0', h11, if_false]
      rw [h0]
      exact zero_mem _
  have hw : (fun i : Two d => T.wt z (inlE i : Two d ⊕ₗ κ)) = fun _ => 1 := by
    funext i; simp [Sys.wt, inlE]
  have hBA : ∀ b : Finset (Two d), (b.card : ℤ) = (d : ℤ) + 2 - d + 1 →
      (fun L => (wd fun i => T.wt z (inlE i)) (fun b' => c0' b' L) b) ∈ (colA A (T.wt z) b).B d := by
    intro b hbc
    have hb3 : b.card = 3 := by omega
    rw [hw]
    obtain ⟨I, J, rfl⟩ : ∃ I J, b = uni I J := ⟨lft b, rgt b, (ul2 b).symm⟩
    have hIJ : I.card + J.card = 3 := by rw [← cu2]; exact hb3
    have dec : ∀ L, (wd fun _ : Two d => (1 : Module.End ℂ E)) (fun b' => c0' b' L) (uni I J) =
        (wd fun _ => 1) (fun I' => c0' (uni I' J) L) I +
          (-1) ^ I.card • (wd fun _ => 1) (fun J' => c0' (uni I J') L) J :=
      fun L => (h (Fin (d + 1)) (Fin (d + 1)) E (fun _ => 1) (fun b' => c0' b' L) I J).1
    have hcases : I.card = 0 ∨ I.card = 1 ∨ I.card = 2 ∨ I.card = 3 := by omega
    rcases hcases with hI | hI | hI | hI
    · have hI0 : I = ∅ := Finset.card_eq_zero.mp hI
      subst hI0
      have hf : (fun L => (wd fun _ : Two d => (1 : Module.End ℂ E)) (fun b' => c0' b' L) (uni ∅ J)) = 0 := by
        funext L
        rw [dec]
        have z1 : (fun J' => c0' (uni ∅ J') L) = 0 := by
          funext J'; simp [cv]
        rw [z1, map_zero]
        simp [wd]
      rw [hf]
      exact zero_mem _
    · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hI
      have hJ2 : J.card = 2 := by simp at hIJ; omega
      obtain ⟨j, j', hjj, rfl⟩ := pair_lt' hJ2
      have hf : (fun L => (wd fun _ : Two d => (1 : Module.End ℂ E)) (fun b' => c0' b' L) (uni {i} {j, j'})) =
          c0 i j - c0 i j' := by
        funext L
        rw [dec, wd_single', wd_pair' _ _ hjj]
        simp [cv, pk1]
      rw [hf, hcol _ _ (Finset.singleton_nonempty i) (Finset.insert_nonempty _ _)]
      exact hB2 i j j'
    · obtain ⟨i, i', hii, rfl⟩ := pair_lt' hI
      have hJ1 : J.card = 1 := by omega
      obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hJ1
      have hf : (fun L => (wd fun _ : Two d => (1 : Module.End ℂ E)) (fun b' => c0' b' L) (uni {i, i'} {j})) =
          -(c0 i j - c0 i' j) := by
        funext L
        rw [dec, wd_single', wd_pair' _ _ hii]
        simp [cv, pk1, Finset.card_pair (ne_of_lt hii)]
      rw [hf, hcol _ _ (Finset.insert_nonempty _ _) (Finset.singleton_nonempty j)]
      exact neg_mem (hB1 i i' j)
    · have hJ0 : J = ∅ := Finset.card_eq_zero.mp (by omega)
      subst hJ0
      have hf : (fun L => (wd fun _ : Two d => (1 : Module.End ℂ E)) (fun b' => c0' b' L) (uni I ∅)) = 0 := by
        funext L
        rw [dec]
        have z1 : (fun I' => c0' (uni I' ∅) L) = 0 := by
          funext I'; simp [cv]
        rw [z1, map_zero]
        simp [wd]
      rw [hf]
      exact zero_mem _
  obtain ⟨c, hc, hcb, -⟩ := hL2 (Two d) κ E A (T.wt z) d (d + 2) hW hKEA c0' hZA hBA
  refine ⟨c, hc, fun i j => ?_⟩
  have := hcb (uni {i} {j}) (by rw [cu2]; simp)
  rw [this, c0ij]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.CubeSignEmb
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private theorem cubeSign_emb {κ : Type} [LinearOrder κ] (t : Finset κ) {n : ℕ} (h : t.card = n) (k : Fin n) :
    GlobalTheory.cubeSign t (t.orderEmbOfFin h k) = (-1) ^ (k : ℕ) :=
  _root_.UpperTheory.Reformulated.B.Qh71.cubeSign_emb t h k

private theorem erase_emb {κ : Type} [LinearOrder κ] (t : Finset κ) {n : ℕ} (h : t.card = n + 1) (k : Fin (n + 1))
    (h' : (t.erase (t.orderEmbOfFin h k)).card = n) (a : Fin n) :
    (t.erase (t.orderEmbOfFin h k)).orderEmbOfFin h' a = t.orderEmbOfFin h (k.succAbove a) := by
  have := Finset.orderEmbOfFin_unique h' (f := fun a => t.orderEmbOfFin h (k.succAbove a))
    (fun x => Finset.mem_erase.2 ⟨fun hx => Fin.succAbove_ne k x ((t.orderEmbOfFin h).injective hx),
      Finset.orderEmbOfFin_mem _ _ _⟩)
    ((t.orderEmbOfFin h).strictMono.comp (Fin.strictMono_succAbove k))
  exact (congrFun this a).symm

private theorem detC_erase {S κ : Type} [CommRing S] [LinearOrder κ] {p : ℕ} (ρ : κ → Fin p → S) (t : Finset κ)
    (h : t.card = p + 1) (k : Fin (p + 1)) :
    detC ρ (t.erase (t.orderEmbOfFin h k)) =
      (Matrix.of fun a b => ρ (t.orderEmbOfFin h (k.succAbove a)) b).det := by
  have h' : (t.erase (t.orderEmbOfFin h k)).card = p := by
    rw [Finset.card_erase_of_mem (Finset.orderEmbOfFin_mem _ _ _), h]; rfl
  unfold detC
  rw [dif_pos h']
  congr 1
  ext a b
  simp only [Matrix.of_apply]
  rw [erase_emb t h k h' a]

private theorem ring_core {S κ : Type} [CommRing S] [LinearOrder κ] {p : ℕ} (ρ : κ → Fin p → S) (f : Fin p → S)
    (t : Finset κ) (h : t.card = p + 1) :
    ∑ i ∈ t, ((GlobalTheory.cubeSign t i : ℤ) : S) * ((∑ b, ρ i b * f b) * detC ρ (t.erase i)) = 0 := by
  set e := t.orderEmbOfFin h with he
  let A : Matrix (Fin (p + 1)) (Fin (p + 1)) S :=
    Matrix.of fun a => Fin.cons (∑ b, ρ (e a) b * f b) (ρ (e a))
  have hA : A.det = 0 := by
    have h1 := Matrix.det_updateCol_sum A 0 (Fin.cons 0 f : Fin (p + 1) → S)
    have h2 : (A.updateCol 0 fun k => ∑ i, (Fin.cons 0 f : Fin (p + 1) → S) i • A k i) = A := by
      ext a b
      refine Fin.cases ?_ (fun b => ?_) b
      · simp [A, Matrix.updateCol_apply, Fin.sum_univ_succ, mul_comm]
      · simp [A, Matrix.updateCol_apply, Fin.succ_ne_zero]
    rw [h2] at h1
    simpa using h1
  have ht : t = Finset.univ.map e.toEmbedding := by
    rw [he, Finset.map_orderEmbOfFin_univ]
  have hs : ∑ i ∈ t, ((GlobalTheory.cubeSign t i : ℤ) : S) * ((∑ b, ρ i b * f b) * detC ρ (t.erase i)) =
      ∑ k : Fin (p + 1), (((-1 : ℤ) ^ (k : ℕ) : ℤ) : S) * ((∑ b, ρ (e k) b * f b) * detC ρ (t.erase (e k))) := by
    conv_lhs => rw [show (∑ i ∈ t, ((GlobalTheory.cubeSign t i : ℤ) : S) * ((∑ b, ρ i b * f b) * detC ρ (t.erase i))) =
      ∑ i ∈ Finset.univ.map e.toEmbedding, ((GlobalTheory.cubeSign t i : ℤ) : S) * ((∑ b, ρ i b * f b) * detC ρ (t.erase i)) by
        rw [← ht]]
    rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [RelEmbedding.coe_toEmbedding]
    rw [he, cubeSign_emb t h k]
  rw [hs, ← hA, Matrix.det_succ_column_zero]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [he, detC_erase ρ t h k]
  have : (A.submatrix k.succAbove Fin.succ) = Matrix.of fun a b => ρ (t.orderEmbOfFin h (k.succAbove a)) b := by
    ext a b
    simp [A, he]
  rw [this]
  simp [A, he, mul_assoc]

theorem UpperTheory.Gal.productCup_of_system.det_of :
    Det := by
  intro S E _ _ _ _ act κ _ p ρ f m
  funext t
  have key : wd (fun l => act (∑ b, ρ l b * f b)) (fun s => act (detC ρ s) m) t =
      ∑ i ∈ t, (GlobalTheory.cubeSign t i : ℤ) • act (∑ b, ρ i b * f b) (act (detC ρ (t.erase i)) m) := by
    simp [wd, LinearMap.pi_apply, LinearMap.sum_apply]
  rw [key]
  by_cases h : t.card = p + 1
  · have h0 := congrArg (fun x => act x m) (ring_core ρ f t h)
    simp only [map_zero, LinearMap.zero_apply, map_sum, LinearMap.sum_apply] at h0
    rw [Pi.zero_apply, ← h0]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← zsmul_eq_mul, map_zsmul, LinearMap.smul_apply, map_mul, Module.End.mul_apply]
  · rw [Pi.zero_apply]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hc : (t.erase i).card ≠ p := by
      rw [Finset.card_erase_of_mem hi]
      have := Finset.card_pos.2 ⟨i, hi⟩
      omega
    simp [detC, hc]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.EuclideanHeightMul
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace UpperTheory.Gal.productCup_of_system

section SlopeTestRemainingChoices

variable {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
  (act : S →ₐ[ℂ] Module.End ℂ E) (R : Subalgebra ℂ S) (M : Submodule ℂ E)

@[reducible] private def modR (h : Stab act R M) : Module R M where
  smul r m := ⟨act r m, h r r.2 m m.2⟩
  one_smul m := Subtype.ext (by
    change act ((1 : R) : S) (m : E) = m
    simp)
  mul_smul a b m := Subtype.ext (by
    change act ((a * b : R) : S) (m : E) = act a (act b m)
    simp [Module.End.mul_apply])
  smul_zero a := Subtype.ext (by
    change act a ((0 : M) : E) = 0
    simp)
  smul_add a m m' := Subtype.ext (by
    change act a ((m + m' : M) : E) = act a m + act a m'
    simp)
  add_smul a b m := Subtype.ext (by
    change act ((a + b : R) : S) (m : E) = act a m + act b m
    simp)
  zero_smul m := Subtype.ext (by
    change act ((0 : R) : S) (m : E) = 0
    simp)

variable {act R M}

private theorem mem_ofList_iff [Module R M] [IsScalarTower ℂ R M] (hsm : ∀ (a : R) (m : M), ((a • m : M) : E) = act a m)
    {d : ℕ} (f : Fin d → R) (k : ℕ) (x : M) :
    x ∈ (Ideal.ofList ((List.ofFn f).take k) • ⊤ : Submodule R M) ↔
      (x : E) ∈ sm act M ((fun j => (f j : S)) '' {j | j.val < k}) := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro a ha n _
      have : ∀ n : M, ((a • n : M) : E) ∈ sm act M ((fun j => (f j : S)) '' {j | j.val < k}) := by
        refine Submodule.span_induction ?_ ?_ ?_ ?_ ha
        · intro b hb n
          obtain ⟨i, hi, rfl⟩ := List.mem_take_iff_getElem.1 hb
          have hi' : i < k := lt_of_lt_of_le hi (min_le_left _ _)
          have hid : i < d := by
            have := lt_of_lt_of_le hi (min_le_right _ _)
            simpa using this
          rw [hsm]
          refine Submodule.mem_iSup_of_mem ((f ⟨i, hid⟩ : S)) (Submodule.mem_iSup_of_mem
            ⟨⟨i, hid⟩, hi', rfl⟩ ?_)
          simpa using ⟨n, n.2, rfl⟩
        · intro n
          simp
        · intro a b _ _ ha hb n
          rw [add_smul]
          simpa using Submodule.add_mem _ (ha n) (hb n)
        · intro a b _ hb n
          rw [smul_eq_mul, mul_comm, mul_smul]
          exact hb (a • n)
      exact this n
    · intro a b ha hb
      simpa using Submodule.add_mem _ ha hb
  · intro hx
    have hle : sm act M ((fun j => (f j : S)) '' {j | j.val < k}) ≤
        ((Ideal.ofList ((List.ofFn f).take k) • ⊤ : Submodule R M).restrictScalars ℂ).map M.subtype := by
      refine iSup₂_le ?_
      rintro _ ⟨j, hj, rfl⟩ _ ⟨m, hm, rfl⟩
      have hmem : f j • (⟨m, hm⟩ : M) ∈ (Ideal.ofList ((List.ofFn f).take k) • ⊤ : Submodule R M) := by
        refine Submodule.smul_mem_smul (Ideal.subset_span ?_) Submodule.mem_top
        refine List.mem_take_iff_getElem.2 ⟨j.val, ?_, by simp⟩
        simpa using hj
      exact Submodule.mem_map.2 ⟨_, (Submodule.restrictScalars_mem ℂ _ _).2 hmem, hsm _ _⟩
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.1 (hle hx)
    have hyx' : y = x := Subtype.ext hyx
    rw [← hyx']
    exact (Submodule.restrictScalars_mem ℂ _ _).1 hy

private theorem wd_coe [Module R M] [IsScalarTower ℂ R M]
    (hsm : ∀ (a : R) (m : M), ((a • m : M) : E) = act a m) {κ : Type} [LinearOrder κ] (r : κ → R)
    (c : Finset κ → M) (t : Finset κ) :
    ((wd (fun l => Algebra.lsmul ℂ ℂ M (r l)) c t : M) : E) =
      wd (fun l => act (r l)) (fun s => (c s : E)) t := by
  simp [wd, hsm]

private theorem koszulExact_of_regular (hK : KoszulExactBelowLengthOfWeaklyRegular) {κ : Type} [LinearOrder κ] [Fintype κ] (r : κ → S) {d : ℕ}
    (f : Fin d → S) (hS : Stab act R M) (hr : ∀ l, r l ∈ R) (hReg : Reg act M f)
    (hf : ∀ j, InSp R r (f j)) : KE (kos act M r) d := by
  letI := modR act R M hS
  have hsm : ∀ (a : R) (m : M), ((a • m : M) : E) = act a m := fun _ _ => rfl
  haveI : IsScalarTower ℂ R M := ⟨fun c a m => Subtype.ext (by
    change act ((c • a : R) : S) (m : E) = c • act a m
    simp)⟩
  have hfR : ∀ j, f j ∈ R := by
    intro j
    obtain ⟨a, ha, h⟩ := hf j
    rw [h]
    exact sum_mem fun l _ => R.mul_mem (ha l) (hr l)
  let r' : κ → R := fun l => ⟨r l, hr l⟩
  let f' : Fin d → R := fun j => ⟨f j, hfR j⟩
  have hreg : RingTheory.Sequence.IsWeaklyRegular M (List.ofFn f') := by
    refine ⟨fun i hi => ?_⟩
    have hid : i < d := by simpa using hi
    rw [isSMulRegular_on_quot_iff_lsmul_comap_le]
    intro x hx
    rw [Submodule.mem_comap, LinearMap.lsmul_apply, mem_ofList_iff hsm] at hx
    rw [mem_ofList_iff hsm]
    have hget : (List.ofFn f')[i] = f' ⟨i, hid⟩ := by simp
    rw [hget, hsm] at hx
    exact hReg ⟨i, hid⟩ x x.2 hx
  have hsp : ∀ g ∈ List.ofFn f', InSp (⊤ : Subalgebra ℂ R) r' g := by
    intro g hg
    obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hg
    obtain ⟨a, ha, h⟩ := hf j
    refine ⟨fun l => ⟨a l, ha l⟩, fun _ => trivial, Subtype.ext ?_⟩
    simpa [f', r'] using h
  have key := hK d R M κ r' (List.ofFn f') (by simp) hreg hsp
  intro m hm c hc
  obtain ⟨hcC, hcD⟩ := hc
  have hcM : ∀ s, c s ∈ M := by
    intro s
    have : c s ∈ if (s.card : ℤ) = m then M else ⊥ := hcC s (Set.mem_univ s)
    split_ifs at this with h
    · exact this
    · rw [Submodule.mem_bot] at this
      exact this ▸ M.zero_mem
  let c' : Finset κ → M := fun s => ⟨c s, hcM s⟩
  have hc' : c' ∈ (kos (Algebra.lsmul ℂ ℂ M) (⊤ : Submodule ℂ M) r').Z m := by
    constructor
    · intro s _
      have : c s ∈ if (s.card : ℤ) = m then M else ⊥ := hcC s (Set.mem_univ s)
      change c' s ∈ if (s.card : ℤ) = m then (⊤ : Submodule ℂ M) else ⊥
      split_ifs at this ⊢ with h
      · trivial
      · rw [Submodule.mem_bot] at this ⊢
        exact Subtype.ext this
    · refine LinearMap.mem_ker.2 (funext fun t => Subtype.ext ?_)
      have := wd_coe hsm r' c' t
      exact this.trans (congrFun (LinearMap.mem_ker.1 hcD) t)
  obtain ⟨y, hy, hyc⟩ := key m hm hc'
  refine ⟨fun s => (y s : E), ?_, ?_⟩
  · intro s _
    have : y s ∈ if (s.card : ℤ) = m - 1 then (⊤ : Submodule ℂ M) else ⊥ := hy s (Set.mem_univ s)
    change (y s : E) ∈ if (s.card : ℤ) = m - 1 then M else ⊥
    split_ifs at this ⊢ with h
    · exact (y s).2
    · rw [Submodule.mem_bot] at this ⊢
      rw [this]
      rfl
  · funext t
    have h1 := wd_coe hsm r' y t
    have h2 : ((wd (fun l => Algebra.lsmul ℂ ℂ M (r' l)) y t : M) : E) = c t :=
      congrArg (fun z : Finset κ → M => ((z t : M) : E)) hyc
    exact h1.symm.trans h2

end SlopeTestRemainingChoices

end UpperTheory.Gal.productCup_of_system

end

theorem UpperTheory.Gal.productCup_of_system.firstCohomologyBound_of_boundaryBound :
    KoszulExactBelowLengthOfWeaklyRegular → K1 := by
  intro hK S E _ _ _ _ act κ _ _ R M r d f hS hr hReg hf
  exact koszulExact_of_regular hK r f hS hr hReg hf
end

