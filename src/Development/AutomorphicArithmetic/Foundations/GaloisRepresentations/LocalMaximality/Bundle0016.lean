import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0418

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.WdOneApply
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma resP_eq_zero {F V : Type} [Field F] [Algebra ℂ F] [AddCommGroup V] [Module ℂ V]
    (ρ : F →ₗ[ℂ] ℂ) (A : Submodule ℂ F) (B : Submodule ℂ V) (hA : ∀ f ∈ A, ρ f = 0)
    {m : F ⊗[ℂ] V} (hm : m ∈ Submodule.map₂ (TensorProduct.mk ℂ F V) A B) :
    resP V ρ m = 0 := by
  rw [Submodule.map₂_eq_span_image2] at hm
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    simp [resP, hA a ha]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul r x _ hx => rw [map_smul, hx, smul_zero]

private lemma residueCharacteristic_mem {F V : Type} [Field F] [Algebra ℂ F] [AddCommGroup V] [Module ℂ V]
    (ρ : F →ₗ[ℂ] ℂ) (A : Submodule ℂ F) (B : Submodule ℂ V)
    {m : F ⊗[ℂ] V} (hm : m ∈ Submodule.map₂ (TensorProduct.mk ℂ F V) A B) :
    resP V ρ m ∈ B := by
  rw [Submodule.map₂_eq_span_image2] at hm
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    simpa [resP] using B.smul_mem (ρ a) hb
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact B.add_mem hx hy
  | smul r x _ hx => rw [map_smul]; exact B.smul_mem r hx

private lemma wd_one_apply {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E] (c : Finset ι → E) (t : Finset ι) :
    wd (fun _ : ι => (1 : Module.End ℂ E)) c t = ∑ i ∈ t, GlobalTheory.cubeSign t i • c (t.erase i) := by
  simp [wd, LinearMap.sum_apply]

theorem UpperTheory.Gal.productCup_of_system.pInt_of :
    WdUni → GoodZ → PInt := by
  intro hW _ F K _ _ _ _ _ _ d x hx τ _ ρ hρ a p t ht
  simp only [UpperTheory.Gal.productCup_of_system.Sys.mix, GlobalTheory.WH.acx, GlobalTheory.PD.Cx.B, Submodule.mem_map,
    Submodule.mem_pi] at ht
  obtain ⟨c, hc, rfl⟩ := ht
  have hU := fun I J : Finset (Fin (d + 1)) =>
    hW (Fin (d + 1)) (Fin (d + 1)) (F ⊗[ℂ] DR ℂ K) (fun _ => 1) c I J
  have hcu : ∀ I J : Finset (Fin (d + 1)), c (uni I J) ≠ 0 →
      I.Nonempty ∧ J.Nonempty ∧ I.card + J.card = d + p + 1 ∧
        c (uni I J) ∈ (sysP K x a).M I J := by
    intro I J h0
    have h := hc (uni I J) (Set.mem_univ _)
    obtain ⟨_, hl, hr, hcard, _⟩ := hU I J
    split_ifs at h with h1
    · simp only [GlobalTheory.WH.mixF, hl, hr] at h
      split_ifs at h with h2
      · refine ⟨h2.1, h2.2, ?_, h⟩
        rw [hcard] at h1
        omega
      · exact absurd ((Submodule.mem_bot ℂ).mp h) h0
    · exact absurd ((Submodule.mem_bot ℂ).mp h) h0
  have hz : ∀ (i : Fin (d + 1)) (J : Finset (Fin (d + 1))),
      resP (DR ℂ K) ρ (c (uni (Finset.univ.erase i) J)) = 0 := by
    intro i J
    by_cases h0 : c (uni (Finset.univ.erase i) J) = 0
    · rw [h0, map_zero]
    obtain ⟨hI, _, _, hm⟩ := hcu _ _ h0
    exact resP_eq_zero ρ _ _
      (fun f hf => GlobalTheory.T.residue_functional_vanishes_on_omega_forms ℂ F d (xv x) hx.pd ρ hρ i _ hI (by simp) f hf) hm
  refine ⟨fun L => ((-1 : ℤ) ^ (d + 1)) • resP (DR ℂ K) ρ (c (uni Finset.univ L)), ?_, ?_⟩
  · simp only [Lef.omCx, GlobalTheory.PD.cech, GlobalTheory.PD.cechC, Submodule.mem_pi]
    intro L _
    by_cases h0 : c (uni Finset.univ L) = 0
    · simp [h0]
    obtain ⟨_, hL, hcard, hm⟩ := hcu _ _ h0
    rw [Finset.card_univ, Fintype.card_fin] at hcard
    dsimp only
    rw [if_pos (show L.Nonempty ∧ (L.card : ℤ) = ↑p - 1 + 1 from ⟨hL, by omega⟩)]
    exact Submodule.smul_of_tower_mem _ _ (residueCharacteristic_mem ρ _ _ hm)
  · funext J
    simp only [Lef.omCx, GlobalTheory.PD.cech, GlobalTheory.PD.deltaL, LinearMap.coe_mk, AddHom.coe_mk, GlobalTheory.DI.delta]
    rw [(hU Finset.univ J).1]
    simp only [wd_one_apply, map_add, map_zsmul, map_sum, hz, smul_zero, Finset.sum_const_zero,
      zero_add, Finset.card_univ, Fintype.card_fin, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_comm]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ZActionCriterion
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private theorem resP_one {F V : Type} [Field F] [Algebra ℂ F] [AddCommGroup V] [Module ℂ V] (ρ : F →ₗ[ℂ] ℂ)
    (h : ρ 1 = 1) (w : V) : resP V ρ ((1 : F) ⊗ₜ[ℂ] w) = w := by
  simp [resP, h]

private theorem lft_uni' {ι κ : Type} [LinearOrder ι] [LinearOrder κ] (I : Finset ι) (J : Finset κ) :
    lft (uni I J) = I := by
  ext i
  simp [lft, uni, Finset.mem_toLeft]

private theorem rgt_uni' {ι κ : Type} [LinearOrder ι] [LinearOrder κ] (I : Finset ι) (J : Finset κ) :
    rgt (uni I J) = J := by
  ext i
  simp [rgt, uni, Finset.mem_toRight]

private theorem card_filter_le {d : ℕ} (i : Fin (d + 1)) :
    (Finset.univ.filter (· ≤ i)).card = (i : ℕ) + 1 := by
  have h : Finset.univ.filter (· ≤ i) = Finset.Iic i := by
    ext j
    simp
  rw [h, Fin.card_Iic]

private theorem card_filter_ge {d : ℕ} (i : Fin (d + 1)) :
    (Finset.univ.filter (i ≤ ·)).card = d + 1 - (i : ℕ) := by
  have h : Finset.univ.filter (i ≤ ·) = Finset.Ici i := by
    ext j
    simp
  rw [h, Fin.card_Ici]

theorem UpperTheory.Gal.productCup_of_system.zAct_of :
    PCup → PTheta → PCmp → PInt → EdgeRel → SysBasic → GoodZ → ZAct := by
  intro hCup hTh hCmp hInt hEdge hBas hGood F K _ _ _ _ _ _ d x hx τ hτ ρ hρ a p ha c hc hD α hα
  obtain ⟨hc1, hv1, hk1⟩ := hCup F K d x hx τ hτ a p ha c hc hD α hα
  obtain ⟨cθ, hcθ, hvθ, hkθ, htθ⟩ := hTh F K d x hx a p α hα
  have hmono := (hGood F K d x hx a).2.2
  have hE := hEdge (Fin (d + 1)) (DR ℂ K) (fun s => omB ℂ K (rB ℂ K (xv x) s) a) p hmono α hα
  let c1 := rcup (muP F K τ) p c α - cθ
  have hZ : c1 ∈ ((sysP K x a).cx n11 (sysP K x a).mu).Z (d + p + 2) := sub_mem hc1 hcθ
  have hv : ∀ (b : Finset (Two d)) (L : Finset (Mi d)), d < L.card → c1 (uni b L) = 0 := by
    intro b L h
    simp [c1, hv1 b L h, hvθ b L h]
  let γ : Finset (Two d) → DR ℂ K :=
    ((-1 : ℤ) ^ (p * (d + 1) + d)) • edge1 α - ((-1 : ℤ) ^ ((p + 1) * d)) • edge2 α
  have hγe : γ = (-((-1 : ℤ) ^ ((p + 1) * d))) • (edge2 α - ((-1 : ℤ) ^ p) • edge1 α) := by
    have h : p * (d + 1) + d = (p + 1) * d + p := by ring
    simp only [γ, h, pow_add]
    generalize ((-1 : ℤ) ^ ((p + 1) * d)) = s
    generalize ((-1 : ℤ) ^ p) = t
    module
  have hγ : γ ∈ (acx (mixF fun I J : Finset (Fin (d + 1)) => omB ℂ K (rB ℂ K (xv x) (I ∪ J)) a) fun _ => 1).B (p + 2) := by
    rw [hγe]
    exact zsmul_mem hE _
  have hk : ∀ (b : Finset (Two d)) (L : Finset (Mi d)), L.card = d → mulP F K (c1 (uni b L)) = kap K x L • γ b := by
    intro b L h
    simp only [c1, γ, Pi.sub_apply, map_sub, hk1 b L h, hkθ b L h, smul_sub, Pi.smul_apply]
  have hB := hCmp F K d x hx a p c1 hZ hv γ hγ hk
  have hTop := (hBas d _ _ (sysP K x a) (Mi d) n11 (sysP K x a).mu (d + p + 2)).2.2.2.1 c1 hB
  have hI := hInt F K d x hx τ hτ ρ hρ a p (top c1) hTop
  have hCc := (hBas d _ _ (sysZ K x a) (Mi d) n11 (sysZ K x a).mu (d + 2)).1 c hc.1
  have hαs : ∀ s : Finset (Fin (d + 1)), s.card ≠ p + 1 → α s = 0 := by
    intro s hs
    have h1 : α s ∈ (if s.Nonempty ∧ (s.card : ℤ) = (p : ℤ) + 1 then omB ℂ K (rB ℂ K (xv x) s) a else ⊥ :
        Submodule ℂ (DR ℂ K)) := hα.1 s (Set.mem_univ s)
    rw [if_neg (by
      rintro ⟨-, h⟩
      exact hs (by exact_mod_cast h))] at h1
    simpa using h1
  have key : (α - fun J => resP (DR ℂ K) ρ (∑ i, muP F K τ (top c (uni (Finset.univ.filter (· ≤ i)) J)) (α (Finset.univ.filter (i ≤ ·))))) =
      -(fun J => resP (DR ℂ K) ρ (top c1 (uni Finset.univ J))) := by
    funext J
    have hsum : ((-1 : ℤ) ^ (p * J.card)) • (∑ i, muP F K τ (top c (uni (Finset.univ.filter (· ≤ i)) J)) (α (Finset.univ.filter (i ≤ ·)))) =
        ∑ i, muP F K τ (top c (uni (Finset.univ.filter (· ≤ i)) J)) (α (Finset.univ.filter (i ≤ ·))) := by
      by_cases hJ : J.card = p + 1
      · have : Even (p * J.card) := by
          rw [hJ]
          exact Nat.even_mul_succ_self p
        rw [this.neg_one_pow, one_smul]
      · have : ∑ i, muP F K τ (top c (uni (Finset.univ.filter (· ≤ i)) J)) (α (Finset.univ.filter (i ≤ ·))) = 0 := by
          refine Finset.sum_eq_zero fun i _ => ?_
          by_cases hi : (Finset.univ.filter (i ≤ ·)).card = p + 1
          · have h0 : top c (uni (Finset.univ.filter (· ≤ i)) J) = 0 := by
              refine hCc _ _ ∅ (Or.inr (Or.inr ?_))
              rw [card_filter_ge] at hi
              have hid := i.is_lt
              simp only [card_filter_le, Finset.card_empty, add_zero]
              omega
            rw [h0]
            simp
          · rw [hαs _ hi]
            simp
        rw [this, smul_zero]
    have htop : top c1 (uni Finset.univ J) = ((-1 : ℤ) ^ (p * J.card)) • (∑ i, muP F K τ (top c (uni (Finset.univ.filter (· ≤ i)) J)) (α (Finset.univ.filter (i ≤ ·)))) - (1 : F) ⊗ₜ[ℂ] α J := by
      simp only [top, c1, Pi.sub_apply, htθ, rcup, lft_uni', rgt_uni', Finset.card_empty, add_zero]
    simp only [Pi.sub_apply, Pi.neg_apply]
    rw [htop, hsum, map_sub, resP_one ρ hρ.1]
    abel
  rw [key]
  exact neg_mem hI
end

