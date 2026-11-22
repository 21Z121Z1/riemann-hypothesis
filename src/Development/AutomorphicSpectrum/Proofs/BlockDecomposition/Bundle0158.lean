import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0004
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TotPairing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0122
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0129
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NegOneSmulCancel
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0151
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StCocycle
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0142
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0150
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1CoboundaryMemBoundaries
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PairSums.SumPair

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedCoverVanishingInduction
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeZig

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C]

theorem res_cupList {A : C ⥤ CommAlgCat.{0} R} {U V : ObjectProperty C} (h : V ≤ U) {k : ℕ} (l : Fin k → Ch A U 1) :
    resB A h (cupListC (U.ι ⋙ A) l) = cupListC (V.ι ⋙ A) fun j => resB A h (l j) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (CH.mulP _).cupC _ (resB A h (cupListC _ fun i => l (Fin.castSucc i))) (resB A h (l (Fin.last k))) = _
    rw [ih]
    rfl

theorem PP_eq {A : C ⥤ CommAlgCat.{0} R} {N : ℕ} {W : Fin N → ObjectProperty C} (b : ∀ α, Ch A (W α) 1)
    {V : ObjectProperty C} (hWV : ∀ α, W α ≤ V) (z : Ch A V 2) (k : ℕ) :
    ∃ e : ℤ, e * e = 1 ∧ ∀ i : Idx (k + 1) N, PP b hWV z k i =
      e • cupListC ((capT W i.1).ι ⋙ A) fun j : Fin k => LL b i j.castSucc j.succ := by
  induction k with
  | zero => exact ⟨1, rfl, fun i => (one_smul ℤ _).symm⟩
  | succ k ih =>
    obtain ⟨e, he, h⟩ := ih
    refine ⟨(-1) ^ k * e, ?_, fun i => ?_⟩
    · rw [mul_mul_mul_comm, he, ← mul_pow]; simp
    · change (-1 : ℤ) ^ k • BB b k k (PP b hWV z k) i = _
      have hLL : ∀ j : Fin k, resB A (cap_le W (Fin.last (k + 1)) i) (LL b (fc (Fin.last (k + 1)) i) j.castSucc j.succ) =
          LL b i j.castSucc.castSucc j.castSucc.succ := by
        intro j
        refine res_LL b i _ _ _ _ _ _ (congrArg i.1 ?_) (congrArg i.1 ?_) <;>
        · have := j.2
          apply Fin.ext
          simp only [CrystallineSemistableComparison.Auxff.sa_val, Fin.val_castSucc, Fin.val_last, Fin.val_succ]
          split_ifs <;> omega
      rw [BB_apply, h, map_zsmul, bm_apply, res_cupList, mul_smul]
      simp only [hLL]
      rfl

theorem PP_mem (Φ : PDF R C) (Fil : ℤ → IdF Φ.A) (hF : IsFil Φ Fil) {N : ℕ} {W : Fin N → ObjectProperty C}
    (b : ∀ α, Ch Φ.A (W α) 1) {V : ObjectProperty C} (hWV : ∀ α, W α ≤ V) (z : Ch Φ.A V 2)
    (hb1 : ∀ α, b α ∈ Lm (Fil 1) (W α) 1) (k : ℕ) :
    PP b hWV z k ∈ (dfil (W := W) Fil hF.anti).L (k : ℤ) k k := by
  induction k with
  | zero =>
    intro i _ σ
    rw [hF.top _ (by simp)]
    trivial
  | succ k ih =>
    refine Submodule.smul_of_tower_mem _ _ ?_
    intro i _
    refine Lm_cup (a := Fil k) (b := Fil 1) (fun T x y hx hy => hF.mul k 1 T hx (by simpa using hy)) rfl
      (Lm_res (cap_le W _ i) (ih (fc (Fin.last (k + 1)) i) trivial)) (sub_mem (Lm_res _ (hb1 _)) (Lm_res _ (hb1 _)))

theorem capT_eq {N : ℕ} (W : Fin N → ObjectProperty C) {m : ℕ} (i : Fin m → Fin N) :
    capT W i = capS W (Finset.univ.image i) := by
  funext T
  refine propext ⟨fun h α hα => ?_, fun h a => h _ (Finset.mem_image_of_mem _ (Finset.mem_univ a))⟩
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hα
  exact h a

theorem KEx (Φ : PDF R C) (Fil : ℤ → IdF Φ.A) (hF : IsFil Φ Fil) {N : ℕ} (W : Fin N → ObjectProperty C)
    (hS : ∀ S : Finset (Fin N), S.Nonempty → ∀ (r : ℤ) (j : ℕ), (j : ℤ) ≠ r → Subsingleton (HU (gr Fil r) (capS W S) j))
    (r : ℕ) (p q : ℕ) (hq : q ≠ r) : (dfil (W := W) Fil hF.anti).Ex (r : ℤ) p q := by
  have hH : ∀ (i : Idx (p + 1) N) (j : ℕ), j ≠ r → Subsingleton (HU (gr Fil r) (capT W i.1) j) := by
    intro i j hj
    rw [capT_eq]
    exact hS _ ⟨i.1 0, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩ _ _ (by exact_mod_cast hj)
  cases q with
  | zero =>
    intro x hx hd i _ σ
    exact ex_zero (a := (Fil r).res (capT W i.1).ι) (b := (Fil (r + 1)).res (capT W i.1).ι) (hH i 0 hq) (x i)
      (hx i trivial) (hd i trivial) σ
  | succ q =>
    intro x hx hd
    have h := fun i : Idx (p + 1) N =>
      ex_succ (a := (Fil r).res (capT W i.1).ι) (b := (Fil (r + 1)).res (capT W i.1).ι) (hH i (q + 1) hq) (x i)
        (hx i trivial) (hd i trivial)
    choose v hv hv' using h
    exact ⟨v, fun i _ => hv i, fun i _ => hv' i⟩

theorem alg_fin {M : Type*} [AddCommGroup M] {ι : Type} [Fintype ι] (e s : ℤ) (he : e * e = 1) (Cl Pv E : M) (t : ι → M)
    (sg : ι → ℤ) (h1 : Pv = e • Cl) (h2 : Pv = ∑ k, sg k • t k + s • E) :
    Cl - ∑ k, (e * sg k) • t k = (e * s) • E := by
  have h3 : Cl = e • Pv := by rw [h1, smul_smul, he, one_smul]
  rw [h3, h2, smul_add, Finset.smul_sum]
  simp only [smul_smul]
  abel

theorem KV (A : C ⥤ CommAlgCat.{0} R) (n : ℕ) (W : Fin (n + 2) → ObjectProperty C) (p q : ℕ) (h : n + 1 < p) :
    Subsingleton ((KK A W).X p q) := by
  have e : IsEmpty (Idx (p + 1) (n + 2)) := ⟨fun i => by
    have := Fintype.card_le_of_injective _ i.2.injective
    simp only [Fintype.card_fin] at this
    omega⟩
  exact ⟨fun x y => funext fun i => (e.false i).elim⟩

theorem fin_step {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (Φ : PDF R C) (Fil : ℤ → IdF Φ.A) (n : ℕ)
    (W : Fin (n + 2) → ObjectProperty C) (Cl : Ch Φ.A (capS W Finset.univ) (n + 1))
    (hCl : Cl ∈ Lm (Fil ((n : ℤ) + 1)) _ (n + 1))
    (c : HU (gr Fil ((n : ℤ) + 1)) (capS W Finset.univ) (n + 1))
    (hc : Rep ((Fil ((n : ℤ) + 1)).res (capS W Finset.univ).ι) ((Fil ((n : ℤ) + 1 + 1)).res (capS W Finset.univ).ι) Cl c)
    (w : ∀ k : Fin (n + 2), Ch Φ.A (capS W (Finset.univ.erase k)) (n + 1))
    (hw : ∀ k, w k ∈ Lm (Fil ((n : ℤ) + 1)) _ (n + 1))
    (hdw : ∀ k, CH.d _ (n + 1) (w k) ∈ Lm (Fil ((n : ℤ) + 1 + 1)) _ (n + 2))
    (f : Ch Φ.A (capS W Finset.univ) n) (hf : f ∈ Lm (Fil (n : ℤ)) _ n)
    (hEq : Cl - ∑ k, resB Φ.A (capS_univ_le W (Finset.univ.erase k)) (w k) = CH.d _ n f) :
    ∃ (ω : ∀ i, HU (gr Fil ((n : ℤ) + 1)) (capS W (Finset.univ.erase i)) (n + 1))
      (f : CH.Cn (CH.modF ((capS W Finset.univ).ι ⋙ Φ.A)) n),
      (∀ σ, f σ ∈ (Fil n).S _) ∧ (∀ σ, CH.d _ n f σ ∈ (Fil ((n : ℤ) + 1)).S _) ∧
      Rep ((Fil ((n : ℤ) + 1)).res (capS W Finset.univ).ι) ((Fil ((n : ℤ) + 1 + 1)).res (capS W Finset.univ).ι)
        (CH.d _ n f) (c - ∑ i, ((resU (gr Fil ((n : ℤ) + 1)) (capS_univ_le W (Finset.univ.erase i))).pull (n + 1)) (ω i)) := by
  have hG : ∀ k : Fin (n + 2), CH.d _ (n + 1) (gC ((Fil ((n : ℤ) + 1)).res (capS W (Finset.univ.erase k)).ι)
      ((Fil ((n : ℤ) + 1 + 1)).res (capS W (Finset.univ.erase k)).ι) (w k) (hw k)) = 0 := fun k =>
    gC_d (a := (Fil ((n : ℤ) + 1)).res (capS W (Finset.univ.erase k)).ι)
      (b := (Fil ((n : ℤ) + 1 + 1)).res (capS W (Finset.univ.erase k)).ι) (w k) (hw k) (fun s => hdw k s)
  have hY : ∀ k : Fin (n + 2), CH.d _ (n + 1) ((resU (gr Fil ((n : ℤ) + 1)) (capS_univ_le W (Finset.univ.erase k))).pullC (n + 1)
      (gC ((Fil ((n : ℤ) + 1)).res (capS W (Finset.univ.erase k)).ι)
        ((Fil ((n : ℤ) + 1 + 1)).res (capS W (Finset.univ.erase k)).ι) (w k) (hw k))) = 0 := fun k => by
    rw [CH.Mor.d_pullC]
    exact (congrArg _ (hG k)).trans (map_zero _)
  refine ⟨fun k => (CH.cx _).cls (gC ((Fil ((n : ℤ) + 1)).res (capS W (Finset.univ.erase k)).ι)
      ((Fil ((n : ℤ) + 1 + 1)).res (capS W (Finset.univ.erase k)).ι) (w k) (hw k)) (hG k), f, hf, ?_, ?_⟩
  · rw [← hEq]
    refine (show _ ∈ Lm (Fil ((n : ℤ) + 1)) _ (n + 1) from sub_mem hCl (Submodule.sum_mem _ fun k _ => ?_))
    exact Lm_res _ (hw k)
  · exact rep_fin hc _ (fun k : Fin (n + 2) => resB Φ.A (capS_univ_le W (Finset.univ.erase k)) (w k)) hY (fun k s => rfl) hEq

theorem cech_top_cup_power : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (Φ : PDF R C) (Fil : ℤ → IdF Φ.A),
    IsFil Φ Fil → ∀ (s n : ℕ) (W : Fin (n + 2) → ObjectProperty C), (∀ T, (∃ α, W α T) → (Fil s).S T = ⊥) →
    (∀ α ⦃T T' : C⦄, (T ⟶ T') → W α T → (∃ β, W β T') → W α T') →
    (∀ S : Finset (Fin (n + 2)), S.Nonempty → ∀ (r : ℤ) (j : ℕ), (j : ℤ) ≠ r → Subsingleton (HU (gr Fil r) (capS W S) j)) →
    (∀ S : Finset (Fin (n + 2)), S.Nonempty → ∀ (r : ℤ) (j : ℕ), (n : ℤ) + 1 < r → Subsingleton (HU (gr Fil r) (capS W S) j)) →
    ∀ (z : CH.Cn (CH.modF ((ObjectProperty.ι fun T : C => ∃ α, W α T) ⋙ Φ.A)) 2), CH.d _ 2 z = 0 → (∀ σ, z σ ∈ (Fil 1).S _) →
    ∀ (b : ∀ i, CH.Cn (CH.modF ((W i).ι ⋙ Φ.A)) 1), (∀ i σ, b i σ ∈ (Fil 1).S _) →
    (∀ i, resB Φ.A (fun T h => ⟨i, h⟩ : W i ≤ fun T : C => ∃ α, W α T) z = CH.d _ 1 (b i)) →
    (∀ h, (CH.cx _).cls (cupPowC ((ObjectProperty.ι fun T : C => ∃ α, W α T) ⋙ Φ.A) z (n + 1)) h = 0) →
    ∀ c : HU (gr Fil ((n : ℤ) + 1)) (capS W Finset.univ) (n + 1),
      Rep ((Fil ((n : ℤ) + 1)).res (capS W Finset.univ).ι) ((Fil ((n : ℤ) + 1 + 1)).res (capS W Finset.univ).ι)
        (cupListC ((capS W Finset.univ).ι ⋙ Φ.A) fun k : Fin (n + 1) =>
          resB Φ.A (capS_le_univ W k.castSucc) (b k.castSucc) - resB Φ.A (capS_le_univ W k.succ) (b k.succ)) c →
      ∃ (ω : ∀ i, HU (gr Fil ((n : ℤ) + 1)) (capS W (Finset.univ.erase i)) (n + 1))
        (f : CH.Cn (CH.modF ((capS W Finset.univ).ι ⋙ Φ.A)) n),
        (∀ σ, f σ ∈ (Fil n).S _) ∧ (∀ σ, CH.d _ n f σ ∈ (Fil ((n : ℤ) + 1)).S _) ∧
        Rep ((Fil ((n : ℤ) + 1)).res (capS W Finset.univ).ι) ((Fil ((n : ℤ) + 1 + 1)).res (capS W Finset.univ).ι)
          (CH.d _ n f) (c - ∑ i, ((resU (gr Fil ((n : ℤ) + 1)) (capS_univ_le W (Finset.univ.erase i))).pull (n + 1)) (ω i)) := by
  intro R _ C _ Φ Fil hF s n W _ _ hS _ z hz hz1 b hb1 hb hcob c hc
  have hWV : ∀ α, W α ≤ (fun T : C => ∃ α, W α T) := fun α T h => ⟨α, h⟩
  have hd := cupPow_d _ z hz (n + 1)
  obtain ⟨u, hu⟩ : cupPowC ((ObjectProperty.ι fun T : C => ∃ α, W α T) ⋙ Φ.A) z (n + 1) ∈
      LinearMap.range (CH.d _ (2 * n + 1)) := ((CrystallineSemistableComparison.P.cls_surj (CH.cx _) _).2.1 _ hd).1 (hcob hd)
  let v : (KK Φ.A W).X 0 (2 * n + 1) := fun i => resB Φ.A (capV hWV i) u
  have hv1 : (KK Φ.A W).dv 0 (2 * n + 1) v = aa hWV z (n + 1) := by
    funext i
    rw [dv_apply]
    change CH.d _ _ (resB Φ.A _ u) = resB Φ.A _ _
    rw [d_resB, hu]
  have hv2 : (KK Φ.A W).dh 0 (2 * n + 1) v = 0 := by
    funext i
    rw [dh_apply, Fin.sum_univ_two]
    have e : resB Φ.A (cap_le W 0 i) (v (fc 0 i)) = resB Φ.A (cap_le W 1 i) (v (fc 1 i)) := rfl
    rw [e, Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul, one_smul, add_neg_cancel]
    rfl
  have hTop : ∀ p q, (dfil (W := W) Fil hF.anti).L 0 p q = ⊤ := fun p q =>
    (Submodule.eq_top_iff'.2 fun x i _ σ => by rw [hF.top 0 le_rfl]; trivial)
  have hPm : PP b hWV z (n + 1) ∈ (dfil (W := W) Fil hF.anti).L ((n : ℤ) + 1) (n + 1) (n + 1) := by
    have h := PP_mem Φ Fil hF b hWV z (fun α σ => hb1 α σ) (n + 1)
    rwa [Nat.cast_succ] at h
  obtain ⟨ω, f, hω, hdω, hf, hP⟩ := zig_stair (BB b) (dfil (W := W) Fil hF.anti) n hTop (fun p q h => KV _ n W p q h)
    (KEx Φ Fil hF W hS) (BB_dh b) (BB_dv b hWV z hb) (aa hWV z) (gg b hWV z) (PP b hWV z)
    (gg_dv b hWV z hz hb) (gg_dh b hWV z) rfl (fun k => rfl) hPm v hv1 hv2
  let tp : Idx (n + 1 + 1) (n + 2) := ⟨id, strictMono_id⟩
  obtain ⟨e, he, hPe⟩ := PP_eq b hWV z (n + 1)
  have hU : capS W Finset.univ ≤ capT W tp.1 := fun T h a => h a (Finset.mem_univ a)
  have hEk : ∀ k : Fin (n + 2), capS W (Finset.univ.erase k) ≤ capT W (fc k tp).1 := fun k T h a =>
    h _ (Finset.mem_erase.2 ⟨Fin.succAbove_ne k a, Finset.mem_univ _⟩)
  have hCl : resB Φ.A hU (PP b hWV z (n + 1) tp) = e • cupListC ((capS W Finset.univ).ι ⋙ Φ.A) fun k : Fin (n + 1) =>
      resB Φ.A (capS_le_univ W k.castSucc) (b k.castSucc) - resB Φ.A (capS_le_univ W k.succ) (b k.succ) := by
    rw [hPe]
    refine (map_zsmul ((rM Φ.A hU).pullC (n + 1)) e _).trans ?_
    have h := res_cupList (A := Φ.A) hU (fun j : Fin (n + 1) => LL b tp j.castSucc j.succ)
    exact congrArg (e • ·) (h.trans (congrArg _ (funext fun j => resB_sub hU _ _)))
  have hP2 : resB Φ.A hU (PP b hWV z (n + 1) tp) = ∑ k : Fin (n + 2), ((-1 : ℤ) ^ (k : ℕ)) •
      resB Φ.A (hU.trans (cap_le W k tp)) (ω (fc k tp)) + ((-1 : ℤ) ^ (n + 1)) • CH.d _ n (resB Φ.A hU (f tp)) := by
    have h := congrFun hP tp
    rw [h]
    change (rM Φ.A hU).pullC (n + 1) ((KK Φ.A W).dh n (n + 1) ω tp + (-1 : ℤ) ^ (n + 1) • CH.d _ n (f tp)) = _
    rw [dh_apply, map_add, map_sum, map_zsmul]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun k _ => ?_) ?_
    · rw [map_zsmul]; rfl
    · rw [d_resB]; rfl
  have hEq := alg_fin e ((-1 : ℤ) ^ (n + 1)) he _ _ _ _ (fun k : Fin (n + 2) => (-1 : ℤ) ^ (k : ℕ)) hCl hP2
  have hd' : CH.d _ n ((e * (-1 : ℤ) ^ (n + 1)) • resB Φ.A hU (f tp)) =
      (e * (-1 : ℤ) ^ (n + 1)) • CH.d _ n (resB Φ.A hU (f tp)) := map_zsmul _ _ _
  have hClm : (cupListC ((capS W Finset.univ).ι ⋙ Φ.A) fun k : Fin (n + 1) =>
      resB Φ.A (capS_le_univ W k.castSucc) (b k.castSucc) - resB Φ.A (capS_le_univ W k.succ) (b k.succ)) ∈
      Lm (Fil ((n : ℤ) + 1)) _ (n + 1) := by
    have h1 : resB Φ.A hU (PP b hWV z (n + 1) tp) ∈ Lm (Fil ((n : ℤ) + 1)) _ (n + 1) := Lm_res _ (hPm tp trivial)
    rw [hCl] at h1
    have h2 := Submodule.smul_of_tower_mem _ e h1
    rwa [smul_smul, he, one_smul] at h2
  have hw : ∀ k : Fin (n + 2), (e * (-1 : ℤ) ^ (k : ℕ)) • resB Φ.A (hEk k) (ω (fc k tp)) ∈ Lm (Fil ((n : ℤ) + 1)) _ (n + 1) :=
    fun k => Submodule.smul_of_tower_mem _ _ (Lm_res _ (hω (fc k tp) trivial))
  have hdw : ∀ k : Fin (n + 2), CH.d _ (n + 1) ((e * (-1 : ℤ) ^ (k : ℕ)) • resB Φ.A (hEk k) (ω (fc k tp))) ∈
      Lm (Fil ((n : ℤ) + 1 + 1)) _ (n + 2) := fun k => by
    rw [map_zsmul, d_resB]
    exact Submodule.smul_of_tower_mem _ _ (Lm_res _ (hdω (fc k tp) trivial))
  have hfm : (e * (-1 : ℤ) ^ (n + 1)) • resB Φ.A hU (f tp) ∈ Lm (Fil (n : ℤ)) _ n :=
    Submodule.smul_of_tower_mem _ _ (Lm_res hU (hf tp trivial))
  refine fin_step Φ Fil n W _ hClm c hc _ hw hdw _ hfm ?_
  have e3 : ∀ k : Fin (n + 2), resB Φ.A (capS_univ_le W (Finset.univ.erase k))
      ((e * (-1 : ℤ) ^ (k : ℕ)) • resB Φ.A (hEk k) (ω (fc k tp))) =
      (e * (-1 : ℤ) ^ (k : ℕ)) • resB Φ.A (hU.trans (cap_le W k tp)) (ω (fc k tp)) := fun k =>
    map_zsmul ((rM Φ.A (capS_univ_le W (Finset.univ.erase k))).pullC (n + 1)) _ _
  simp only [e3]
  rw [hd']
  exact hEq

end GlobalTheory.CompanionTheory.ConeZig
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormAdd
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
noncomputable section
namespace GlobalTheory.CompanionTheory.GrForm

section Abstract
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C]

theorem rep_add {A : C ⥤ CommAlgCat.{0} R} {a b : IdF A} {j : ℕ}
    {z z' z'' : ∀ s : ComposableArrows C j, A.obj (s.obj (Fin.last j))} {c c' : CH.H (sq a b) j}
    (h : ∀ s, z'' s - (z s + z' s) ∈ b.S _) (hc : Rep a b z c) (hc' : Rep a b z' c') :
    Rep a b z'' (c + c') := by
  obtain ⟨f, hf, rfl, e⟩ := hc
  obtain ⟨f', hf', rfl, e'⟩ := hc'
  refine ⟨f + f', by rw [map_add, hf, hf', add_zero], rfl, fun s => ?_⟩
  change (show sqM a b _ from f s).1 + (show sqM a b _ from f' s).1 = _
  rw [e s, e' s, ← map_add]
  refine Ideal.Quotient.eq.2 ?_
  have := (b.S _).neg_mem (h s)
  rwa [neg_sub] at this

theorem rep_neg {A : C ⥤ CommAlgCat.{0} R} {a b : IdF A} {j : ℕ}
    {z z' : ∀ s : ComposableArrows C j, A.obj (s.obj (Fin.last j))} {c : CH.H (sq a b) j}
    (h : ∀ s, z' s - (-z s) ∈ b.S _) (hc : Rep a b z c) : Rep a b z' (-c) := by
  obtain ⟨f, hf, rfl, e⟩ := hc
  refine ⟨-f, by rw [map_neg, hf, neg_zero], rfl, fun s => ?_⟩
  change -(show sqM a b _ from f s).1 = _
  rw [e s, ← map_neg]
  refine Ideal.Quotient.eq.2 ?_
  have := (b.S _).neg_mem (h s)
  rwa [neg_sub] at this

theorem sum_wz_sub {Φ : PDF R C} {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) {d j : ℕ} (u : Fin d → ∀ T : C, Φ.A.obj T)
    (hu : ∀ i {T T' : C} (φ : T ⟶ T'), u i T' - (Φ.A.map φ).hom (u i T) ∈ Φ.J.S T')
    {ι : Type} [Fintype ι] (I : ι → Fin j → Fin d) (s : ComposableArrows C j)
    (y y' : ι → Φ.A.obj (s.obj (Fin.last j))) (h : ∀ i, y i - y' i ∈ Φ.J.S _) :
    ∑ i, wz u (I i) s * y i - ∑ i, wz u (I i) s * y' i ∈ (Fil ((j : ℤ) + 1)).S _ := by
  rw [← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ fun i _ => ?_
  rw [← mul_sub]
  have h1 : y i - y' i ∈ (Fil ((1 : ℕ) : ℤ)).S _ := by
    rw [Nat.cast_one, hF.one]
    exact h i
  have := hF.mul j 1 _ (wz_mem hF u hu (I i) s) h1
  rwa [Nat.cast_add, Nat.cast_one] at this

end Abstract

section Forms
variable {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

theorem lft_add_sub {W : X.Opens} (T : Thick (LL q)) (h : InU W T) (f g : Γ(X, W)) :
    lft W T (f + g) - (lft W T f + lft W T g) ∈ T.J := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_add, lft_spec T h, lft_spec T h, lft_spec T h, map_add, sub_self]

theorem lft_neg_sub {W : X.Opens} (T : Thick (LL q)) (h : InU W T) (f : Γ(X, W)) :
    lft W T (-f) - (-lft W T f) ∈ T.J := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_neg, lft_spec T h, lft_spec T h, map_neg, sub_self]

theorem lift_cocycle {W : X.Opens} {d : ℕ} {t : Fin d → Γ(X, W)} {u : Fin d → ∀ T : Thick (LL q), T.B}
    (hu : IsLift W t u) (P : ObjectProperty (Thick (LL q))) (hP : ∀ T, P T → InU W T) (i : Fin d)
    {T T' : P.FullSubcategory} (φ : T ⟶ T') :
    (show (sP P).A.obj T' from u i T'.obj) - ((sP P).A.map φ).hom (show (sP P).A.obj T from u i T.obj) ∈ (sP P).J.S T' := by
  change u i T'.obj - φ.hom.φ (u i T.obj) ∈ T'.obj.J
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hu i _ (hP _ T'.property), ev_nat φ.hom (hP _ T.property) (hP _ T'.property),
    ← hu i _ (hP _ T.property)]
  exact sub_eq_zero.2 rfl

end Forms

theorem stAdd : StAdd := by
  intro O _ X q W d t u hu P hP r x x' c c' hc hc'
  have hF : IsFil (sP P) (sFil P) := GlobalTheory.CompanionTheory.DPFil.isFil_sFil P
  have hcoc := fun i {T T' : P.FullSubcategory} (φ : T ⟶ T') => lift_cocycle hu P hP i φ
  constructor
  · refine rep_add (fun s => ?_) hc hc'
    have := sum_wz_sub hF (fun i T => u i T.obj) hcoc (fun I : Idx r d => I.1) s
      (fun I => (show (sP P).A.obj (s.obj (Fin.last r)) from lft W (s.obj (Fin.last r)).obj ((x + x') I)))
      (fun I => (show (sP P).A.obj (s.obj (Fin.last r)) from lft W (s.obj (Fin.last r)).obj (x I)) +
        (show (sP P).A.obj (s.obj (Fin.last r)) from lft W (s.obj (Fin.last r)).obj (x' I)))
      (fun I => lft_add_sub _ (hP _ (s.obj (Fin.last r)).property) _ _)
    simpa only [mul_add, Finset.sum_add_distrib] using this
  · refine rep_neg (fun s => ?_) hc
    have := sum_wz_sub hF (fun i T => u i T.obj) hcoc (fun I : Idx r d => I.1) s
      (fun I => (show (sP P).A.obj (s.obj (Fin.last r)) from lft W (s.obj (Fin.last r)).obj ((-x) I)))
      (fun I => -(show (sP P).A.obj (s.obj (Fin.last r)) from lft W (s.obj (Fin.last r)).obj (x I)))
      (fun I => lft_neg_sub _ (hP _ (s.obj (Fin.last r)).property) _)
    simpa only [mul_neg, Finset.sum_neg_distrib] using this

end GlobalTheory.CompanionTheory.GrForm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormExistsOfCocycle
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
noncomputable section
namespace GlobalTheory.CompanionTheory.GrForm

variable {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

theorem lift_sub_mem {W : X.Opens} {P : ObjectProperty (Thick (LL q))} (hP : ∀ T, P T → InU W T) (f : Γ(X, W))
    (v : ∀ T : Thick (LL q), T.B) (hv : ∀ (T : Thick (LL q)) (h : InU W T), Ideal.Quotient.mk T.J (v T) = ev T h f)
    {T T' : P.FullSubcategory} (φ : T ⟶ T') :
    (show (sP P).A.obj T' from v T'.obj) - ((sP P).A.map φ).hom (show (sP P).A.obj T from v T.obj) ∈ (sP P).J.S T' := by
  have h := hP _ T.property
  have h' := hP _ T'.property
  change v T'.obj - φ.hom.φ (v T.obj) ∈ T'.obj.J
  rw [← Ideal.Quotient.eq, hv _ h', ev_nat φ.hom h h' f, ← hv _ h]
  rfl

theorem exists_of_cocycle : StCocycle → StExists := by
  intro hC O _ X q W d t u hu P hP r x
  have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil P
  have hu' : ∀ i {T T' : P.FullSubcategory} (φ : T ⟶ T'),
      (show (sP P).A.obj T' from u i T'.obj) - ((sP P).A.map φ).hom (show (sP P).A.obj T from u i T.obj) ∈ (sP P).J.S T' :=
    fun i _ _ φ => lift_sub_mem hP (t i) (u i) (hu i) φ
  have hy : ∀ (I : Idx r d) {T T' : P.FullSubcategory} (φ : T ⟶ T'),
      (show (sP P).A.obj T' from lft W T'.obj (x I)) -
        ((sP P).A.map φ).hom (show (sP P).A.obj T from lft W T.obj (x I)) ∈ (sP P).J.S T' :=
    fun I _ _ φ => lift_sub_mem hP (x I) (fun T => lft W T (x I)) (fun T h => lft_spec T h (x I)) φ
  choose f hf hz using fun I : Idx r d =>
    hC hF (fun i (T : P.FullSubcategory) => (show (sP P).A.obj T from u i T.obj)) hu'
      (fun T : P.FullSubcategory => (show (sP P).A.obj T from lft W T.obj (x I))) (hy I) I.1
  have hd : CH.d (sq (sFil P r) (sFil P ((r : ℤ) + 1))) r (∑ I, f I) = 0 := by
    rw [map_sum]
    exact Finset.sum_eq_zero fun I _ => hf I
  refine ⟨(CH.cx (sq (sFil P r) (sFil P ((r : ℤ) + 1)))).cls (∑ I, f I) hd, ∑ I, f I, hd, rfl, ?_⟩
  intro s
  have e : (show sqM (sFil P r) (sFil P ((r : ℤ) + 1)) _ from (∑ I, f I) s) =
      ∑ I, (show sqM (sFil P r) (sFil P ((r : ℤ) + 1)) _ from f I s) := Finset.sum_apply _ _ _
  rw [e, AddSubmonoidClass.coe_finset_sum, map_sum]
  exact Finset.sum_congr rfl fun I _ => hz I s

end GlobalTheory.CompanionTheory.GrForm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormLocalOfFrame
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
noncomputable section
namespace GlobalTheory.CompanionTheory.GrForm

theorem rep_congr {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R} {a b : IdF A} {j : ℕ}
    {z z' : ∀ s : ComposableArrows C j, A.obj (s.obj (Fin.last j))} {c : CH.H (sq a b) j}
    (h : ∀ s, z s - z' s ∈ b.S _) (hr : Rep a b z c) : Rep a b z' c := by
  obtain ⟨f, hf, hc, hz⟩ := hr
  exact ⟨f, hf, hc, fun s => (hz s).trans (Ideal.Quotient.eq.2 (h s))⟩

section Frame
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {d : ℕ} (E : Frame Φ d)
  (σ : ∀ T : C, E.D ⟶ T) {t : Fin d → Φ.A.obj E.D} (ht : E.Coords t) {u : Fin d → ∀ T : C, Φ.A.obj T}
  (hu : ∀ i T, (Φ.A.map (σ T)).hom (t i) = u i T)

include ht hu

theorem a_eq (i : Fin d) {T T' : C} (φ : T ⟶ T') : E.a σ i φ = u i T' - (Φ.A.map φ).hom (u i T) := by
  have e : (Φ.A.map (σ T ≫ φ)).hom (t i) = (Φ.A.map φ).hom ((Φ.A.map (σ T)).hom (t i)) := by
    rw [Functor.map_comp]; rfl
  rw [Frame.a, ht, hu, e, hu]

theorem form_eq {j : ℕ} (I : Fin j → Fin d) (x : Φ.A.obj E.D) (s : ComposableArrows C j) :
    E.form σ I x s = wz u I s * (Φ.A.map (σ _)).hom x := by
  unfold Frame.form wz
  refine congrArg (· * _) (Finset.prod_congr rfl fun k _ => ?_)
  rw [a_eq E σ ht hu]

theorem form_sub_mem {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) {r : ℕ} (I : Fin r → Fin d) (x : Φ.A.obj E.D)
    (s : ComposableArrows C r) (l : Φ.A.obj (s.obj (Fin.last r)))
    (hl : (Φ.A.map (σ _)).hom x - l ∈ Φ.J.S _) :
    E.form σ I x s - wz u I s * l ∈ (Fil ((r : ℤ) + 1)).S _ := by
  have hm : ∀ i {T T' : C} (φ : T ⟶ T'), u i T' - (Φ.A.map φ).hom (u i T) ∈ Φ.J.S T' := fun i T T' φ => by
    rw [← a_eq E σ ht hu]
    exact E.mem _ _ _
  have h1 := wz_mem hF u hm I s
  have h2 : (Φ.A.map (σ _)).hom x - l ∈ (Fil ((1 : ℕ) : ℤ)).S _ := by
    simpa [hF.one] using hl
  have h3 := hF.mul r 1 _ h1 h2
  rw [form_eq E σ ht hu, ← mul_sub]
  simpa using h3

end Frame

theorem stLoc : StFrame → KH.LocGr → KH.PolyTf → StLoc := by
  intro hFr hLoc hPoly O _ l s hb X q W d c u hu r hr
  obtain ⟨E, σ, θ, hGr, hbot, hco, hσ, hpt⟩ := hFr l s hb q c u hu
  obtain ⟨Q, hQ⟩ := hPoly (dividedPowersBot O) q (Ideal.Quotient.mk ⊥) l s {W}
  have hF : IsFil (sP (SS q l s W)) (sFil (SS q l s W)) := GlobalTheory.CompanionTheory.DPFil.isFil_sFil (SS q l s W)
  obtain ⟨-, hL⟩ := hLoc Q hF E σ hGr (r : ℤ) (fun r' h => (hQ r' (by omega)).1) r
  obtain ⟨h2, h3⟩ := hL 0 (by simp)
  have hin : ∀ T : (SS q l s W).FullSubcategory, InU W T.obj := fun T => by
    obtain ⟨-, V, hV, h⟩ := T.property
    rwa [Set.mem_singleton_iff.1 hV] at h
  have key : ∀ (y : Idx r d → Γ(X, W)) (z : ComposableArrows (SS q l s W).FullSubcategory r),
      (∑ I : Idx r d, E.form σ I.1 (θ (y I)) z) - (∑ I : Idx r d,
        wz (Φ := sP (SS q l s W)) (fun i T => u i T.obj) I.1 z *
          (show (sP (SS q l s W)).A.obj (z.obj (Fin.last r)) from lft W (z.obj (Fin.last r)).obj (y I))) ∈
        (sFil (SS q l s W) ((r : ℤ) + 1)).S _ := by
    intro y z
    rw [← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ fun I _ => ?_
    refine form_sub_mem E σ hco (u := fun i T => u i T.obj) (fun i T => hσ i T) hF I.1 _ z _ ?_
    have h := hpt _ (hin (z.obj (Fin.last r))) (y I)
    rw [← lft_spec _ (hin (z.obj (Fin.last r))) (y I)] at h
    exact Ideal.Quotient.eq.1 h
  refine ⟨fun cl => ?_, fun x hx => ?_⟩
  · obtain ⟨x, -, hx⟩ := h2 cl
    refine ⟨fun I => θ.symm (x I), ?_⟩
    refine rep_congr (fun z => ?_) hx
    have := key (fun I => θ.symm (x I)) z
    simpa using this
  · have h4 := h3 (fun I => θ (x I)) (fun I => by
      rw [hF.top _ (by simp)]
      trivial) (rep_congr (fun z => by
        have := Ideal.neg_mem_iff _ |>.2 (key x z)
        simpa using this) hx)
    funext I
    have h5 := h4 I
    have e : (sFil (SS q l s W) (((0 : ℕ) : ℤ) + 1)).S E.D = ⊥ := by
      simpa using hbot 1 one_ne_zero
    rw [e] at h5
    exact θ.injective ((Ideal.mem_bot.1 h5).trans (map_zero θ).symm)

end GlobalTheory.CompanionTheory.GrForm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LowDegreeCocyclesLiftToNerveStatement
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.low_degree_cocycles_lift_to_nerve : DictSt → ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), ∃ (u₁ : H1 F ≃ₗ[R] HH F 1) (u₂ : H2 F ≃ₗ[R] HH F 2), IsIdealValuedLiftSystemCocycle F u₁.toLinearMap ∧ IsDegreeTwoComparison F u₂.toLinearMap ∧ (∀ f : Z1 F, ∃ x : Zc F 1, ∀ (T T' : C) (φ : T ⟶ T'), x.1 (ComposableArrows.mk₁ φ) = f.1 T T' φ) ∧ (∀ f : Z2 F, ∃ x : Zc F 2, ∀ (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T''), x.1 (ComposableArrows.mk₂ φ ψ) = f.1 T T' T'' φ ψ) := by
  first | exact @GlobalTheory.CompanionTheory.HopfC.LowDict.dict_low | exact GlobalTheory.CompanionTheory.HopfC.LowDict.dict_low | (intros; apply GlobalTheory.CompanionTheory.HopfC.LowDict.dict_low <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LowDegreeComparisonIndependentOfChoiceStatement
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.low_degree_comparison_independent_of_choice : ∀ {R : Type} [CommRing R] {C C' : Type} [Category.{0} C] [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (F' : C' ⥤ CommAlgCat.{0} R) (m : CoefMap (RingHom.id R) F F') (u₁ : H1 F →ₗ[R] HH F 1) (u₁' : H1 F' →ₗ[R] HH F' 1) (u₂ : H2 F →ₗ[R] HH F 2) (u₂' : H2 F' →ₗ[R] HH F' 2), IsIdealValuedLiftSystemCocycle F u₁ → IsIdealValuedLiftSystemCocycle F' u₁' → IsDegreeTwoComparison F u₂ → IsDegreeTwoComparison F' u₂' → (∀ f : Z1 F, ∃ x : Zc F 1, ∀ (T T' : C) (φ : T ⟶ T'), x.1 (ComposableArrows.mk₁ φ) = f.1 T T' φ) → (∀ f : Z2 F, ∃ x : Zc F 2, ∀ (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T''), x.1 (ComposableArrows.mk₂ φ ψ) = f.1 T T' T'' φ ψ) → (∀ c, u₁' (m.pull1 c) = pullH m 1 (u₁ c)) ∧ (∀ c, u₂' (m.pull2 c) = pullH m 2 (u₂ c)) := by
  first | exact @GlobalTheory.CompanionTheory.HopfC.dictionary_pull | exact GlobalTheory.CompanionTheory.HopfC.dictionary_pull | (intros; apply GlobalTheory.CompanionTheory.HopfC.dictionary_pull <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MonomialFormsBasisStatement
section
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monomial_forms_basis : ∀ {K : Type} [Field K] {n d : ℕ} (a : ℕ), ∃ b : Module.Basis (Gam n d × {D : Finset (E n d) // D.card = a}) K (Om K (Lr K n d) a), ∀ p, b p = monW K p.1 p.2 := by
  first | exact @GlobalTheory.CompanionTheory.SurjectionOntoH4.BasisW.monW_basis | exact GlobalTheory.CompanionTheory.SurjectionOntoH4.BasisW.monW_basis | (intros; apply GlobalTheory.CompanionTheory.SurjectionOntoH4.BasisW.monW_basis <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PoitouTateNineTermExactStatement
section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.S2pt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poitou_tate_nine_term_exact : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 F))) (Av : S → ValuationSubring Ω) (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ) (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M) (hρ : ContAction ρ), ∀ (j : ∀ v : S, H2 ((charRep μ).comp (locFam S Av v)) →ₗ[ZMod (l ^ r)] ZMod (l ^ r)), LocalFiniteness → 0 < r → (∀ v : S, IsPlaceOver (Av v) v.1) → NineTermExact S Av μ j ρ hρ → Finite (H2 ρ) → Finite (H0 (twDual μ ρ)) → Nat.card (Sha2 ρ (locFam S Av) (continuous_locFam S Av)) * Nat.card (∀ v : S, H2 (ρ.comp (locFam S Av v))) = Nat.card (H2 ρ) * Nat.card (H0 (twDual μ ρ)) := by
  first | exact @GlobalTheory.CompanionTheory.PoitouTateCount.card_sha2_mul_card_local_h2 | exact GlobalTheory.CompanionTheory.PoitouTateCount.card_sha2_mul_card_local_h2 | (intros; apply GlobalTheory.CompanionTheory.PoitouTateCount.card_sha2_mul_card_local_h2 <;> assumption)
end

