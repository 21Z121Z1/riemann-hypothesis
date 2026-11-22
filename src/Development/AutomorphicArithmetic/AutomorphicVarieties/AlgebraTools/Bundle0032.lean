import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0018
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0028
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0026
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwFactTorus
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0025
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0031
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0022
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0021
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwBruhatKO

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwDomMul
section
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

section SlopeTestRemainingChoices

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem unif_lt {x : kˣ} (hx : IsUnif x) : valuation k (x : k) < 1 := by
  obtain ⟨p, hp, h⟩ := hx
  rw [← h]
  exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.1 hp.not_isUnit

private theorem unif_dec {x : kˣ} (hx : IsUnif x) (y : kˣ) :
    ∃ a : ℤ, valuation k (y : k) = valuation k (x : k) ^ a := by
  obtain ⟨p, hp, h⟩ := hx
  obtain ⟨a, u, hu⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible (K := k) hp y.ne_zero
  refine ⟨a, ?_⟩
  have h1 : valuation k (algebraMap 𝒪[k] k (u : 𝒪[k])) = 1 :=
    (Valuation.integer.integers (valuation k)).valuation_unit u
  rw [hu, h, Units.smul_def, Algebra.smul_def, map_mul, h1, one_mul, map_zpow₀]

private theorem dom_zpow {x : kˣ} (hx : IsUnif x) {a : Fin n → ℤ} (ha : Antitone a) : Dom fun i => x ^ a i := by
  intro i j hij
  have h0 : 0 < valuation k (x : k) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 x.ne_zero)
  simp only [Units.val_zpow_eq_zpow_val, map_zpow₀]
  exact (zpow_le_zpow_iff_right_of_lt_one₀ h0 (unif_lt hx)).2 (ha hij)

private theorem exists_cut (a : Fin n → ℤ) (ha : Antitone a) (c : ℤ) :
    ∃ m ≤ n, ∀ i : Fin n, (i : ℕ) < m ↔ c < a i := by
  classical
  have hex : ∃ m : ℕ, ∀ i : Fin n, m ≤ (i : ℕ) → a i ≤ c := ⟨n, fun i hi => absurd i.2 (not_lt.2 hi)⟩
  refine ⟨Nat.find hex, Nat.find_min' hex fun i hi => absurd i.2 (not_lt.2 hi), fun i => ⟨fun hi => ?_, fun hi => ?_⟩⟩
  · have := Nat.find_min hex hi
    push Not at this
    obtain ⟨j, hj, hc⟩ := this
    exact hc.trans_le (ha (Fin.le_def.2 hj))
  · by_contra h
    exact absurd (Nat.find_spec hex i (not_lt.1 h)) (not_le.2 hi)

private theorem const_central (y : kˣ) : diagT k (Fin n) (fun _ => y) ∈ Subgroup.center (GL (Fin n) k) := by
  rw [Subgroup.mem_center_iff]
  intro g
  ext i j
  simp only [Units.val_mul, val_diagT, mul_diagonal, diagonal_mul, mul_comm]

private theorem unit_norm (C : Subgroup 𝓀[k]ˣ) (u : Fin n → kˣ) (hu : ∀ i, valuation k (u i : k) = 1) :
    diagT k (Fin n) u ∈ Subgroup.normalizer (iwC k n C : Set (GL (Fin n) k)) := by
  obtain ⟨-, -, hn, hv⟩ := memIwC k n C
  have h : diagT k (Fin n) u ∈ iwahori k (Fin n) := by
    rw [← (memIwC k n C).2.1]
    exact Subgroup.mem_sup_right ⟨u, fun i _ => (hv _).2 (hu i), rfl⟩
  rw [Subgroup.mem_set_normalizer_iff]
  intro b
  refine ⟨fun hb => hn _ h b hb, fun hb => ?_⟩
  have := hn _ (inv_mem h) _ hb
  simpa [mul_assoc] using this

end SlopeTestRemainingChoices

theorem UpperTheory.V.AlgebraTools.domMul :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (C : Subgroup 𝓀[k]ˣ) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (ρ : Representation A (GL (Fin n) k) M), (∀ t t' : Fin n → kˣ, Dom t → Dom t' → hk ρ (iwC k n C) (diagT k (Fin n) t) * hk ρ (iwC k n C) (diagT k (Fin n) t') = hk ρ (iwC k n C) (diagT k (Fin n) (t * t'))) ∧ (IsUnit (resCard k : A) → ∀ t : Fin n → kˣ, Dom t → IsUnit (hk ρ (iwC k n C) (diagT k (Fin n) t))) ∧ ∀ (C' : Subgroup 𝓀[k]ˣ) (h : iwC k n C ≤ iwC k n C') (t : Fin n → kˣ), Dom t → hk ρ (iwC k n C) (diagT k (Fin n) t) ∘ₗ inc ρ h = inc ρ h ∘ₗ hk ρ (iwC k n C') (diagT k (Fin n) t) ∧ trc ρ (iwC k n C') (iwC k n C) ∘ₗ hk ρ (iwC k n C) (diagT k (Fin n) t) = hk ρ (iwC k n C') (diagT k (Fin n) t) ∘ₗ trc ρ (iwC k n C') (iwC k n C) := by
  intro k _ _ _ _ n C A M _ _ _ ρ
  have hH := (heckePairIwC k n C).1
  obtain ⟨F, hU, hM, hL, hUI, hLI, hF⟩ := factTorus k n C
  have hmul : ∀ t t' : Fin n → kˣ, Dom t → Dom t' → hk ρ (iwC k n C) (diagT k (Fin n) t) * hk ρ (iwC k n C) (diagT k (Fin n) t') = hk ρ (iwC k n C) (diagT k (Fin n) (t * t')) := by
    intro t t' ht ht'
    rw [map_mul]
    exact (leviMul A _ M ρ _ F _ _ hH ((hF t).2 ht) ((hF t').2 ht') (Or.inl (hF t).1)).2
  refine ⟨hmul, fun hq t ht => ?_, fun C' h t ht => ?_⟩
  · obtain ⟨x, hx⟩ := exists_isUnif (k := k)
    have hfund : ∀ m ≤ n, IsUnit (hk ρ (iwC k n C) (pw x (fund n m))) := by
      intro m hm
      obtain ⟨w, hw⟩ := fundNorm k n C x hx m hm
      obtain ⟨-, -, hu, hx⟩ := hkNorm A _ M ρ _ _ hH hw
      have e : pw x (fund n m) = pm k n w⁻¹ * (pm k n w * pw x (fund n m)) := by
        rw [map_inv, inv_mul_cancel_left]
      rw [e, (hx _).2]
      exact (permUnit k n C A M ρ _ hq).mul hu
    have key : ∀ (c : ℤ) (N : ℕ) (a : Fin n → ℤ), Antitone a → (∀ i, c ≤ a i ∧ a i ≤ c + N) →
        IsUnit (hk ρ (iwC k n C) (diagT k (Fin n) fun i => x ^ a i)) := by
      intro c N
      induction N with
      | zero =>
        intro a _ hb
        have e : (fun i => x ^ a i) = fun _ : Fin n => x ^ c := by
          funext i
          have := hb i
          rw [show a i = c by omega]
        rw [e]
        exact (hkNorm A _ M ρ _ _ hH (Subgroup.center_le_normalizer _ (const_central _))).2.2.1
      | succ N ih =>
        intro a ha hb
        obtain ⟨m, hm, hc⟩ := exists_cut a ha c
        have hfa : Antitone (fund n m) := by
          intro i j hij
          have := Fin.le_def.1 hij
          simp only [fund]
          split_ifs <;> omega
        have ha' : Antitone (a - fund n m) := by
          intro i j hij
          have h1 := ha hij
          have h2 := hc i
          have h3 := hc j
          have h4 := hb i
          have h5 := hb j
          simp only [fund, Pi.sub_apply]
          split_ifs <;> omega
        have hb' : ∀ i, c ≤ (a - fund n m) i ∧ (a - fund n m) i ≤ c + N := by
          intro i
          have h2 := hc i
          have h4 := hb i
          simp only [fund, Pi.sub_apply]
          split_ifs <;> omega
        have e : (fun i => x ^ a i) = (fun i => x ^ (a - fund n m) i) * fun i => x ^ fund n m i := by
          funext i
          simp only [Pi.mul_apply, Pi.sub_apply, ← _root_.zpow_add, sub_add_cancel]
        rw [e, ← hmul _ _ (dom_zpow hx ha') (dom_zpow hx hfa)]
        exact (ih _ ha' hb').mul (hfund m hm)
    choose a hav using fun i => unif_dec hx (t i)
    have h0 : 0 < valuation k (x : k) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 x.ne_zero)
    have ha : Antitone a := by
      intro i j hij
      have := ht i j hij
      rw [hav, hav] at this
      exact (zpow_le_zpow_iff_right_of_lt_one₀ h0 (unif_lt hx)).1 this
    obtain ⟨c, hc⟩ := (Set.finite_range a).bddBelow
    obtain ⟨d, hd⟩ := (Set.finite_range a).bddAbove
    have hk1 := key c (d - c).toNat a ha fun i => by
      have h1 : c ≤ a i := hc ⟨i, rfl⟩
      have h2 : a i ≤ d := hd ⟨i, rfl⟩
      omega
    have hn := unit_norm C (fun i => t i * (x ^ a i)⁻¹) fun i => by
      simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_mul, map_inv₀, map_zpow₀, hav]
      exact mul_inv_cancel₀ (zpow_ne_zero _ h0.ne')
    obtain ⟨-, -, hu, hx⟩ := hkNorm A _ M ρ _ _ hH hn
    have e : t = (fun i => t i * (x ^ a i)⁻¹) * fun i => x ^ a i := by
      funext i
      simp
    rw [e, map_mul, (hx _).1]
    exact hu.mul hk1
  · obtain ⟨F', hU', hM', hL', hUI', hLI', hF'⟩ := factTorus k n C'
    refine leviLevel A _ M ρ _ _ h F' F _ (heckePairIwC k n C').1 hH ((heckePairIwC k n C).2.2 C').1
      (hU.trans hU'.symm) (hM.trans hM'.symm) (hL.trans hL'.symm) ?_ ?_ ?_ ((hF' t).2 ht) ?_
    · rw [hUI', ← hUI]
      exact inf_le_right
    · rw [hLI', ← hLI]
      exact inf_le_right
    · intro a ha b hb
      exact (memIwC k n C).2.2.1 a (((memIwC k n C').1 a).1 ha).1 b hb
    · rintro j ⟨hj, -⟩
      rw [hM'] at hj
      obtain ⟨s, rfl⟩ := hj
      rw [← map_mul, ← map_mul, mul_comm]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwDomSum
section
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

private theorem domSum_reps {G : Type} [Group G] {N I : Subgroup G} (hN : N ≤ I) (d : G) (h : FinOrb I I d) :
    ∃ s : Finset G, (∀ u ∈ s, u ∈ N) ∧ ∀ y ∈ N, ∃! u, u ∈ s ∧ d⁻¹ * (u⁻¹ * y) * d ∈ I := by
  obtain ⟨S, hS, hb⟩ := Set.exists_subset_bijOn (N : Set G) (fun y => ((y * d : G) : G ⧸ I))
  have hq : ((fun y => ((y * d : G) : G ⧸ I)) '' (N : Set G)).Finite := by
    refine h.subset ?_
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨⟨y, hN hy⟩, rfl⟩
  have hf : S.Finite := Set.Finite.of_finite_image (hb.image_eq ▸ hq) hb.injOn
  have key : ∀ u y : G, ((u * d : G) : G ⧸ I) = ((y * d : G) : G ⧸ I) ↔ d⁻¹ * (u⁻¹ * y) * d ∈ I := by
    intro u y
    rw [QuotientGroup.eq]
    have : (u * d)⁻¹ * (y * d) = d⁻¹ * (u⁻¹ * y) * d := by group
    rw [this]
  refine ⟨hf.toFinset, fun u hu => hS (hf.mem_toFinset.1 hu), fun y hy => ?_⟩
  obtain ⟨u, hu, e⟩ := hb.surjOn ⟨y, hy, rfl⟩
  refine ⟨u, ⟨hf.mem_toFinset.2 hu, (key u y).1 e⟩, ?_⟩
  rintro u' ⟨hu', e'⟩
  exact hb.injOn (hf.mem_toFinset.1 hu') hu (((key u' y).2 e').trans e.symm)

private theorem domSum_gen {G : Type} [Group G] {I : Subgroup G} (F : LeviFact I) (d : G) (hI : HeckePair I)
    (hp : F.Pos d) (hn : F.NormJ d) (s : Finset G) (hs : ∀ u ∈ s, u ∈ F.Uf ⊓ I)
    (hs' : ∀ x ∈ F.Uf ⊓ I, ∃! u, u ∈ s ∧ d⁻¹ * (u⁻¹ * x) * d ∈ I)
    (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (ρ : Representation A G M) (v : fixd ρ I) :
    (hk ρ I d v : M) = ∑ u ∈ s, ρ (u * d) v := by
  classical
  have H := leviSum G I F d hI hp {d}
    (fun a ha => ⟨1, one_mem _, 1, one_mem _, by simpa using ha⟩)
    (fun j hj => ⟨d, ⟨Finset.mem_singleton_self d, by simpa [mul_assoc] using (hn j hj).2⟩,
      fun a ha => Finset.mem_singleton.1 ha.1⟩)
    (fun _ => s) (fun a ha => by
      rw [Finset.mem_singleton.1 ha]
      exact ⟨hs, hs'⟩)
  have h2 := (hkApply A G M ρ I I d (hI d)).2.1 (s.image (· * d)) ?_ ?_ v
  · rw [hk, h2, Finset.sum_image (fun a _ b _ h => mul_right_cancel h)]
  · intro y hy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hy
    exact ⟨⟨u, (hs u hu).2⟩, rfl⟩
  · intro q hq
    obtain ⟨⟨a, u⟩, ⟨ha, hu, e⟩, huniq⟩ := (H q).1 hq
    have had : a = d := Finset.mem_singleton.1 ha
    subst had
    refine ⟨u * a, ⟨Finset.mem_image.2 ⟨u, hu, rfl⟩, e⟩, ?_⟩
    rintro y ⟨hy, e'⟩
    obtain ⟨u', hu', rfl⟩ := Finset.mem_image.1 hy
    have := huniq (a, u') ha hu' e'
    rw [show u' = u from (Prod.ext_iff.1 this).2]

theorem UpperTheory.V.AlgebraTools.domSum :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (t : Fin n → kˣ), Dom t → ∃ s : Finset (GL (Fin n) k), (∀ u ∈ s, u ∈ unipO k n) ∧ (∀ y ∈ unipO k n, ∃! u, u ∈ s ∧ (diagT k (Fin n) t)⁻¹ * (u⁻¹ * y) * diagT k (Fin n) t ∈ unipO k n) ∧ ∀ (C : Subgroup 𝓀[k]ˣ) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (ρ : Representation A (GL (Fin n) k) M) (v : fixd ρ (iwC k n C)), (hk ρ (iwC k n C) (diagT k (Fin n) t) v : M) = ∑ u ∈ s, ρ (u * diagT k (Fin n) t) v := by
  intro k _ _ _ _ n t ht
  have key : ∀ (C : Subgroup 𝓀[k]ˣ), ∀ u ∈ unipO k n, ∀ y ∈ unipO k n,
      (diagT k (Fin n) t)⁻¹ * (u⁻¹ * y) * diagT k (Fin n) t ∈ iwC k n C ↔
      (diagT k (Fin n) t)⁻¹ * (u⁻¹ * y) * diagT k (Fin n) t ∈ unipO k n := by
    intro C u hu y hy
    obtain ⟨F, -, -, -, hU, -, hF⟩ := factTorus k n C
    rw [← hU] at hu hy ⊢
    have := F.M_U _ (inv_mem ((hF t).2 ht).1) _ (mul_mem (inv_mem hu.1) hy.1)
    rw [inv_inv] at this
    exact ⟨fun h => ⟨this, h⟩, fun h => h.2⟩
  have hle : unipO k n ≤ iwC k n ⊤ := le_sup_right.trans le_sup_left
  obtain ⟨s, hs, hs'⟩ := domSum_reps hle (diagT k (Fin n) t) ((heckePairIwC k n ⊤).1 _)
  have hs2 : ∀ (C : Subgroup 𝓀[k]ˣ), ∀ y ∈ unipO k n, ∃! u, u ∈ s ∧
      (diagT k (Fin n) t)⁻¹ * (u⁻¹ * y) * diagT k (Fin n) t ∈ iwC k n C := by
    intro C y hy
    refine (existsUnique_congr fun u => and_congr_right fun hu => ?_).1 (hs' y hy)
    rw [key ⊤ u (hs u hu) y hy, key C u (hs u hu) y hy]
  refine ⟨s, hs, fun y hy => ?_, fun C A M _ _ _ ρ v => ?_⟩
  · exact (existsUnique_congr fun u => and_congr_right fun hu => key ⊤ u (hs u hu) y hy).1 (hs' y hy)
  · obtain ⟨F, -, -, -, hU, -, hF⟩ := factTorus k n C
    exact domSum_gen F _ (heckePairIwC k n C).1 ((hF t).2 ht) (hF t).1 s (hU ▸ hs) (hU ▸ hs2 C) A M ρ v
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwSatakeIndep
section
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

section SlopeTestRemainingChoices

variable {A G M : Type} [CommRing A] [Group G] [AddCommGroup M] [Module A M]

private theorem double_coset_operator_sum_orbit (ρ : Representation A G M) (K K' : Subgroup G) (x : G) (h : FinOrb K K' x)
    [Fintype (MulAction.orbit K (x : G ⧸ K'))] (v : fixd ρ K') :
    (hk2 ρ K K' x v : M) = ∑ q : MulAction.orbit K (x : G ⧸ K'), ρ (q : G ⧸ K').out v := by
  rw [(hkApply A G M ρ K K' x h).1 v, dc, finsum_eq_sum_of_fintype, LinearMap.sum_apply]

private noncomputable def permRepBaseCosetVector (A : Type) [CommRing A] (I : Subgroup G) : fixd (permRep A I) I :=
  ⟨MonoidAlgebra.single ((1 : G) : G ⧸ I) 1, fun u hu => by
    rw [Representation.ofMulAction_single]
    congr 1
    change ((u * 1 : G) : G ⧸ I) = _
    exact QuotientGroup.eq.mpr (by simpa using hu)⟩

open Classical in
private theorem satInd_trc {I K : Subgroup G} (h : I ≤ K) (hf : FinOrb K I 1) (g y : G) :
    (permRep A I g (trc (permRep A I) K I (permRepBaseCosetVector A I) : MonoidAlgebra A (G ⧸ I))).coeff (y : G ⧸ I) =
      if g⁻¹ * y ∈ K then 1 else 0 := by
  haveI : Fintype (MulAction.orbit K ((1 : G) : G ⧸ I)) := hf.fintype
  have hv : ((trc (permRep A I) K I (permRepBaseCosetVector A I) : fixd (permRep A I) K) : MonoidAlgebra A (G ⧸ I)) =
      ∑ q : MulAction.orbit K ((1 : G) : G ⧸ I), MonoidAlgebra.single (q : G ⧸ I) (1 : A) := by
    rw [trc, double_coset_operator_sum_orbit _ K I 1 hf]
    refine Finset.sum_congr rfl fun q _ => ?_
    show permRep A I _ (MonoidAlgebra.single ((1 : G) : G ⧸ I) 1) = _
    rw [Representation.ofMulAction_single]
    congr 1
    show (((q : G ⧸ I).out * 1 : G) : G ⧸ I) = _
    rw [mul_one, QuotientGroup.out_eq']
  rw [hv, map_sum, MonoidAlgebra.coeff_sum]
  simp only [Representation.ofMulAction_single, MonoidAlgebra.coeff_single, Finsupp.coe_finset_sum,
    Finset.sum_apply, Finsupp.single_apply]
  have key : ∀ q : MulAction.orbit K ((1 : G) : G ⧸ I),
      (g • (q : G ⧸ I) = (y : G ⧸ I)) ↔ (q : G ⧸ I) = ((g⁻¹ * y : G) : G ⧸ I) := by
    intro q
    rw [smul_eq_iff_eq_inv_smul]
    rfl
  simp only [key]
  by_cases hy : g⁻¹ * y ∈ K
  · rw [if_pos hy]
    have hmem : ((g⁻¹ * y : G) : G ⧸ I) ∈ MulAction.orbit K ((1 : G) : G ⧸ I) :=
      MulAction.mem_orbit_iff.2 ⟨⟨g⁻¹ * y, hy⟩, by
        show (((g⁻¹ * y : G) * 1 : G) : G ⧸ I) = _
        rw [mul_one]⟩
    have e2 : ∀ q : MulAction.orbit K ((1 : G) : G ⧸ I),
        (q : G ⧸ I) = ((g⁻¹ * y : G) : G ⧸ I) ↔ q = ⟨_, hmem⟩ :=
      fun q => ⟨fun hq => Subtype.ext hq, fun hq => by rw [hq]⟩
    simp only [e2]
    rw [Finset.sum_ite_eq']
    simp
  · rw [if_neg hy]
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [if_neg]
    intro hq
    obtain ⟨k, hk⟩ := MulAction.mem_orbit_iff.1 q.2
    have h1 : (((k : G) * 1 : G) : G ⧸ I) = ((g⁻¹ * y : G) : G ⧸ I) := hk.trans hq
    rw [QuotientGroup.eq] at h1
    apply hy
    have := K.mul_mem k.2 (h h1)
    simpa using this

private theorem satInd_abs {I K : Subgroup G} (h : I ≤ K) (hI : HeckePair I) (hf : FinOrb K I 1)
    (e : HkAlg A I) (he : e.1 = inc (permRep A I) h ∘ₗ trc (permRep A I) K I) {ι : Type} (t : ι → G)
    (H : ∀ a b, ∀ i ∈ I, (i * t a)⁻¹ * t b ∈ K → a = b ∧ (i * t a)⁻¹ * t a ∈ I) :
    LinearIndependent A fun a => hT A I (t a) * e := by
  classical
  have key : ∀ a b, (((hT A I (t a) * e).1 (permRepBaseCosetVector A I) : fixd (permRep A I) I) :
      MonoidAlgebra A (G ⧸ I)).coeff ((t b : G) : G ⧸ I) = if a = b then 1 else 0 := by
    intro a b
    haveI : Fintype (MulAction.orbit I ((t a : G) : G ⧸ I)) := (hI (t a)).fintype
    have h1 : (((hT A I (t a) * e).1 (permRepBaseCosetVector A I) : fixd (permRep A I) I) : MonoidAlgebra A (G ⧸ I)) =
        ∑ q : MulAction.orbit I ((t a : G) : G ⧸ I), permRep A I (q : G ⧸ I).out
          ((trc (permRep A I) K I (permRepBaseCosetVector A I) : fixd (permRep A I) K) : MonoidAlgebra A (G ⧸ I)) := by
      show ((hk2 (permRep A I) I I (t a) (e.1 (permRepBaseCosetVector A I)) : fixd (permRep A I) I) :
        MonoidAlgebra A (G ⧸ I)) = _
      rw [double_coset_operator_sum_orbit _ I I (t a) (hI (t a)), he]
      rfl
    rw [h1, MonoidAlgebra.coeff_sum, Finsupp.coe_finset_sum, Finset.sum_apply]
    simp only [satInd_trc h hf]
    have hq : ∀ q : MulAction.orbit I ((t a : G) : G ⧸ I), ((q : G ⧸ I).out⁻¹ * t b ∈ K ↔
        (a = b ∧ q = ⟨((t a : G) : G ⧸ I), MulAction.mem_orbit_self _⟩)) := by
      intro q
      obtain ⟨i, hi⟩ := MulAction.mem_orbit_iff.1 q.2
      have hqi : (((i : G) * t a : G) : G ⧸ I) = (q : G ⧸ I) := hi
      have hout : (((q : G ⧸ I).out : G) : G ⧸ I) = (q : G ⧸ I) := QuotientGroup.out_eq' _
      have hm : ((i : G) * t a)⁻¹ * (q : G ⧸ I).out ∈ I := QuotientGroup.eq.1 (hqi.trans hout.symm)
      constructor
      · intro hK
        have h2 : ((i : G) * t a)⁻¹ * t b ∈ K := by
          have := K.mul_mem (h hm) hK
          simpa [mul_assoc] using this
        obtain ⟨hab, hI'⟩ := H a b i i.2 h2
        refine ⟨hab, Subtype.ext ?_⟩
        show (q : G ⧸ I) = ((t a : G) : G ⧸ I)
        rw [← hqi]
        exact QuotientGroup.eq.2 hI'
      · rintro ⟨rfl, rfl⟩
        have h3 : ((((⟨((t a : G) : G ⧸ I), MulAction.mem_orbit_self _⟩ :
            MulAction.orbit I ((t a : G) : G ⧸ I)) : G ⧸ I).out : G) : G ⧸ I) = ((t a : G) : G ⧸ I) :=
          QuotientGroup.out_eq' _
        exact h (QuotientGroup.eq.1 h3)
    simp only [hq]
    by_cases hab : a = b
    · subst hab
      simp [Finset.sum_ite_eq']
    · simp [hab]
  rw [linearIndependent_iff']
  intro s c hs i hi
  have hc := congrArg (fun z : HkAlg A I => ((z.1 (permRepBaseCosetVector A I) : fixd (permRep A I) I) :
    MonoidAlgebra A (G ⧸ I)).coeff ((t i : G) : G ⧸ I)) hs
  have key2 : ∀ a b, ((((hT A I (t a) : Module.End A (fixd (permRep A I) I)) (e.1 (permRepBaseCosetVector A I))) :
      fixd (permRep A I) I) : MonoidAlgebra A (G ⧸ I)).coeff ((t b : G) : G ⧸ I) = if a = b then 1 else 0 :=
    key
  simp [key2] at hc
  simpa [hi] using hc

end SlopeTestRemainingChoices

private theorem satInd_diag {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} {x : kˣ} (hx : IsUnif x) {a b : Fin n → ℤ} {u : GL (Fin n) k} (hu : u ∈ unipB k (Fin n))
    (h : (pw x a)⁻¹ * u * pw x b ∈ KO k (Fin n)) : a ≤ b := by
  obtain ⟨p, hp, hpx⟩ := hx
  have hx1 : valuation k (x : k) < 1 := by
    rw [← hpx]
    exact (Valuation.Integer.not_isUnit_iff_valuation_lt_one).1 hp.not_isUnit
  obtain ⟨g, hg⟩ := h
  intro i
  by_contra hlt
  have hlt' : b i < a i := lt_of_not_ge hlt
  have hent : (((pw x a)⁻¹ * u * pw x b : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i i =
      ((x ^ (b i - a i) : kˣ) : k) := by
    rw [Units.val_mul, Units.val_mul, pw, pw, ← map_inv, val_diagT, val_diagT, Matrix.mul_diagonal,
      Matrix.diagonal_mul, ((mem_unipB k).1 hu).2 i, mul_one, ← Units.val_mul, _root_.zpow_sub, mul_comm]
    rfl
  have hint : valuation k ((((pw x a)⁻¹ * u * pw x b : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i i) ≤ 1 := by
    rw [← hg]
    exact (g i i).2
  rw [hent] at hint
  obtain ⟨d, hd⟩ : ∃ d : ℕ, a i - b i = (d : ℤ) := ⟨(a i - b i).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  have hd0 : d ≠ 0 := by omega
  have hone : ((x ^ (b i - a i) : kˣ) : k) * (x : k) ^ d = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, ← zpow_natCast, ← hd, ← _root_.zpow_add]
    simp
  have hv := congrArg (valuation k) hone
  rw [map_one, map_mul, map_pow] at hv
  have hlt1 : valuation k (x : k) ^ d < 1 := pow_lt_one₀ zero_le' hx1 hd0
  have := mul_le_of_le_one_left (zero_le' : (0 : ValueGroupWithZero k) ≤ valuation k (x : k) ^ d) hint
  rw [hv] at this
  exact absurd (this.trans_lt hlt1) (lt_irrefl 1)

private theorem satInd_sep {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} {x : kˣ} (hx : IsUnif x) (hle : iwC k n ⊤ ≤ KO k (Fin n)) (a b : {a : Fin n → ℤ // Antitone a})
    (i : GL (Fin n) k) (hi : i ∈ iwC k n ⊤) (hK : (i * pw x a.1)⁻¹ * pw x b.1 ∈ KO k (Fin n)) :
    a = b ∧ (i * pw x a.1)⁻¹ * pw x a.1 ∈ iwC k n ⊤ := by
  have hx' := hx
  obtain ⟨p, hp, hpx⟩ := hx'
  have hx1 : valuation k (x : k) < 1 := by
    rw [← hpx]
    exact (Valuation.Integer.not_isUnit_iff_valuation_lt_one).1 hp.not_isUnit
  have hx0 : (0 : ValueGroupWithZero k) < valuation k (x : k) :=
    zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 x.ne_zero)
  obtain ⟨F, hU, hM, hL, hUI, hLI, hF⟩ := factTorus k n ⊤
  have dom : ∀ c : {a : Fin n → ℤ // Antitone a}, Dom (fun j => x ^ c.1 j) := by
    intro c i j hij
    simp only [Units.val_zpow_eq_zpow_val, map_zpow₀]
    exact zpow_le_zpow_right_of_le_one₀ hx0 hx1.le (c.2 hij)
  have step : ∀ (c d : {a : Fin n → ℤ // Antitone a}) (u m l : GL (Fin n) k),
      u ∈ F.Uf ⊓ iwC k n ⊤ → m ∈ F.Mf ⊓ iwC k n ⊤ → l ∈ F.Lf ⊓ iwC k n ⊤ →
      (pw x c.1)⁻¹ * (u * m * l) * pw x d.1 ∈ KO k (Fin n) →
      (pw x c.1)⁻¹ * u * pw x d.1 ∈ KO k (Fin n) := by
    intro c d u m l hu hm hl hK'
    have h1 : (pw x d.1)⁻¹ * m * pw x d.1 ∈ KO k (Fin n) := hle ((hF _).1 m hm).2
    have h2 : (pw x d.1)⁻¹ * l * pw x d.1 ∈ KO k (Fin n) := hle (((hF _).2 (dom d)).2.2 l hl)
    have e : (pw x c.1)⁻¹ * u * pw x d.1 =
        ((pw x c.1)⁻¹ * (u * m * l) * pw x d.1) * ((pw x d.1)⁻¹ * l * pw x d.1)⁻¹ *
          ((pw x d.1)⁻¹ * m * pw x d.1)⁻¹ := by
      group
    rw [e]
    exact (KO k (Fin n)).mul_mem ((KO k (Fin n)).mul_mem hK' ((KO k (Fin n)).inv_mem h2))
      ((KO k (Fin n)).inv_mem h1)
  obtain ⟨u, hu, m, hm, l, hl, hiu⟩ := F.fact _ ((iwC k n ⊤).inv_mem hi)
  obtain ⟨u', hu', m', hm', l', hl', hiu'⟩ := F.fact _ hi
  have hK1 : (pw x a.1)⁻¹ * (u * m * l) * pw x b.1 ∈ KO k (Fin n) := by
    rw [← hiu]
    simpa [mul_assoc] using hK
  have hK2 : (pw x b.1)⁻¹ * (u' * m' * l') * pw x a.1 ∈ KO k (Fin n) := by
    rw [← hiu']
    have := (KO k (Fin n)).inv_mem hK
    simpa [mul_assoc] using this
  have hUb : ∀ v, v ∈ F.Uf → v ∈ unipB k (Fin n) := fun v hv => hU ▸ hv
  have hab : a.1 ≤ b.1 := satInd_diag hx (hUb u hu.1) (step a b u m l hu hm hl hK1)
  have hba : b.1 ≤ a.1 := satInd_diag hx (hUb u' hu'.1) (step b a u' m' l' hu' hm' hl' hK2)
  obtain rfl : a = b := Subtype.ext (le_antisymm hab hba)
  refine ⟨rfl, ?_⟩
  have hu1 : (pw x a.1)⁻¹ * u * pw x a.1 ∈ KO k (Fin n) := step a a u m l hu hm hl hK1
  have huU : (pw x a.1)⁻¹ * u * pw x a.1 ∈ F.Uf := by
    have := F.M_U _ (F.Mf.inv_mem ((hF _).2 (dom a)).1) u hu.1
    rw [inv_inv] at this
    exact this
  have huI : (pw x a.1)⁻¹ * u * pw x a.1 ∈ iwC k n ⊤ := by
    have hmem : (pw x a.1)⁻¹ * u * pw x a.1 ∈ unipO k n := ⟨hUb _ huU, hu1⟩
    rw [← hUI] at hmem
    exact hmem.2
  have e : (i * pw x a.1)⁻¹ * pw x a.1 =
      ((pw x a.1)⁻¹ * u * pw x a.1) * ((pw x a.1)⁻¹ * m * pw x a.1) * ((pw x a.1)⁻¹ * l * pw x a.1) := by
    rw [_root_.mul_inv_rev, hiu]
    group
  rw [e]
  exact (iwC k n ⊤).mul_mem ((iwC k n ⊤).mul_mem huI ((hF _).1 m hm).2) (((hF _).2 (dom a)).2.2 l hl)

private theorem satInd_gen {A G : Type} [CommRing A] [Group G] {I K : Subgroup G} (h : I ≤ K) (hI : HeckePair I)
    {κ : Type} [Fintype κ] (w : κ → G) (hw : ∀ i, w i ∈ K)
    (hw' : ∀ g ∈ K, ∃! i, ∃ a ∈ I, ∃ b ∈ I, g = a * w i * b) {ι : Type} (t : ι → G)
    (H : ∀ a b, ∀ i ∈ I, (i * t a)⁻¹ * t b ∈ K → a = b ∧ (i * t a)⁻¹ * t a ∈ I) :
    LinearIndependent A fun a => hT A I (t a) * ∑ i, hT A I (w i) := by
  obtain ⟨hf, hsum, -⟩ := hkTrace A G _ (permRep A I) I K h κ w hI hw hw'
  refine satInd_abs h hI hf (∑ i, hT A I (w i)) ?_ t H
  rw [← hsum]
  exact AddSubmonoidClass.coe_finset_sum _ _

theorem UpperTheory.V.AlgebraTools.satakeIndep :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (A : Type) [CommRing A] (x : kˣ), IsUnif x → LinearIndependent A fun a : {a : Fin n → ℤ // Antitone a} => hT A (iwC k n ⊤) (pw x a.1) * ∑ w : Equiv.Perm (Fin n), hT A (iwC k n ⊤) (pm k n w) := by
  intro k _ _ _ _ n A _ x hx
  have hIw : iwC k n ⊤ = iwahori k (Fin n) := (memIwC k n ⊤).2.1
  have hle : iwC k n ⊤ ≤ KO k (Fin n) := by
    rw [hIw]
    exact iwahori_le_KO k (Fin n)
  have hbr := bruhatKO k n
  have hw' : ∀ g ∈ KO k (Fin n), ∃! w : Equiv.Perm (Fin n), ∃ a ∈ iwC k n ⊤, ∃ b ∈ iwC k n ⊤,
      g = a * pm k n w * b := by
    rw [hIw]
    exact hbr.2
  have hsep : ∀ (a b : {a : Fin n → ℤ // Antitone a}), ∀ i ∈ iwC k n ⊤,
      (i * pw x a.1)⁻¹ * pw x b.1 ∈ KO k (Fin n) → a = b ∧ (i * pw x a.1)⁻¹ * pw x a.1 ∈ iwC k n ⊤ :=
    fun a b i hi hK => satInd_sep hx hle a b i hi hK
  exact satInd_gen (A := A) (I := iwC k n ⊤) (K := KO k (Fin n)) hle (heckePairIwC k n ⊤).1
    (pm k n) hbr.1 hw' (fun a : {a : Fin n → ℤ // Antitone a} => pw x a.1) hsep
end

