import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSmulTopOfEntries
section
namespace GlobalTheory.SpanOfResidue

theorem mem_smul_top_of_entries {A : Type} [CommRing A] {r : ℕ} (I : Ideal A)
    (d : Matrix (Fin r) (Fin r) A) (hd : ∀ i j, d i j ∈ I) :
    d ∈ I • (⊤ : Submodule A (Matrix (Fin r) (Fin r) A)) := by
  rw [Matrix.matrix_eq_sum_single d]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  have h : Matrix.single i j (d i j) = d i j • Matrix.single i j (1 : A) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [h]
  exact Submodule.smul_mem_smul (hd i j) Submodule.mem_top

theorem span_eq_top_of_residue {ι A : Type} [CommRing A] [IsLocalRing A] {r : ℕ}
    (f : ι → Matrix (Fin r) (Fin r) A)
    (h : Submodule.span (IsLocalRing.ResidueField A)
      (Set.range fun (i : ι) ↦ Matrix.map (f i)
        (⇑(IsLocalRing.residue A) : A → IsLocalRing.ResidueField A)) = ⊤) :
    Submodule.span A (Set.range f) = ⊤ := by
  have key : ∀ y ∈ Submodule.span (IsLocalRing.ResidueField A)
      (Set.range fun (i : ι) ↦ Matrix.map (f i)
        (⇑(IsLocalRing.residue A) : A → IsLocalRing.ResidueField A)),
      ∃ n ∈ Submodule.span A (Set.range f),
        Matrix.map n (⇑(IsLocalRing.residue A) : A → IsLocalRing.ResidueField A) = y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ⟨f i, Submodule.subset_span ⟨i, rfl⟩, rfl⟩
    | zero =>
      refine ⟨0, Submodule.zero_mem _, ?_⟩
      ext i j
      simp
    | add x y _ _ hx hy =>
      obtain ⟨n, hn, rfl⟩ := hx
      obtain ⟨m, hm, rfl⟩ := hy
      refine ⟨n + m, Submodule.add_mem _ hn hm, ?_⟩
      ext i j
      simp
    | smul c x _ hx =>
      obtain ⟨n, hn, rfl⟩ := hx
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
      refine ⟨a • n, Submodule.smul_mem _ a hn, ?_⟩
      ext i j
      simp
  rw [eq_top_iff]
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal A)
    Module.Finite.fg_top (IsLocalRing.maximalIdeal_le_jacobson _) ?_
  intro x _
  obtain ⟨n, hn, hnx⟩ := key (Matrix.map x (IsLocalRing.residue A)) (h ▸ Submodule.mem_top)
  have hx : x = n + (x - n) := by abel
  rw [hx]
  refine Submodule.add_mem_sup hn (mem_smul_top_of_entries _ _ fun i j => ?_)
  rw [← IsLocalRing.residue_eq_zero_iff, Matrix.sub_apply, map_sub, sub_eq_zero]
  exact (congrFun (congrFun hnx i) j).symm

end GlobalTheory.SpanOfResidue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanIndicatorLowerSetsFinitePoset
section
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory

theorem mem_span_indicator_lowerSets :
    ∀ (X L : Type) [Fintype L] [PartialOrder L] (ρ : X → Option L) (Φ : X → ℂ),
      (∀ x, ρ x = none → Φ x = 0) → (∀ x x', ρ x = ρ x' → Φ x = Φ x') →
      Φ ∈ Submodule.span ℂ {Ψ | ∃ l : L, Ψ = Set.indicator {x | ∃ l', ρ x = some l' ∧ l' ≤ l}
        (fun _ => (1 : ℂ))} := by
  classical
  intro X L _ _ ρ Φ h0 hΦ
  set S := Submodule.span ℂ {Ψ : X → ℂ | ∃ l : L, Ψ = Set.indicator
    {x | ∃ l', ρ x = some l' ∧ l' ≤ l} (fun _ => (1 : ℂ))} with hS
  have key : ∀ l : L, Set.indicator {x | ρ x = some l} (fun _ => (1 : ℂ)) ∈ S := by
    intro l
    induction l using WellFoundedLT.induction with
    | ind l ih =>
      have hsum : Set.indicator {x | ρ x = some l} (fun _ => (1 : ℂ)) =
          Set.indicator {x | ∃ l', ρ x = some l' ∧ l' ≤ l} (fun _ => (1 : ℂ)) -
            ∑ l' ∈ Finset.univ.filter (· < l),
              Set.indicator {x | ρ x = some l'} (fun _ => (1 : ℂ)) := by
        funext x
        simp only [Pi.sub_apply, Finset.sum_apply, Set.indicator_apply, Set.mem_setOf_eq]
        cases hx : ρ x with
        | none => simp
        | some m =>
          have h1 : (∃ l', some m = some l' ∧ l' ≤ l) ↔ m ≤ l := by simp
          simp only [Option.some.injEq, h1]
          rw [Finset.sum_ite_eq]
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          by_cases hml : m = l
          · subst hml; simp
          · by_cases hle : m ≤ l
            · have hlt : m < l := lt_of_le_of_ne hle hml
              simp [hml, hle, hlt]
            · have hlt : ¬ m < l := fun h => hle h.le
              simp [hml, hle, hlt]
      rw [hsum]
      exact S.sub_mem (Submodule.subset_span ⟨l, rfl⟩)
        (S.sum_mem fun l' hl' => ih l' (by simpa using hl'))
  let c : L → ℂ := fun l => if h : ∃ x, ρ x = some l then Φ h.choose else 0
  have hdecomp : Φ = ∑ l, c l • Set.indicator {x | ρ x = some l} (fun _ => (1 : ℂ)) := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, Set.indicator_apply, Set.mem_setOf_eq,
      smul_eq_mul, mul_ite, mul_one, mul_zero]
    cases hx : ρ x with
    | none => simpa using h0 x hx
    | some m =>
      simp only [Option.some.injEq, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      have hex : ∃ y, ρ y = some m := ⟨x, hx⟩
      simp only [c, dif_pos hex]
      exact hΦ _ _ (hx.trans hex.choose_spec.symm)
  rw [hdecomp]
  exact S.sum_mem fun l _ => S.smul_mem _ (key l)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanKilledUnionAverages
section
namespace GlobalTheory

private theorem exists_equivariant_projection_onto_invariant_submodule {G M : Type} [Group G] [Fintype G] [AddCommGroup M]
    [Module ℂ M] (S W : Submodule ℂ M) (π : G → Module.End ℂ M)
    (h1 : ∀ v ∈ S, π 1 v = v)
    (hmul : ∀ g h, ∀ v ∈ S, π (g * h) v = π h (π g v))
    (hWS : W ≤ S) (hW : ∀ g, ∀ w ∈ W, π g w ∈ W) :
    ∃ P : M →ₗ[ℂ] M, (∀ x, P x ∈ W) ∧ (∀ w ∈ W, P w = w) ∧
      (∀ g, ∀ x ∈ S, P (π g x) = π g (P x)) := by
  classical
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl W
  refine ⟨(Fintype.card G : ℂ)⁻¹ • ∑ g, π g⁻¹ ∘ₗ W.projection q hq ∘ₗ π g,
    ?_, ?_, ?_⟩
  · intro x
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply]
    exact W.smul_mem _ (W.sum_mem fun g _ => hW _ _ (Submodule.projection_apply_mem _ _))
  · intro w hw
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply]
    have key : ∀ g : G, π g⁻¹ (W.projection q hq (π g w)) = w := by
      intro g
      rw [Submodule.projection_apply_of_mem_left hq (hW g w hw), ← hmul _ _ w (hWS hw)]
      simp [h1 w (hWS hw)]
    simp only [key, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ]
    rw [smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 Fintype.card_ne_zero), one_smul]
  · intro h x hx
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply, map_smul, map_sum]
    refine congrArg (fun y => (Fintype.card G : ℂ)⁻¹ • y) ?_
    refine Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => ?_
    simp only [Equiv.coe_mulLeft]
    rw [← hmul _ _ x hx, ← hmul _ h _ (hWS (Submodule.projection_apply_mem _ _))]
    simp only [mul_inv_rev, inv_mul_cancel_right]

theorem mem_span_killed_union_averages {G M : Type} [Group G] [Fintype G] [AddCommGroup M]
    [Module ℂ M] (S : Submodule ℂ M) (π : G → Module.End ℂ M)
    (hS : ∀ g, ∀ v ∈ S, π g v ∈ S) (h1 : ∀ v ∈ S, π 1 v = v)
    (hmul : ∀ g h, ∀ v ∈ S, π (g * h) v = π h (π g v))
    (C : Set (G → ℂ)) (hC : ∀ c ∈ C, ∀ x : G, (fun g => c (x * g * x⁻¹)) ∈ C)
    (v : M) (hv : v ∈ S) :
    v ∈ Submodule.span ℂ ({w | w ∈ S ∧ ∀ c ∈ C, ∑ g, c g • π g w = 0} ∪
      {u | ∃ c ∈ C, ∃ w ∈ S, u = ∑ g, c g • π g w}) := by
  classical
  have hAS : ∀ (c : G → ℂ), ∀ w ∈ S, ∑ g, c g • π g w ∈ S := fun c w hw =>
    S.sum_mem fun g _ => S.smul_mem _ (hS g w hw)
  have hWS : Submodule.span ℂ {u | ∃ c ∈ C, ∃ w ∈ S, u = ∑ g, c g • π g w} ≤ S :=
    Submodule.span_le.2 (by rintro u ⟨c, -, w, hw, rfl⟩; exact hAS c w hw)
  have hWst : ∀ h, ∀ u ∈ Submodule.span ℂ {u | ∃ c ∈ C, ∃ w ∈ S, u = ∑ g, c g • π g w},
      π h u ∈ Submodule.span ℂ {u | ∃ c ∈ C, ∃ w ∈ S, u = ∑ g, c g • π g w} := by
    intro h u hu
    have hle : Submodule.span ℂ {u | ∃ c ∈ C, ∃ w ∈ S, u = ∑ g, c g • π g w} ≤
        (Submodule.span ℂ {u | ∃ c ∈ C, ∃ w ∈ S, u = ∑ g, c g • π g w}).comap (π h) := by
      refine Submodule.span_le.2 ?_
      rintro u ⟨c, hc, w, hw, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      refine Submodule.subset_span ⟨fun k => c (h * k * h⁻¹), hC c hc h, π h w, hS h w hw, ?_⟩
      rw [map_sum]
      refine Fintype.sum_equiv (MulAut.conj h⁻¹).toEquiv _ _ fun g => ?_
      simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, inv_inv,
        map_smul]
      rw [show h * (h⁻¹ * g * h) * h⁻¹ = g by group, ← hmul _ _ w hw, ← hmul _ _ w hw,
        show g * h = h * (h⁻¹ * g * h) by group]
    exact hle hu
  obtain ⟨P, hPW, hPid, hPc⟩ := exists_equivariant_projection_onto_invariant_submodule S _ π h1 hmul hWS hWst
  have hPv : P v ∈ S := hWS (hPW v)
  have hPc' : ∀ g, P (π g v) = π g (P v) := fun g => hPc g v hv
  have hkill : v - P v ∈ {w | w ∈ S ∧ ∀ c ∈ C, ∑ g, c g • π g w = 0} := by
    refine ⟨S.sub_mem hv hPv, fun c hc => ?_⟩
    have hA : ∑ g, c g • π g (P v) = P (∑ g, c g • π g v) := by
      simp only [map_sum, map_smul, hPc']
    simp only [map_sub, smul_sub, Finset.sum_sub_distrib, hA]
    rw [hPid _ (Submodule.subset_span ⟨c, hc, v, hv, rfl⟩), sub_self]
  have hsum := Submodule.add_mem _ (Submodule.subset_span (Set.mem_union_left _ hkill))
    (Submodule.span_mono Set.subset_union_right (hPW v))
  rwa [sub_add_cancel] at hsum

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonicDvdXPowCardSubOneExistsRoot
section
open Polynomial IsLocalRing

namespace GlobalTheory

theorem monic_dvd_X_pow_card_sub_one_exists_root :
    ∀ (S : Type) [CommRing S] [HenselianLocalRing S] [Finite (ResidueField S)] (f : S[X]),
      f.Monic → f.natDegree ≠ 0 → f ∣ X ^ (Nat.card (ResidueField S) - 1) - 1 →
        ∃ y : S, f.eval y = 0 := by
  intro S _ _ _ f hmon hdeg hdvd
  classical
  letI : Fintype (ResidueField S) := Fintype.ofFinite _
  have hQ : Nat.card (ResidueField S) = Fintype.card (ResidueField S) := Nat.card_eq_fintype_card
  set Q := Fintype.card (ResidueField S) with hQdef
  set g : (ResidueField S)[X] := f.map (residue S) with hgdef
  have hgm : g.Monic := hmon.map _
  have hgdeg : g.natDegree ≠ 0 := by rw [hgdef, hmon.natDegree_map]; exact hdeg
  have hQ1 : 1 < Q := Fintype.one_lt_card
  have hdvd' : g ∣ X ^ Q - X := by
    have h1 : g ∣ X ^ (Q - 1) - 1 := by
      have := Polynomial.map_dvd (residue S) hdvd
      simpa [hQ, g] using this
    have : (X ^ Q - X : (ResidueField S)[X]) = X * (X ^ (Q - 1) - 1) := by
      conv_lhs => rw [show Q = (Q - 1) + 1 by omega]
      ring
    rw [this]; exact dvd_mul_of_dvd_right h1 _
  have hne : (X ^ Q - X : (ResidueField S)[X]) ≠ 0 :=
    FiniteField.X_pow_card_sub_X_ne_zero (ResidueField S) hQ1
  have hsplit : Splits (X ^ Q - X : (ResidueField S)[X]) := by
    rw [splits_iff_card_roots, FiniteField.roots_X_pow_card_sub_X,
      FiniteField.X_pow_card_sub_X_natDegree_eq (ResidueField S) hQ1]
    simp [Q]
  have hgs : Splits g := hsplit.of_dvd hne hdvd'
  obtain ⟨abar, habar⟩ := hgs.exists_eval_eq_zero
    (by rw [degree_eq_natDegree hgm.ne_zero]; exact_mod_cast hgdeg)
  have hchar : ringChar (ResidueField S) ∣ Q := by
    apply (ringChar.spec (ResidueField S) Q).mp
    exact FiniteField.cast_card_eq_zero (ResidueField S)
  have hsep : (X ^ Q - X : (ResidueField S)[X]).Separable :=
    galois_poly_separable (ringChar (ResidueField S)) Q hchar
  have hgsep := hsep.of_dvd hdvd'
  have hder : eval abar (derivative g) ≠ 0 := by
    have := hgsep.aeval_derivative_ne_zero (S := ResidueField S) (x := abar)
      (by simpa [aeval_def] using habar)
    simpa [aeval_def] using this
  obtain ⟨a, rfl⟩ := residue_surjective abar
  have key : ∀ p : S[X], residue S (p.eval a) = (p.map (residue S)).eval (residue S a) := by
    intro p; rw [eval_map, eval₂_hom]
  obtain ⟨y, hy, -⟩ := HenselianLocalRing.is_henselian f hmon a
    (by rw [← residue_eq_zero_iff, key]; exact habar)
    (by
      rw [← residue_ne_zero_iff_isUnit, key, ← derivative_map]
      exact hder)
  exact ⟨y, hy⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonoidAlgebraExistsRightInvOfMapField
section
namespace GlobalTheory

open MonoidAlgebra

theorem groupAlgebra_coeff_mul_fintype {R G : Type} [CommRing R] [Group G] [Fintype G]
    (x y : MonoidAlgebra R G) (a : G) :
    (x * y).coeff a = ∑ c : G, x.coeff (a * c⁻¹) * y.coeff c := by
  classical
  have hs : ∀ (f : G →₀ R) (g : G → R → R), (∀ i, g i 0 = 0) → f.sum g = ∑ i, g i (f i) :=
    fun f g h => Finsupp.sum_fintype f g h
  rw [MonoidAlgebra.coeff_mul, hs _ _ (fun i => by simp)]
  rw [Finset.sum_congr rfl fun b _ => hs _ _ (fun i => by simp)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  have : ∀ m : G, (m * c = a) ↔ (m = a * c⁻¹) := fun m => eq_mul_inv_iff_mul_eq.symm
  simp_rw [this]
  simp

theorem groupAlgebra_exists_right_inv_of_map {E L G : Type} [Field E] [Field L] [Group G]
    [Fintype G] (j : E →+* L) (x : MonoidAlgebra E G) :
    (∃ v : MonoidAlgebra L G, MonoidAlgebra.mapRingHom G j x * v = 1) →
      ∃ v : MonoidAlgebra E G, x * v = 1 := by
  classical
  rintro ⟨vL, hvL⟩
  let M : Matrix G G E := fun a c => x.coeff (a * c⁻¹)

  have hsurj : Function.Surjective (M.map j).mulVec := by
    intro w
    let y : MonoidAlgebra L G := ofCoeff (Finsupp.equivFunOnFinite.symm w)
    refine ⟨fun c => (vL * y).coeff c, ?_⟩
    funext a
    have h1 : (MonoidAlgebra.mapRingHom G j x * (vL * y)).coeff a = w a := by
      rw [← mul_assoc, hvL, one_mul]
      rfl
    rw [groupAlgebra_coeff_mul_fintype] at h1
    simp only [MonoidAlgebra.coeff_mapRingHom] at h1
    exact h1
  have hU : IsUnit (M.map j) := Matrix.mulVec_surjective_iff_isUnit.1 hsurj
  have hdetL : IsUnit (j M.det) := by
    rw [RingHom.map_det]
    exact (Matrix.isUnit_iff_isUnit_det _).1 hU
  have hdet : M.det ≠ 0 := by
    intro h
    rw [h, map_zero] at hdetL
    exact not_isUnit_zero hdetL
  have hM : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).2 (isUnit_iff_ne_zero.2 hdet)
  obtain ⟨u, hu⟩ := Matrix.mulVec_surjective_iff_isUnit.2 hM
    (fun a => (1 : MonoidAlgebra E G).coeff a)
  refine ⟨ofCoeff (Finsupp.equivFunOnFinite.symm u), ?_⟩
  apply MonoidAlgebra.ext
  ext a
  rw [groupAlgebra_coeff_mul_fintype]
  have := congrFun hu a
  simpa [Matrix.mulVec, dotProduct, M] using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MulVecEqZeroOfSubalgebra
section
namespace GlobalTheory.SubalgebraMulVecZero

theorem mulVec_frac_eq_zero {B : Type} [CommRing B] [IsDomain B] {ι κ : Type} [Fintype ι]
    (A : Matrix κ ι B) (hA : ∀ u : ι → B, A.mulVec u = 0 → u = 0)
    (v : ι → FractionRing B)
    (hv : (A.map (algebraMap B (FractionRing B))).mulVec v = 0) : v = 0 := by
  classical
  obtain ⟨⟨b, hbM⟩, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors B) Finset.univ v
  choose u hu using fun i => hb i (Finset.mem_univ i)
  have hAu : A.mulVec u = 0 := by
    funext k
    apply IsFractionRing.injective B (FractionRing B)
    rw [Pi.zero_apply, map_zero]
    have e : algebraMap B (FractionRing B) (A.mulVec u k) =
        (A.map (algebraMap B (FractionRing B))).mulVec (fun i => algebraMap B (FractionRing B) (u i)) k := by
      simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
    rw [e]
    have e2 : (fun i => algebraMap B (FractionRing B) (u i)) = b • v := funext hu
    rw [e2, Matrix.mulVec_smul, hv, smul_zero]
    rfl
  have hu0 := hA u hAu
  funext i
  have h1 := hu i
  rw [hu0, Pi.zero_apply, map_zero] at h1
  have hb0 : algebraMap B (FractionRing B) b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hbM
  rw [Algebra.smul_def] at h1
  exact (mul_eq_zero.1 h1.symm).resolve_left hb0

theorem exists_left_inv {K : Type} [Field K] {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (A : Matrix κ ι K) (hA : ∀ v : ι → K, A.mulVec v = 0 → v = 0) :
    ∃ N : Matrix ι κ K, N * A = 1 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' A) (by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    exact hA v hv)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have e : LinearMap.toMatrix' (g ∘ₗ Matrix.toLin' A) = LinearMap.toMatrix' g * A := by
    rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin']
  rw [← e, hg, LinearMap.toMatrix'_id]

theorem mulVec_eq_zero_of_subalgebra {O S : Type} [CommRing O] [CommRing S] [IsDomain S]
    [Algebra O S] (B : Subalgebra O S) {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (M : Matrix κ ι S) (hM : ∀ (i : κ) (j : ι), M i j ∈ B)
    (hinj : ∀ v : ι → S, (∀ j, v j ∈ B) → Matrix.mulVec M v = 0 → v = 0)
    (w : ι → S) (hw : Matrix.mulVec M w = 0) : w = 0 := by
  let A : Matrix κ ι B := Matrix.of fun i j => ⟨M i j, hM i j⟩
  let c : B →+* S := B.val.toRingHom
  have hc : Function.Injective c := Subtype.val_injective
  have hAM : A.map c = M := by
    ext i j
    rfl
  have hA : ∀ u : ι → B, A.mulVec u = 0 → u = 0 := by
    intro u hu
    have h1 : M.mulVec (c ∘ u) = 0 := by
      funext i
      rw [← hAM, ← RingHom.map_mulVec, hu]
      simp
    have h2 := hinj (c ∘ u) (fun j => (u j).2) h1
    funext j
    apply hc
    have := congrFun h2 j
    simpa using this
  obtain ⟨N, hN⟩ := exists_left_inv (A.map (algebraMap B (FractionRing B)))
    (mulVec_frac_eq_zero A hA)
  have hL := IsFractionRing.injective S (FractionRing S)
  let g : B →+* FractionRing S := (algebraMap S (FractionRing S)).comp c
  have hg : Function.Injective g := hL.comp hc
  let φ : FractionRing B →+* FractionRing S := IsFractionRing.lift hg
  have hmap : (A.map (algebraMap B (FractionRing B))).map φ
      = M.map (algebraMap S (FractionRing S)) := by
    ext i j
    simp only [Matrix.map_apply]
    exact IsFractionRing.lift_algebraMap hg (A i j)
  have hN' : N.map φ * M.map (algebraMap S (FractionRing S)) = 1 := by
    rw [← hmap, ← Matrix.map_mul, hN]
    exact Matrix.map_one _ (map_zero φ) (map_one φ)
  have hw' : (M.map (algebraMap S (FractionRing S))).mulVec
      ((algebraMap S (FractionRing S)) ∘ w) = 0 := by
    funext i
    rw [← RingHom.map_mulVec, hw]
    simp
  have h0 : (algebraMap S (FractionRing S)) ∘ w = 0 := by
    rw [← Matrix.one_mulVec ((algebraMap S (FractionRing S)) ∘ w), ← hN',
      ← Matrix.mulVec_mulVec, hw', Matrix.mulVec_zero]
  funext j
  apply hL
  have := congrFun h0 j
  simpa using this

end GlobalTheory.SubalgebraMulVecZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MultisetEqOfProdAddEq
section
namespace GlobalTheory.MultisetOfProduct

open Polynomial

theorem eval_prod_neg (m : Multiset ℂ) (u : ℂ) :
    (((m.map (fun x : ℂ => -x)).map (fun a : ℂ => X - C a)).prod).eval u
      = (m.map (fun x : ℂ => u + x)).prod := by
  rw [Polynomial.eval_multiset_prod, Multiset.map_map, Multiset.map_map]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun x _ => ?_)
  simp [sub_neg_eq_add]

theorem multiset_eq_of_prod_add_eq {m m' : Multiset ℂ}
    (h : ∀ (u : ℂ), Multiset.prod (Multiset.map (fun (x : ℂ) ↦ u + x) m)
      = Multiset.prod (Multiset.map (fun (x : ℂ) ↦ u + x) m')) : m = m' := by

  have hp : ((m.map (fun x : ℂ => -x)).map (fun a : ℂ => X - C a)).prod =
      ((m'.map (fun x : ℂ => -x)).map (fun a : ℂ => X - C a)).prod := by
    apply Polynomial.funext
    intro u
    rw [eval_prod_neg, eval_prod_neg]
    exact h u
  have hr := congrArg Polynomial.roots hp
  rw [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at hr
  exact Multiset.map_injective neg_injective hr

end GlobalTheory.MultisetOfProduct
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MultisetManySeparatedPoints
section
open Polynomial
open Classical

namespace GlobalTheory

theorem multiset_many_separated_points : ∀ (K : Type) [NormedAddCommGroup K] (s : Multiset K) (ρ : ℝ) (A B : ℕ), 0 ≤ ρ → 0 < B → A * B ≤ Multiset.card s → (∀ W ∈ s, Multiset.card (s.filter fun z => ‖z - W‖ ≤ ρ) ≤ B) → ∃ Z : Finset K, A ≤ Z.card ∧ (∀ W ∈ Z, W ∈ s) ∧ ∀ W ∈ Z, ∀ W' ∈ Z, W ≠ W' → ρ < ‖W - W'‖ := by
  intro K _ s ρ A B hρ hB hAB hball
  set S := s.toFinset.powerset.filter
    (fun Z : Finset K => ∀ W ∈ Z, ∀ W' ∈ Z, W ≠ W' → ρ < ‖W - W'‖) with hS
  have hne : S.Nonempty := ⟨∅, by simp [hS]⟩
  obtain ⟨Z, hZS, hZmax⟩ := Finset.exists_max_image S Finset.card hne
  rw [hS, Finset.mem_filter, Finset.mem_powerset] at hZS
  obtain ⟨hZsub, hZsep⟩ := hZS
  have hZs : ∀ W ∈ Z, W ∈ s := fun W hW => Multiset.mem_toFinset.mp (hZsub hW)
  have hcov : ∀ z ∈ s, ∃ W ∈ Z, ‖z - W‖ ≤ ρ := by
    intro z hz
    by_contra h
    push_neg at h
    have hzZ : z ∉ Z := by
      intro hzZ
      have := h z hzZ
      simp at this
      linarith
    have hmem : insert z Z ∈ S := by
      rw [hS, Finset.mem_filter, Finset.mem_powerset]
      refine ⟨Finset.insert_subset (Multiset.mem_toFinset.mpr hz) hZsub, ?_⟩
      intro W hW W' hW' hne
      rw [Finset.mem_insert] at hW hW'
      rcases hW with rfl | hW <;> rcases hW' with rfl | hW'
      · exact absurd rfl hne
      · exact h W' hW'
      · rw [norm_sub_rev]; exact h W hW
      · exact hZsep W hW W' hW' hne
    have := hZmax _ hmem
    rw [Finset.card_insert_of_notMem hzZ] at this
    omega
  have hle : s ≤ ∑ W ∈ Z, s.filter (fun z => ‖z - W‖ ≤ ρ) := by
    rw [Multiset.le_iff_count]
    intro a
    rw [Multiset.count_sum']
    by_cases ha : a ∈ s
    · obtain ⟨W, hW, hd⟩ := hcov a ha
      calc Multiset.count a s = Multiset.count a (s.filter (fun z => ‖z - W‖ ≤ ρ)) := by
            rw [Multiset.count_filter_of_pos (p := fun z => ‖z - W‖ ≤ ρ) hd]
        _ ≤ _ := Finset.single_le_sum
            (f := fun W => Multiset.count a (s.filter (fun z => ‖z - W‖ ≤ ρ)))
            (fun _ _ => Nat.zero_le _) hW
    · rw [Multiset.count_eq_zero_of_notMem ha]; exact Nat.zero_le _
  have hcard : Multiset.card s ≤ Z.card * B := by
    calc Multiset.card s ≤ Multiset.card (∑ W ∈ Z, s.filter (fun z => ‖z - W‖ ≤ ρ)) :=
          Multiset.card_le_card hle
      _ = ∑ W ∈ Z, Multiset.card (s.filter (fun z => ‖z - W‖ ≤ ρ)) := by
          simp [map_sum]
      _ ≤ ∑ W ∈ Z, B := Finset.sum_le_sum fun W hW => hball W (hZs W hW)
      _ = Z.card * B := by simp
  exact ⟨Z, Nat.le_of_mul_le_mul_right (hAB.trans hcard) hB, hZs, hZsep⟩

end GlobalTheory
end

