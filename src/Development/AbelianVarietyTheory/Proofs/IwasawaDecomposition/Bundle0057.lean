import Mathlib
import Formalism.LocalRingCardinality.DataLevel
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0043
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0054
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0055
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyRayDataOfNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0040

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalDualEqAddSpan
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.LocalDualBase

theorem localDual_eq_add_span : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (w : HeightOneSpectrum (𝓞 F)) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (p : 𝓞 E), J = 1 → p ≠ 0 → (∀ x, x ∈ L ↔ ∀ j : Fin n, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = n → p ∣ r)) → (∀ x, σ (σ x) = x) → ∃ e : latS (F := F) (w.adicCompletion F) (intV E w) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J L)), ∀ t : latS (F := F) (w.adicCompletion F) (intV E w) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J L)), ∃ s : intV E w, (t - s • e).1 ∈ latS (F := F) (w.adicCompletion F) (intV E w) L := by
  intro F E _ _ _ _ _ σ w n J L p hJ hp hL _
  subst hJ
  have hform1 : ∀ x y : Fin n → E, hform (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) x y = ∑ i, σ (x i) * y i := by
    intro x y
    unfold hform
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Matrix.one_apply]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨0, fun t => ⟨0, ?_⟩⟩
    have : (t - (0 : intV E w) • (0 : latS (F := F) (w.adicCompletion F) (intV E w)
        (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin 0) (Fin 0) E) L)))).1 = 0 :=
      Subsingleton.elim _ _
    rw [this]
    exact Submodule.zero_mem _

  set R := w.adicCompletion F
  let l : Fin n := ⟨n - 1, by omega⟩
  have hl : l.1 + 1 = n := by simp [l]; omega
  have hσO : ∀ r : 𝓞 E, σ (r : E) ∈ (algebraMap (𝓞 E) E).range := fun r =>
    ⟨⟨σ (r : E), map_isIntegral_int σ (RingOfIntegers.isIntegral_coe r)⟩, rfl⟩
  obtain ⟨pb, hpb⟩ := hσO p
  have hpb0 : (algebraMap (𝓞 E) E pb) ≠ 0 := by
    rw [hpb]
    intro h
    exact hp (by simpa using (map_eq_zero σ).1 h)
  set e0 : Fin n → E := Pi.single l (algebraMap (𝓞 E) E pb)⁻¹ with he0def
  have he0 : e0 ∈ dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) L := by
    intro x hx
    rw [hform1, Finset.sum_eq_single l (by intro b _ hb; simp [e0, hb]) (by simp)]
    obtain ⟨r, hr, hd⟩ := (hL x).1 hx l
    obtain ⟨s, rfl⟩ := hd hl
    obtain ⟨u, hu⟩ := hσO s
    refine ⟨u, ?_⟩
    rw [hu, hr]
    simp only [e0, Pi.single_eq_same]
    push_cast
    rw [map_mul, ← hpb]
    field_simp
  have hglob : ∀ y ∈ Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) L),
      ∃ r : 𝓞 E, y - (algebraMap (𝓞 E) E r) • e0 ∈ L := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      have hxl : Pi.single l (p : E) ∈ L := by
        refine (hL _).2 fun i => ?_
        by_cases h : i = l
        · subst h
          exact ⟨p, by simp, fun _ => dvd_rfl⟩
        · exact ⟨0, by simp [h], fun _ => dvd_zero _⟩
      have h1 := hy _ hxl
      rw [hform1, Finset.sum_eq_single l (by intro b _ hb; simp [hb]) (by simp)] at h1
      simp only [Pi.single_eq_same] at h1
      obtain ⟨r, hr⟩ := h1
      refine ⟨r, (hL _).2 fun j => ?_⟩
      by_cases hj : j = l
      · subst hj
        refine ⟨0, ?_, fun _ => dvd_zero _⟩
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, e0, Pi.single_eq_same, hr, ← hpb]
        push_cast
        field_simp
        ring
      · have hxj : Pi.single j (1 : E) ∈ L := by
          refine (hL _).2 fun i => ?_
          by_cases h : i = j
          · subst h
            exact ⟨1, by simp, fun hi => absurd (Fin.ext (by omega)) hj⟩
          · exact ⟨0, by simp [h], fun _ => dvd_zero _⟩
        have h2 := hy _ hxj
        rw [hform1, Finset.sum_eq_single j (by intro b _ hb; simp [hb]) (by simp)] at h2
        simp only [Pi.single_eq_same, map_one, one_mul] at h2
        obtain ⟨u, hu⟩ := h2
        refine ⟨u, ?_, fun hj' => absurd (Fin.ext (by omega)) hj⟩
        simp [e0, hj, hu]
    | zero => exact ⟨0, by simp⟩
    | add y z _ _ h1 h2 =>
      obtain ⟨r1, hr1⟩ := h1
      obtain ⟨r2, hr2⟩ := h2
      refine ⟨r1 + r2, ?_⟩
      have : y + z - (algebraMap (𝓞 E) E (r1 + r2)) • e0 =
          (y - (algebraMap (𝓞 E) E r1) • e0) + (z - (algebraMap (𝓞 E) E r2) • e0) := by
        rw [map_add, add_smul]; abel
      rw [this]
      exact L.add_mem hr1 hr2
    | smul c y _ h =>
      obtain ⟨r, hr⟩ := h
      refine ⟨c * r, ?_⟩
      have : c • y - (algebraMap (𝓞 E) E (c * r)) • e0 = c • (y - (algebraMap (𝓞 E) E r) • e0) := by
        ext j
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_mul]
        simp only [Algebra.smul_def]
        ring
      rw [this]
      exact L.smul_mem c hr
  have hincl : ∀ r : 𝓞 E, inclE (F := F) R (algebraMap (𝓞 E) E r) ∈ intV E w := by
    intro r
    exact Subring.subset_closure (Or.inl ⟨⟨_, r, rfl⟩, rfl⟩)
  refine ⟨⟨fun i => inclE (F := F) R (e0 i),
    Submodule.subset_span ⟨e0, Submodule.subset_span he0, rfl⟩⟩, fun t => ?_⟩
  obtain ⟨t, ht⟩ := t
  suffices H : ∃ s : intV E w, t - (s : E ⊗[F] R) • (fun i => inclE (F := F) R (e0 i)) ∈
      latS (F := F) R (intV E w) L by
    obtain ⟨s, hs⟩ := H
    exact ⟨s, hs⟩
  induction ht using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨y', hy', rfl⟩ := hy
    obtain ⟨r, hr⟩ := hglob y' hy'
    refine ⟨⟨_, hincl r⟩, ?_⟩
    have : (fun i => inclE (F := F) R (y' i)) - inclE (F := F) R (algebraMap (𝓞 E) E r) •
        (fun i => inclE (F := F) R (e0 i)) =
        fun i => inclE (F := F) R ((y' - (algebraMap (𝓞 E) E r) • e0) i) := by
      ext i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul]
    rw [this]
    exact Submodule.subset_span ⟨_, hr, rfl⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ h1 h2 =>
    obtain ⟨s1, hs1⟩ := h1
    obtain ⟨s2, hs2⟩ := h2
    refine ⟨s1 + s2, ?_⟩
    have : x + y - ((s1 + s2 : intV E w) : E ⊗[F] R) • (fun i => inclE (F := F) R (e0 i)) =
        (x - (s1 : E ⊗[F] R) • (fun i => inclE (F := F) R (e0 i))) +
        (y - (s2 : E ⊗[F] R) • (fun i => inclE (F := F) R (e0 i))) := by
      rw [Subring.coe_add, add_smul]; abel
    rw [this]
    exact Submodule.add_mem _ hs1 hs2
  | smul a x _ h =>
    obtain ⟨s, hs⟩ := h
    refine ⟨a * s, ?_⟩
    have : a • x - ((a * s : intV E w) : E ⊗[F] R) • (fun i => inclE (F := F) R (e0 i)) =
        a • (x - (s : E ⊗[F] R) • (fun i => inclE (F := F) R (e0 i))) := by
      rw [Subring.coe_mul, mul_smul, smul_sub]
      rfl
    rw [this]
    exact Submodule.smul_mem _ a hs

end GlobalTheory.Mem.LocalDualBase
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulVecMemSpanLowerWeightsOfBorelEigenvector
section
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory.AlgWtHW

theorem mulVec_mem_sle_of_isBEig : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ → ∀ (v : ι → ℂ) (lam : Fin n → ℤ), IsBEig Φ v lam → ∀ B : GL (Fin n) ℂ, Φ B *ᵥ v ∈ Sle Φ lam := by
  intro n ι _ _ Φ hΦ v lam hv B
  have hdom : DomLE lam lam := ⟨rfl, fun _ => le_rfl⟩
  have hvS : v ∈ Sle Φ lam := by
    refine Submodule.subset_span ⟨lam, hdom, fun D hD => hv.2 D ?_⟩
    intro a b hab
    exact hD (ne_of_gt hab)

  have hstab : ∀ L : GL (Fin n) ℂ, L.val.BlockTriangular OrderDual.toDual →
      ∀ w ∈ Sle Φ lam, Φ L *ᵥ w ∈ Sle Φ lam := by
    refine GlobalTheory.T.lowerTriangular_GL_complex_induction _ ?_ ?_ ?_ ?_
    · intro w hw; rw [hΦ.one, one_mulVec]; exact hw
    · intro A C hA hC w hw
      rw [hΦ.mul, ← mulVec_mulVec]
      exact hA _ (hC w hw)
    · intro D hD w hw
      refine Submodule.span_induction (p := fun w _ => Φ D *ᵥ w ∈ Sle Φ lam) ?_ ?_ ?_ ?_ hw
      · rintro u ⟨ν, hν, hu⟩
        rw [hu D hD]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨ν, hν, hu⟩)
      · simp
      · intro x y _ _ hx hy; rw [mulVec_add]; exact Submodule.add_mem _ hx hy
      · intro c x _ hx; rw [mulVec_smul]; exact Submodule.smul_mem _ _ hx
    · intro i j s T hji hT w hw
      refine Submodule.span_induction (p := fun w _ => Φ T *ᵥ w ∈ Sle Φ lam) ?_ ?_ ?_ ?_ hw
      · rintro u ⟨ν, hν, hu⟩
        exact GlobalTheory.T.lowerTransvection_mulVec_mem_spanWeightVectorsDominatedBy Φ hΦ lam ν hν u hu i j hji s T hT
      · simp
      · intro x y _ _ hx hy; rw [mulVec_add]; exact Submodule.add_mem _ hx hy
      · intro c x _ hx; rw [mulVec_smul]; exact Submodule.smul_mem _ _ hx

  have hbig : ∀ C : GL (Fin n) ℂ,
      (∀ (k : ℕ) (hk : k ≤ n), (C.val.submatrix (Fin.castLE hk) (Fin.castLE hk)).det ≠ 0) →
      Φ C *ᵥ v ∈ Sle Φ lam := by
    intro C hC
    obtain ⟨L, U, hL, hU, rfl⟩ := GlobalTheory.T.exists_LU_decomposition_of_leading_minors_ne_zero C hC
    rw [hΦ.mul, ← mulVec_mulVec, hv.2 U hU, mulVec_smul]
    exact Submodule.smul_mem _ _ (hstab L hL v hvS)

  refine GlobalTheory.T.polyRep_mulVec_mem_of_cofinite_scalar_shift Φ hΦ _ v B _ (GlobalTheory.T.finite_shifts_vanishing_leading_minor B.val) ?_
  intro s hs C hC
  apply hbig
  rw [hC]
  simpa using hs

end GlobalTheory.AlgWtHW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdLocalValuesGlobalOverPlacesAbove
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat

namespace GlobalTheory.NormCompat

theorem prod_zpow_const {ι B : Type} [CommGroup B] (c : B) (s : Finset ι) (e : ι → ℤ) :
    ∏ i ∈ s, c ^ e i = c ^ (∑ i ∈ s, e i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, ih, zpow_add]

theorem finite_setOf_valuation_ne_one (F : Type) [Field F] [NumberField F] (x : Fˣ) :
    {v : HeightOneSpectrum (𝓞 F) | v.valuation F (x : F) ≠ 1}.Finite := by
  refine ((HeightOneSpectrum.Support.finite (𝓞 F) (x : F)).union
    (HeightOneSpectrum.Support.finite (𝓞 F) ((x : F)⁻¹))).subset ?_
  intro v hv
  have h0 : v.valuation F (x : F) ≠ 0 := by simp
  rcases lt_or_gt_of_ne hv with h | h
  · right
    show 1 < v.valuation F ((x : F)⁻¹)
    rw [map_inv₀]
    exact (one_lt_inv₀ (zero_lt_iff.2 h0)).2 h
  · left
    exact h

theorem valued_locUnit (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (b : Fˣ) :
    Valued.v ((Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom b : (v.adicCompletion F)ˣ) :
      v.adicCompletion F) = v.valuation F (b : F) := by
  show Valued.v ((b : F) : v.adicCompletion F) = _
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _

theorem map_locUnit_eq_zpow {F B : Type} [Field F] [NumberField F] [CommGroup B] (ψ : Ideles F →* B)
    (v : HeightOneSpectrum (𝓞 F)) (hu : ∀ x, IsUnitAt v x → ψ (localIdele F v x) = 1)
    (ϖ : (v.adicCompletion F)ˣ) (hϖ : IsUnifAt v ϖ) (b : Fˣ) :
    ψ (locUnit F v b) = ψ (localIdele F v ϖ) ^ ordF v b := by
  set x : (v.adicCompletion F)ˣ := Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom b with hx
  have hb0 : v.valuation F (b : F) ≠ 0 := by simp
  have hu' : IsUnitAt v (x * ϖ ^ (-ordF v b)) := by
    unfold IsUnitAt
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hx, valued_locUnit, hϖ, ordF, neg_neg,
      ← WithZero.exp_zsmul, ← WithZero.exp_log hb0, ← WithZero.exp_add, WithZero.log_exp]
    simp
  have h := hu _ hu'
  rw [map_mul, map_mul, map_zpow, map_zpow, zpow_neg, mul_inv_eq_one] at h
  rw [locUnit_apply, ← hx]
  exact h

end GlobalTheory.NormCompat

namespace GlobalTheory.NormCompat

theorem under_eq_iff {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
    (w : HeightOneSpectrum (𝓞 K)) (v : HeightOneSpectrum (𝓞 E)) :
    w.under (𝓞 E) = v ↔ w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal := by
  constructor
  · rintro rfl; rfl
  · intro h; exact HeightOneSpectrum.ext h

theorem finite_setOf_under_eq {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
    (v : HeightOneSpectrum (𝓞 E)) : {w : HeightOneSpectrum (𝓞 K) | w.under (𝓞 E) = v}.Finite := by
  have h0 : Ideal.map (algebraMap (𝓞 E) (𝓞 K)) v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)]
    exact v.ne_bot
  refine (Ideal.finite_factors h0).subset fun w hw => ?_
  simp only [Set.mem_setOf_eq] at hw ⊢
  rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, ← (under_eq_iff w v).mp hw]

end GlobalTheory.NormCompat

namespace GlobalTheory.NormCompat

theorem prod_locUnit_eq_prod_locUnit_norm : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] (B : Type) [CommGroup B] (ψ1 : Ideles K →* B) (ψ2 : Ideles E →* B) (S : Finset (HeightOneSpectrum (𝓞 E))), (∀ v ∉ S, ∀ x, IsUnitAt v x → ψ2 (localIdele E v x) = 1) → (∀ v ∉ S, ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal → ∀ x, IsUnitAt w x → ψ1 (localIdele K w x) = 1) → (∀ v ∉ S, ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal → ∀ x ϖ, IsUnifAt w x → IsUnifAt v ϖ → ψ1 (localIdele K w x) = ψ2 (localIdele E v ϖ) ^ w.asIdeal.inertiaDeg (𝓞 E)) → ∀ a : Kˣ, ∃ (TK : Finset (HeightOneSpectrum (𝓞 K))) (TE : Finset (HeightOneSpectrum (𝓞 E))), (∀ w ∈ TK, ∀ v ∈ S, w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) ≠ v.asIdeal) ∧ (∀ w ∉ TK, (∀ v ∈ S, w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) ≠ v.asIdeal) → ψ1 (locUnit K w a) = 1) ∧ (∀ v ∈ TE, v ∉ S) ∧ (∀ v ∉ TE, v ∉ S → ψ2 (locUnit E v (Units.map (Algebra.norm E (S := K)) a)) = 1) ∧ ∏ w ∈ TK, ψ1 (locUnit K w a) = ∏ v ∈ TE, ψ2 (locUnit E v (Units.map (Algebra.norm E (S := K)) a)) := by
  classical
  intro E K _ _ _ _ _ B _ ψ1 ψ2 S h2u h1u h1f a
  set Na : Eˣ := Units.map (Algebra.norm E (S := K)) a with hNa
  have hfinE : ((fun w : HeightOneSpectrum (𝓞 K) => w.under (𝓞 E)) ''
      {w | w.valuation K (a : K) ≠ 1} ∪ {v : HeightOneSpectrum (𝓞 E) | v.valuation E (Na : E) ≠ 1}).Finite :=
    ((finite_setOf_valuation_ne_one K a).image _).union (finite_setOf_valuation_ne_one E Na)
  set TE : Finset (HeightOneSpectrum (𝓞 E)) := hfinE.toFinset.filter (· ∉ S) with hTE
  set TK : Finset (HeightOneSpectrum (𝓞 K)) :=
    TE.biUnion (fun v => (finite_setOf_under_eq (K := K) v).toFinset) with hTK
  have memTK : ∀ w, w ∈ TK ↔ w.under (𝓞 E) ∈ TE := by
    intro w
    simp only [hTK, Finset.mem_biUnion, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    exact ⟨fun ⟨v, hv, h⟩ => h ▸ hv, fun h => ⟨_, h, rfl⟩⟩
  have memTE : ∀ v, v ∈ TE ↔ v ∉ S ∧ ((∃ w : HeightOneSpectrum (𝓞 K), w.valuation K (a : K) ≠ 1 ∧
      w.under (𝓞 E) = v) ∨ v.valuation E (Na : E) ≠ 1) := by
    intro v
    simp only [hTE, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_union, Set.mem_image, Set.mem_setOf_eq]
    exact and_comm
  have hcomap : ∀ w : HeightOneSpectrum (𝓞 K),
      w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = (w.under (𝓞 E)).asIdeal := fun w => rfl
  refine ⟨TK, TE, ?_, ?_, ?_, ?_, ?_⟩
  · intro w hw v hv h
    have := ((memTE _).mp ((memTK w).mp hw)).1
    rw [(under_eq_iff w v).mpr h] at this
    exact this hv
  · intro w hw hS
    have hS' : w.under (𝓞 E) ∉ S := fun h => hS _ h (hcomap w)
    have hval : w.valuation K (a : K) = 1 := by
      by_contra h
      exact hw ((memTK w).mpr ((memTE _).mpr ⟨hS', Or.inl ⟨w, h, rfl⟩⟩))
    rw [locUnit_apply]
    refine h1u _ hS' w (hcomap w) _ ?_
    unfold IsUnitAt
    rw [valued_locUnit, hval]
  · intro v hv
    exact ((memTE v).mp hv).1
  · intro v hv hS
    have hval : v.valuation E (Na : E) = 1 := by
      by_contra h
      exact hv ((memTE v).mpr ⟨hS, Or.inr h⟩)
    rw [locUnit_apply]
    refine h2u v hS _ ?_
    unfold IsUnitAt
    rw [valued_locUnit, hval]
  ·
    set c : HeightOneSpectrum (𝓞 E) → B := fun v => ψ2 (localIdele E v (atFin v (unif v))) with hc
    have hK : ∀ w ∈ TK, ψ1 (locUnit K w a) =
        c (w.under (𝓞 E)) ^ ((w.asIdeal.inertiaDeg (𝓞 E) : ℤ) * ordF w a) := by
      intro w hw
      have hS : w.under (𝓞 E) ∉ S := ((memTE _).mp ((memTK w).mp hw)).1
      rw [map_locUnit_eq_zpow ψ1 w (h1u _ hS w (hcomap w)) _ (unif_spec w),
        h1f _ hS w (hcomap w) _ _ (unif_spec w) (unif_spec _), zpow_mul, zpow_natCast]
    have hE : ∀ v ∈ TE, ψ2 (locUnit E v Na) = c v ^ ordF v Na := by
      intro v hv
      exact map_locUnit_eq_zpow ψ2 v (h2u v ((memTE v).mp hv).1) _ (unif_spec v) Na
    rw [Finset.prod_congr rfl hK, Finset.prod_congr rfl hE,
      ← Finset.prod_fiberwise_of_maps_to (g := fun w : HeightOneSpectrum (𝓞 K) => w.under (𝓞 E))
        (t := TE) (fun w hw => (memTK w).mp hw)]
    refine Finset.prod_congr rfl fun v hv => ?_
    have hfib : ∀ w ∈ TK.filter (fun w => w.under (𝓞 E) = v), c (w.under (𝓞 E)) = c v := by
      intro w hw
      rw [(Finset.mem_filter.mp hw).2]
    rw [Finset.prod_congr rfl fun w hw => by rw [hfib w hw], prod_zpow_const]
    congr 1
    have hs : ∀ w, w ∈ TK.filter (fun w => w.under (𝓞 E) = v) ↔
        w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal := by
      intro w
      rw [Finset.mem_filter, ← under_eq_iff]
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨(memTK w).mpr (h ▸ hv), h⟩
    have key := GlobalTheory.T.intValuation_norm_eq_sum_residueDegree_mul E K v a _ hs
    simp only [ordF, hNa, Units.coe_map, MonoidHom.coe_coe] at key ⊢
    rw [key, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    ring

end GlobalTheory.NormCompat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayLNonvanishingAtOne
section
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder

namespace GlobalTheory.Mem

lemma exists_entire_div_sub_one {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h1 : f 1 = 0) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ s, f s = (s - 1) * g s := by
  refine ⟨dslope f 1, ?_, fun s => ?_⟩
  · rw [← differentiableOn_univ] at hf ⊢
    exact (Complex.differentiableOn_dslope Filter.univ_mem).2 hf
  · have := sub_smul_dslope f 1 s
    rw [h1, sub_zero, smul_eq_mul] at this
    exact this.symm

lemma RayData.LSeries_coef_eq_sum {K : Type} [Field K] [NumberField K] {M : ℕ} (D : RayData K M)
    (χ : D.G →* ℂˣ) (s : ℂ) (h : ∀ c, LSeriesSummable (D.cnt c) s) :
    LSeries (D.coef χ) s = ∑ c, (χ c : ℂ) * LSeries (D.cnt c) s := by
  have e : D.coef χ = ∑ c, (χ c : ℂ) • D.cnt c := by
    funext n
    simp [RayData.coef, Finset.sum_apply]
  rw [e, LSeries_sum (fun c _ => (h c).smul _)]
  simp [LSeries_smul]

theorem rayLSeries_entire_ne_zero_one : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 → ∀ (M : ℕ), 2 ≤ M → ∀ (D : RayData K M) (χ : D.G →* ℂˣ), χ ≠ 1 → ∃ L : ℂ → ℂ, Differentiable ℂ L ∧ L 1 ≠ 0 ∧ ∀ s : ℂ, 1 < s.re → L s = LSeries (D.coef χ) s := by
  intro K _ _ _ hK M hM D χ₀ hχ₀
  classical
  obtain ⟨ρ, -, hZ⟩ := GlobalTheory.T.ray_class_partial_zeta_continuation K hK M hM D
  choose Z hZd hZ1 hZm hZs using hZ
  let Y : (D.G →* ℂˣ) → ℂ → ℂ := fun χ s => ∑ c, (χ c : ℂ) * Z c s
  have hYd : ∀ χ, Differentiable ℂ (Y χ) := fun χ =>
    Differentiable.fun_sum fun c _ => (hZd c).const_mul _
  have hYm : ∀ χ, Y χ (-1) = 0 := fun χ => by simp [Y, hZm]
  have hYs : ∀ χ s, 1 < s.re → Y χ s = (s - 1) * LSeries (D.coef χ) s := by
    intro χ s hs
    rw [D.LSeries_coef_eq_sum χ s fun c => (hZs c s hs).1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [(hZs c s hs).2]; ring
  have hY1 : ∀ χ, χ ≠ 1 → Y χ 1 = 0 := by
    intro χ hχ
    have h0 : ∑ c, (χ c : ℂ) = 0 := by
      have := sum_hom_units_eq_zero ((Units.coeHom ℂ).comp χ) (by
        intro h
        apply hχ
        ext c
        simpa using DFunLike.congr_fun h c)
      simpa using this
    simp only [Y, hZ1]
    rw [← Finset.sum_mul, h0, zero_mul]
  have hL : ∀ χ : D.G →* ℂˣ, ∃ L : ℂ → ℂ, χ ≠ 1 →
      Differentiable ℂ L ∧ ∀ s : ℂ, 1 < s.re → L s = LSeries (D.coef χ) s := by
    intro χ
    by_cases hχ : χ = 1
    · exact ⟨0, fun h => absurd hχ h⟩
    obtain ⟨g, hg, hg'⟩ := exists_entire_div_sub_one (hYd χ) (hY1 χ hχ)
    refine ⟨g, fun _ => ⟨hg, fun s hs => ?_⟩⟩
    have hs1 : s - 1 ≠ 0 := by
      rw [sub_ne_zero]; rintro rfl; simp at hs
    exact mul_left_cancel₀ hs1 ((hg' s).symm.trans (hYs χ s hs))
  choose L hL using hL
  refine ⟨L χ₀, (hL χ₀ hχ₀).1, fun h0 => ?_, (hL χ₀ hχ₀).2⟩
  obtain ⟨g, hg, hg'⟩ := exists_entire_div_sub_one (hL χ₀ hχ₀).1 h0
  haveI : NeZero ((Monoid.exponent D.G : ℕ) : ℂ) := ⟨by exact_mod_cast Monoid.exponent_ne_zero_of_finite⟩
  haveI : Finite (D.G →* ℂˣ) := by
    obtain ⟨e⟩ := CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity D.G ℂ
    exact Finite.of_equiv _ e.toEquiv.symm
  haveI : Fintype (D.G →* ℂˣ) := Fintype.ofFinite _
  obtain ⟨b, hb0, hb1, hba, hbs⟩ := GlobalTheory.T.dedekind_zeta_factorization_ray K M hM D
  let F : ℂ → ℂ := fun s => Y 1 s * (g s * ∏ χ ∈ (Finset.univ.erase 1).erase χ₀, L χ s)
  have hFd : Differentiable ℂ F := by
    refine (hYd 1).mul (hg.mul ?_)
    refine Differentiable.fun_finset_prod fun χ hχ => (hL χ ?_).1
    exact Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hχ)
  have hFs : {s : ℂ | (1 : ℝ) < s.re}.EqOn F (LSeries b) := by
    intro s hs
    have hs' : 1 < s.re := hs
    rw [hbs s hs', ← Finset.mul_prod_erase _ _ (Finset.mem_univ (1 : D.G →* ℂˣ)),
      ← Finset.mul_prod_erase _ _ (Finset.mem_erase.2 ⟨hχ₀, Finset.mem_univ χ₀⟩),
      ← (hL χ₀ hχ₀).2 s hs', hg' s]
    simp only [F]
    rw [hYs 1 s hs', Finset.prod_congr rfl fun χ hχ =>
      (hL χ (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hχ))).2 s hs']
    ring
  have hpos := LSeries.positive_of_differentiable_of_eqOn hb0 hb1 hFd (x := 1)
    (by exact_mod_cast hba) hFs (-1)
  have : F ((-1 : ℝ) : ℂ) = 0 := by
    simp [F, hYm]
  rw [this] at hpos
  exact lt_irrefl _ hpos

end GlobalTheory.Mem
end

