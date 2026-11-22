import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0008
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalFormAtPrime
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0058
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0012
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0011
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ValuedAlgebraMapLtOneIff

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalFormBoundsUnfolding
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

noncomputable section

namespace GlobalTheory.Proof.normal_form_bounds_unfolding

open GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance GlobalTheory.Proof.NormalFormAtPrime

variable {E : Type} [Field E] [NumberField E]

theorem nonneg_of_intAt_zpow {P : HeightOneSpectrum (𝓞 E)} {k : ℤ} (h : IntAt P ((qOf P : E) ^ k)) : 0 ≤ k := by
  by_contra hk
  obtain ⟨m, hm⟩ : ∃ m : ℕ, k = -((m + 1 : ℕ) : ℤ) := ⟨(-k - 1).toNat, by omega⟩
  subst hm
  obtain ⟨r, s, hs, e⟩ := h
  apply hs
  have hq := qOf_ne_zero P
  have e' : s = (qOf P : 𝓞 E) * ((qOf P : 𝓞 E) ^ m * r) := by
    apply RingOfIntegers.ext
    change algebraMap (𝓞 E) E s = algebraMap (𝓞 E) E _
    rw [map_mul, map_mul, map_pow, map_natCast, ← e, zpow_neg, zpow_natCast]
    field_simp
    ring
  rw [e']
  exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)

theorem le_of_zpow_eq {P : HeightOneSpectrum (𝓞 E)} {a b : ℤ} {u : E} (hu : IntAt P u)
    (h : (qOf P : E) ^ a = (qOf P : E) ^ b * u) : b ≤ a := by
  have hq := qOf_ne_zero P
  have : (qOf P : E) ^ (a - b) = u := by
    rw [zpow_sub₀ hq, h]
    field_simp
  have := nonneg_of_intAt_zpow (this ▸ hu)
  omega

theorem intAt_zpow {P : HeightOneSpectrum (𝓞 E)} {k : ℤ} (hk : 0 ≤ k) : IntAt P ((qOf P : E) ^ k) := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk
  simpa using intAt_pow_mul m (intAt_one P)

variable [StarRing E] {n c : ℕ}

omit [NumberField E] [StarRing E] in
theorem inX_natAdd (x : Fin n → E) (b : Fin c) : Loc.inX E n c x (Fin.natAdd n b) = 0 := by
  rw [inX_apply, dif_neg (by simp)]

omit [NumberField E] [StarRing E] in
theorem atN_natAdd (v : Fin (n + c) → E) (b : Fin c) : Loc.atN v (n + b.1) = v (Fin.natAdd n b) := by
  unfold Loc.atN
  rw [dif_pos (by omega)]
  rfl

omit [NumberField E] [StarRing E] in
theorem nfGen_natAdd (q : ℕ) (e : Fin c → ℤ) (z : Fin n → E) (i b : Fin c) :
    nfGen q n c e z i (Fin.natAdd n b) = if b = i then (q : E) ^ e i else 0 := by
  unfold nfGen
  rw [Pi.smul_apply, Pi.add_apply]
  have h0 : (if i.1 = 0 then Loc.inX E n c z else 0 : Fin (n + c) → E) (Fin.natAdd n b) = 0 := by
    split_ifs
    · exact inX_natAdd _ _
    · rfl
  rw [h0]
  simp [Loc.eN, Fin.val_inj]

omit [NumberField E] [StarRing E] in
theorem nfGen_castAdd (q : ℕ) (e : Fin c → ℤ) (z : Fin n → E) (i : Fin c) (a : Fin n) :
    nfGen q n c e z i (Fin.castAdd c a) = if i.1 = 0 then (q : E) ^ e i * z a else 0 := by
  unfold nfGen
  rw [Pi.smul_apply, Pi.add_apply]
  have h0 : Loc.eN E (n + c) (n + i.1) (Fin.castAdd c a) = 0 := by
    unfold Loc.eN
    rw [if_neg (by have := a.2; simp; omega)]
  rw [h0]
  split_ifs
  · rw [inX_castAdd]; simp
  · simp

theorem coords_of_mem {P : HeightOneSpectrum (𝓞 E)} (hc : 1 ≤ c) {e : Fin c → ℤ} {z : Fin n → E} {y : Fin (n + c) → E}
    (hy : y ∈ nfLat P n c e z) :
    (∀ b, ∃ u, IntAt P u ∧ y (Fin.natAdd n b) = (qOf P : E) ^ e b * u) ∧
      ∀ a, IntAt P (y (Fin.castAdd c a) - y (Fin.natAdd n ⟨0, hc⟩) * z a) := by
  obtain ⟨l, hl, s, hs, rfl⟩ := hy
  have h1 : ∀ b, (Loc.inX E n c l + ∑ i, s i • nfGen (qOf P) n c e z i : Fin (n + c) → E) (Fin.natAdd n b) =
      (qOf P : E) ^ e b * s b := by
    intro b
    rw [Pi.add_apply, inX_natAdd, Finset.sum_apply]
    simp [nfGen_natAdd, mul_comm]
  refine ⟨fun b => ⟨s b, hs b, h1 b⟩, fun a => ?_⟩
  rw [h1, Pi.add_apply, inX_castAdd, Finset.sum_apply, Finset.sum_eq_single ⟨0, hc⟩]
  · rw [Pi.smul_apply, nfGen_castAdd, if_pos rfl, smul_eq_mul]
    convert (mem_stdAt_iff l).1 hl a using 1
    ring
  · intro b _ hb
    rw [Pi.smul_apply, nfGen_castAdd, if_neg (fun h => hb (Fin.ext h)), smul_zero]
  · simp

theorem nfGen_mem (P : HeightOneSpectrum (𝓞 E)) (e : Fin c → ℤ) (z : Fin n → E) (i : Fin c) :
    nfGen (qOf P) n c e z i ∈ nfLat P n c e z :=
  ⟨0, zero_mem _, Pi.single i 1, intV_single P i, by simp [Pi.single_apply]⟩

omit [NumberField E] [StarRing E] in
theorem nfGen_mem_Ufl (q : ℕ) (e : Fin c → ℤ) (z : Fin n → E) (i : Fin c) :
    nfGen q n c e z i ∈ Loc.Ufl E n c (i.1 + 1) := by
  unfold nfGen
  refine Submodule.smul_mem _ _ (add_mem (eN_mem_Ufl (by omega)) ?_)
  split_ifs
  · exact inX_mem_Ufl _ _
  · exact zero_mem _

theorem read_normalForm : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) (n' n c j : ℕ), 1 ≤ c → ∀ (e' : ℕ → ℤ) (z' : Fin n' → E) (abelian₂ : Submodule (𝓞 E) (Fin (n + c) → E)) (xj : (Fin n' → E) →ₗ[E] (Fin n → E)) (r : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E)) (e : Fin c → ℤ) (z : Fin n → E), r ∈ Loc.R1 E n c → (∀ i, 1 ≤ i → i ≤ c + 1 → -(j : ℤ) ≤ e' i ∧ e' i ≤ 0) → GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.Bounds P e' z' abelian₂ xj → Loc.inX E n c (xj z') ∈ abelian₂ → r '' (abelian₂ : Set (Fin (n + c) → E)) = GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm.nfLat P n c e z → (∀ i, -((j + 1 : ℕ) : ℤ) ≤ e i ∧ e i ≤ 0) ∧ IntV P z := by
  intro E _ _ _ P n' n c j hc e' z' abelian₂ xj r e z hr he' ⟨⟨f, hf⟩, hb⟩ hz hL
  have hq := qOf_ne_zero P
  have hmem : ∀ v ∈ abelian₂, r v ∈ nfLat P n c e z := fun v hv => hL ▸ Set.mem_image_of_mem r hv
  constructor
  · intro i
    obtain ⟨hs, hlo, hhi⟩ := hf (i.1 + 1) (by omega) (by omega)
    have h1 : f (i.1 + 1) ≤ e i := by
      obtain ⟨v, hv, hrv⟩ : nfGen (qOf P) n c e z i ∈ r '' (abelian₂ : Set (Fin (n + c) → E)) := hL ▸ nfGen_mem P e z i
      have hU : v ∈ Loc.Ufl E n c (i.1 + 1) := by
        have := hr.2.1 _ _ (hrv ▸ nfGen_mem_Ufl (qOf P) e z i)
        change r.symm (r v) ∈ _ at this
        rwa [r.symm_apply_apply] at this
      obtain ⟨u, hu, h⟩ := (hs _).1 ⟨v, hv, hU, rfl⟩
      refine le_of_zpow_eq hu ?_
      rw [← h]
      change _ = Loc.atN v (n + i.1)
      rw [← atN_of_R1cond hr.1 hU, hrv, atN_natAdd, nfGen_natAdd, if_pos rfl]
    have h2 : e i ≤ f (i.1 + 1) := by
      obtain ⟨v, hv, hU, h⟩ := (hs _).2 ⟨1, intAt_one P, rfl⟩
      obtain ⟨u, hu, h'⟩ := (coords_of_mem hc (hmem v hv)).1 i
      refine le_of_zpow_eq hu ?_
      rw [← h', ← atN_natAdd (r v) i, atN_of_R1cond hr.1 hU, ← mul_one (_ ^ _), ← h]
      rfl
    have h3 := (he' (i.1 + 1 + 1) (by omega) (by omega)).1
    have h4 := (he' (i.1 + 1) (by omega) (by omega)).2
    push_cast
    omega
  · obtain ⟨γ, hγ⟩ := exists_res hr
    intro a
    have h1 := (coords_of_mem hc (hmem _ hz)).2 a
    rw [hγ, inX_natAdd, inX_castAdd, zero_mul, sub_zero] at h1
    have h2 := (coords_of_mem hc (hmem _ hb)).2 a
    have h3 : r (adaptedVector E n c 1) = Loc.eN E (n + c) n := hr.1.2.1
    have h4 : Loc.eN E (n + c) n (Fin.castAdd c a) = 0 := by
      unfold Loc.eN
      rw [if_neg (by have := a.2; simp; omega)]
    have h5 : Loc.eN E (n + c) n (Fin.natAdd n ⟨0, hc⟩) = 1 := by simp [Loc.eN]
    rw [map_smul, map_add, hγ, h3] at h2
    simp only [Pi.smul_apply, Pi.add_apply, inX_natAdd, inX_castAdd, h4, h5, smul_eq_mul] at h2
    have h6 := h1.add (intAt_neg ((intAt_zpow (P := P) (k := -e' 1) (by have := (he' 1 le_rfl (by omega)).2; omega)).mul h2))
    convert h6 using 1
    rw [zpow_neg]
    have := zpow_ne_zero (e' 1) hq
    field_simp
    ring

end GlobalTheory.Proof.normal_form_bounds_unfolding
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.OverLatticeIffSelfDualOverBase
section
noncomputable section

namespace GlobalTheory.OverCompare

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions
open scoped TensorProduct
open GlobalTheory.IndefiniteRowSideFullHecke

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι : Type} [Fintype ι] {hc : ι → HCParam R} {C : ColumnChain R ι hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}

theorem localAtT_of_overAt (L : ColLevel R F E sp gp C A clsLat) (N : Submodule (𝓞 E) (Fin R.k → E))
    (v : HeightOneSpectrum (𝓞 F)) (hv : (A.T : 𝓞 F) ∈ v.asIdeal) (H : OverPlaceIntegralForm.OverAt L N v hv) :
    ∃ s, SplittingProjection.LocalAtT L N v hv s := by
  obtain ⟨P, Pb, s, hs, hfac, hker, ⟨iso⟩, hP, hPb, ⟨hle, -, hU⟩, b, φ, e, hfr, hbij, hφ, hrow, -⟩ := H
  have hs' : SplittingProjection.IsSplitting sp.cm.sig v s := ⟨hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1⟩
  have hpart1 : SplittingProjection.partOf (SplittingProjection.prP s) (SplittingProjection.locLat v N) =
      SplittingProjection.partOf (SplittingProjection.prP s) (SplittingProjection.locLat v (SplittingProjection.dualLb L)) :=
    SetLike.coe_injective ((coe_partOf_prP hs' _).trans (hP.trans (coe_partOf_prP hs' _).symm))
  have hpart2 : SplittingProjection.partOf (SplittingProjection.prPbar s) (SplittingProjection.locLat v N) =
      SplittingProjection.partOf (SplittingProjection.prPbar s) (SplittingProjection.locLat v L.Lb) :=
    SetLike.coe_injective ((coe_partOf_prPbar hs' _).trans (hPb.trans (coe_partOf_prPbar hs' _).symm))
  have hb : IsFrame (SplittingProjection.partOf (SplittingProjection.prP s) (SplittingProjection.locLat v N)) b :=
    (isFrame_iff _ _).2 ((coe_partOf_prP hs' _).trans hfr)
  have huniq : ∀ g' : GL (Fin R.k) (v.adicCompletion F),
      ∃! g : UPts sp.cm.sig sp.gram0 (v.adicCompletion F), bc (SplittingProjection.prP s) g.1 = g' :=
    existsUnique_upts sp.cm.sig sp.gram0 sp.baseGram_isHermitian (gram_matrix_det_unit sp) _ s hs'.2.1
  have hlev : ∀ g ∈ UPts sp.cm.sig sp.gram0 (v.adicCompletion F),
      g ∈ levelVL sp.cm.sig sp.gram0 v N ↔ b⁻¹ * bc (SplittingProjection.prP s) g * b ∈
        (bc (n := Fin R.k) (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))).range := by
    intro g hg
    refine ⟨fun h => hbij.mapsTo h, fun h => ?_⟩
    obtain ⟨g', hg', hgg⟩ := hbij.surjOn h
    have h1 : bc (SplittingProjection.prP s) g' = bc (SplittingProjection.prP s) g :=
      mul_left_cancel (mul_right_cancel (show b⁻¹ * bc (SplittingProjection.prP s) g' * b =
        b⁻¹ * bc (SplittingProjection.prP s) g * b from hgg))
    have h2 : (⟨g', hg'.1⟩ : UPts sp.cm.sig sp.gram0 (v.adicCompletion F)) = ⟨g, hg⟩ :=
      (huniq (bc (SplittingProjection.prP s) g)).unique h1 rfl
    have h3 : g' = g := congrArg Subtype.val h2
    exact h3 ▸ hg'
  have hstab : ∀ g ∈ UPts sp.cm.sig sp.gram0 (v.adicCompletion F),
      g ∈ levelVL sp.cm.sig sp.gram0 v N ↔
        bc (SplittingProjection.prP s) g ∈ stabGL (SplittingProjection.partOf (SplittingProjection.prP s) (SplittingProjection.locLat v N)) :=
    fun g hg => (hlev g hg).trans (hb.mem_stabGL_iff _).symm
  obtain ⟨f, hf⟩ := hb.exists_fun φ
  let ε : L.fM v hv ≃+ IsLocalRing.ResidueField (v.adicCompletionIntegers F) := e
  have hfe : ∀ (x : SplittingProjection.locLat v (SplittingProjection.dualLb L))
      (y : SplittingProjection.partOf (SplittingProjection.prP s) (SplittingProjection.locLat v N)),
      (∀ i, y.1 i = SplittingProjection.prP s (x.1 i)) → f y = ε (L.fT v hv x) := by
    intro x y hxy
    obtain ⟨z, hz⟩ := hb.exists_coord y
    exact (hf y z hz).trans (hrow x z ((funext hxy).symm.trans hz)).symm
  have hlift : ∀ y : SplittingProjection.partOf (SplittingProjection.prP s) (SplittingProjection.locLat v N),
      ∃ x : SplittingProjection.locLat v (SplittingProjection.dualLb L), ∀ i, y.1 i = SplittingProjection.prP s (x.1 i) := by
    intro y
    obtain ⟨x, hx, hxy⟩ := (mem_partOf _ (sur_prP hs') _ y.1).1 (hpart1.le y.2)
    exact ⟨⟨x, hx⟩, fun i => (congrFun hxy i).symm⟩
  have hf0 : f ≠ 0 := (hf.ne_zero_iff hb).2 hφ
  have hsm : ∀ (a : intV E v) (a' : v.adicCompletionIntegers F),
      (a' : v.adicCompletion F) = SplittingProjection.prP s a →
      ∀ (x : SplittingProjection.locLat v (SplittingProjection.dualLb L))
      (y : SplittingProjection.partOf (SplittingProjection.prP s) (SplittingProjection.locLat v N)),
      (∀ i, y.1 i = SplittingProjection.prP s (x.1 i)) → f (a' • y) = ε (L.fT v hv (a • x)) := by
    intro a a' ha x y hxy
    refine hfe _ _ fun i => ?_
    show (a' : v.adicCompletion F) * y.1 i = SplittingProjection.prP s ((a : E ⊗[F] v.adicCompletion F) * x.1 i)
    rw [map_mul, ha, hxy]
  refine ⟨s, hs', fun x hx => hfac x (funext hx), ?_, hpart1, hpart2, huniq, hstab, ⟨b, hb, hlev⟩,
    f, ε, ?_, hfe, hf0, ?_, ?_, ?_⟩
  · rw [← (map_primes hs).1, ← (map_primes hs).2]
    exact ⟨iso⟩
  · intro a a' ha m
    obtain ⟨y, hy⟩ := surjective_of_ne_zero hf0 (ε m)
    obtain ⟨x, hx⟩ := hlift y
    have hm : m = L.fT v hv x := ε.injective (hy.symm.trans (hfe x y hx))
    rw [← hy, ← map_smul, hsm a a' ha x y hx, hm, (L.fT v hv).map_smul]
  · intro y
    obtain ⟨x, hx⟩ := hlift y
    rw [hsm (A.T : intV E v) (A.T : v.adicCompletionIntegers F) (by simp) x y hx, L.fT_T, map_zero]
  · intro y
    obtain ⟨x, hx⟩ := hlift y
    rw [hfe x y hx, map_eq_zero_iff _ ε.injective, hker x, ← SetLike.mem_coe, coe_partOf_prP hs',
      show y.1 = OverPlaceIntegralForm.pr₁ s x.1 from funext hx]
  · intro g
    rw [hU, Subgroup.mem_inf]
    refine and_congr_right fun hg => ?_
    exact mem_stabFun_iff_part (SplittingProjection.prP s) _ _ (mem_partOf _ (sur_prP hs') _) _ f ε
      (fun x y hxy => hfe (Submodule.inclusion hle x) y hxy) g hg.2 ((hstab g hg.1).1 hg)

theorem overAt_of_localAtT (L : ColLevel R F E sp gp C A clsLat) (N : Submodule (𝓞 E) (Fin R.k → E))
    (hN : N ≤ SplittingProjection.dualLb L)
    (v : HeightOneSpectrum (𝓞 F)) (hv : (A.T : 𝓞 F) ∈ v.asIdeal)
    (s : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
    (H : SplittingProjection.LocalAtT L N v hv s) : OverPlaceIntegralForm.OverAt L N v hv := by
  obtain ⟨hs', hfac, ⟨iso⟩, hpart1, hpart2, huniq, hstab, ⟨b, hb, hlev⟩, f, ε, -, hfe, hf0, -, hker,
    hU⟩ := H
  replace hb : IsFrame (SplittingProjection.partOf (SplittingProjection.prP s) (SplittingProjection.locLat v N)) b := hb
  obtain ⟨P, Pb, hs⟩ := exists_primes sp.cm.deg2 hs'
  obtain ⟨φ, hf⟩ := hb.exists_row f
  have hle : OverPlaceIntegralForm.latV v N ≤ OverPlaceIntegralForm.latV v (OverPlaceIntegralForm.baseDual L) :=
    Submodule.span_mono (Set.image_mono hN)
  have hmem : ∀ x : SplittingProjection.locLat v (SplittingProjection.dualLb L),
      OverPlaceIntegralForm.pr₁ s x.1 ∈ SplittingProjection.partOf (SplittingProjection.prP s) (SplittingProjection.locLat v N) := fun x => by
    rw [hpart1]
    exact Submodule.subset_span ⟨x.1, x.2, rfl⟩
  refine ⟨P, Pb, s, hs, fun x hx => hfac x (congrFun hx), ?_, ?_, ?_, ?_, ⟨hle, ?_, ?_⟩, b, φ, ε,
    ?_, ⟨?_, ?_, ?_⟩, (hf.ne_zero_iff hb).1 hf0, ?_, ?_⟩
  · intro x
    rw [← coe_partOf_prP hs', SetLike.mem_coe, ← map_eq_zero_iff _ ε.injective,
      ← hfe x ⟨_, hmem x⟩ (fun _ => rfl)]
    exact hker _
  · rw [(map_primes hs).1, (map_primes hs).2]
    exact ⟨iso⟩
  · rw [← coe_partOf_prP hs', ← coe_partOf_prP hs', hpart1]
  · rw [← coe_partOf_prPbar hs', ← coe_partOf_prPbar hs', hpart2]
  · intro h0
    apply hf0
    ext y
    obtain ⟨x, hx, hxy⟩ := (mem_partOf _ (sur_prP hs') _ y.1).1 y.2
    have h1 := hfe (Submodule.inclusion hle ⟨x, hx⟩) y (fun i => (congrFun hxy i).symm)
    have h2 : L.fT v hv (Submodule.inclusion hle ⟨x, hx⟩) = 0 := LinearMap.congr_fun h0 ⟨x, hx⟩
    rw [h1, h2, map_zero, LinearMap.zero_apply]
  · ext g
    rw [hU, Subgroup.mem_inf]
    refine and_congr_right fun hg => ?_
    exact (mem_stabFun_iff_part (SplittingProjection.prP s) _ _ (mem_partOf _ (sur_prP hs') _) _ f ε
      (fun x y hxy => hfe (Submodule.inclusion hle x) y hxy) g hg.2 ((hstab g hg.1).1 hg)).symm
  · exact (coe_partOf_prP hs' _).symm.trans ((isFrame_iff _ _).1 hb)
  · exact fun g hg => (hlev g hg.1).1 hg
  · intro g hg g' hg' hgg
    have h1 : bc (SplittingProjection.prP s) g = bc (SplittingProjection.prP s) g' :=
      mul_left_cancel (mul_right_cancel (show b⁻¹ * bc (SplittingProjection.prP s) g * b =
        b⁻¹ * bc (SplittingProjection.prP s) g' * b from hgg))
    have h2 : (⟨g, hg.1⟩ : UPts sp.cm.sig sp.gram0 (v.adicCompletion F)) = ⟨g', hg'.1⟩ :=
      (huniq (bc (SplittingProjection.prP s) g')).unique h1 rfl
    exact congrArg Subtype.val h2
  · intro u hu
    obtain ⟨g, hg, -⟩ := huniq (b * u * b⁻¹)
    have h1 : b⁻¹ * bc (SplittingProjection.prP s) g.1 * b = u := by rw [hg]; group
    exact ⟨g.1, (hlev g.1 g.2).2 (h1 ▸ hu), h1⟩
  · intro x y hxy
    exact (hfe x ⟨_, hmem x⟩ (fun _ => rfl)).symm.trans (hf _ y hxy)
  · intro g hg
    refine (hU g).trans (Iff.trans ⟨fun h => h.2, fun h => ⟨(hstab g hg).2 h.1, h⟩⟩ ?_)
    exact hf.mem_stabFun_iff hb _

theorem isOverLattice_iff (L : ColLevel R F E sp gp C A clsLat) (N : Submodule (𝓞 E) (Fin R.k → E)) :
    OverPlaceIntegralForm.IsOverLattice L N ↔
      (SplittingProjection.IsOverLattice L N ∧
        (∀ (v : HeightOneSpectrum (𝓞 F)) (h : (A.T : 𝓞 F) ∈ v.asIdeal),
          ∃ φ, SplittingProjection.LocalAtT L N v h φ) ∧
        (∀ v, L.Uloc v ≤ levelVL sp.cm.sig sp.gram0 v N) ∧
        L.U ≤ levelAfL sp.cm.sig sp.gram0 N) := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    refine ⟨⟨h1, h2, h3, h4, fun x hx => Submodule.subset_span (h5 hx), h6⟩,
      fun v hv => localAtT_of_overAt L N v hv (h7 v hv), fun v => ?_, h8⟩
    by_cases hv : (A.T : 𝓞 F) ∈ v.asIdeal
    · obtain ⟨P, Pb, s, -, -, -, -, -, -, ⟨hle, -, hU⟩, -⟩ := h7 v hv
      rw [hU]; exact inf_le_left
    · have : levelVL sp.cm.sig sp.gram0 v N = levelVL sp.cm.sig sp.gram0 v L.Lb :=
        congrArg (level _ _) (h6 v hv)
      rw [this]; exact L.Uloc_lev v
  · rintro ⟨⟨h1, h2, h3, h4, h5, h6⟩, h7, -, h8⟩
    refine ⟨h1, h2, h3, h4, fun y hy x hx => ?_, h6, fun v hv => ?_, h8⟩
    · rw [← h3] at hy
      exact hy x (h4 hx)
    · obtain ⟨s, hs⟩ := h7 v hv
      exact overAt_of_localAtT L N h5 v hv s hs

theorem overLatticeAt_iff (D : D7) (Lv : LevelData D) (u : D.what₂.Word) :
    OverPlaceIntegralForm.OverLatticeAt D Lv u ↔
      (letI := D.host.cmStar
       Formalism.MainNotions.StandardLattice.SplitsF D (D.mem u).A.T → SplittingProjection.HasOverLattice (Lv u)) := by
  letI := D.host.cmStar
  exact imp_congr_right fun _ => and_congr_right fun _ =>
    exists_congr fun N => isOverLattice_iff (Lv u) N

theorem overLattice_iff_selfDualOverBase : OverPlaceIntegralForm.OverLattice ↔ SplittingProjection.SelfDualOverBase :=
  forall_congr' fun D => forall_congr' fun Lv => forall_congr' fun u => overLatticeAt_iff D Lv u

end GlobalTheory.OverCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ParahoricLeIntegralGl
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

noncomputable section

namespace GlobalTheory.Proof.parahoric_le_integral_gl

theorem inX_mem_nfLat_iff {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) (n c : ℕ)
    (e : Fin c → ℤ) (z : Sp E n) (x : Sp E n) :
    Loc.inX E n c x ∈ IndefiniteRowSideFullHecke.SandwichNormalForm.nfLat P n c e z ↔ x ∈ stdAt E n P := by
  constructor
  · rintro ⟨l, hl, s, -, h⟩
    have hs : ∀ b, s b = 0 := by
      intro b
      have h1 := congrFun h (Fin.natAdd n b)
      have hq := Proof.NormalFormAtPrime.qOf_ne_zero P
      have h2 : ∀ (y : Fin n → E), Loc.inX E n c y (Fin.natAdd n b) = 0 := fun y => by
        rw [inX_apply, dif_neg (by simp)]
      have h3 : ∀ i : Fin c, IndefiniteRowSideFullHecke.SandwichNormalForm.nfGen (qOf P) n c e z i (Fin.natAdd n b) =
          if b = i then ((qOf P : E) ^ e i) else 0 := by
        intro i
        unfold IndefiniteRowSideFullHecke.SandwichNormalForm.nfGen
        rw [Pi.smul_apply, Pi.add_apply]
        have h4 : (if i.1 = 0 then Loc.inX E n c z else 0 : Sp E (n + c)) (Fin.natAdd n b) = 0 := by
          split_ifs
          · exact h2 z
          · rfl
        rw [h4]
        simp [Loc.eN, Fin.val_inj]
      rw [Pi.add_apply, h2, h2, Finset.sum_apply] at h1
      simp only [Pi.smul_apply, h3, smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, zero_add] at h1
      exact (mul_eq_zero.1 h1.symm).resolve_right (zpow_ne_zero _ hq)
    simp only [hs, zero_smul, Finset.sum_const_zero, add_zero] at h
    rwa [inX_injective h]
  · intro hx
    exact ⟨x, hx, 0, fun _ => IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P, by simp⟩

theorem prCat_le_GLint : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)),
    P ∉ Pr.vGs → ∀ h : AutY X R j, GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm.NF Pr j P h → prCat (Pr := Pr) sharp j P h ≤ GLint X.E (R.N j) P := by
  rintro X Pr R sharp j P hP h ⟨e, z, -, -, hnf⟩ g ⟨r, ⟨-, hr⟩, hrg⟩ x
  have hJ : h⁻¹ * r * h ∈ Jat (Pr := Pr) (R := R) sharp j P := by
    have := Subgroup.mem_comap.1 hr
    simpa using this
  unfold Jat at hJ
  rw [if_neg hP] at hJ
  have hk := hJ.1
  have key : ∀ y, y ∈ IndefiniteRowSideFullHecke.SandwichNormalForm.nfLat P (R.N j) (cOf R j) e z ↔ h⁻¹ y ∈ stdAt X.E _ P := by
    intro y
    rw [← hnf, mem_stdAt_iff]
    constructor
    · rintro ⟨w, hw, rfl⟩
      have : h⁻¹ (h w) = w := h.symm_apply_apply w
      rw [this]
      exact (IndefiniteRowSideFullHecke.SandwichNormalForm.mem_lamYat hP w).1 hw
    · intro hy
      exact ⟨h⁻¹ y, (IndefiniteRowSideFullHecke.SandwichNormalForm.mem_lamYat hP _).2 hy, h.apply_symm_apply y⟩
  rw [← inX_mem_nfLat_iff P _ (cOf R j) e z, ← inX_mem_nfLat_iff P _ (cOf R j) e z, ← hrg, key, key,
    ← hk (h⁻¹ (Loc.inX X.E (R.N j) (cOf R j) x))]
  have : (h⁻¹ * r * h) (h⁻¹ (Loc.inX X.E (R.N j) (cOf R j) x)) = h⁻¹ (r (Loc.inX X.E (R.N j) (cOf R j) x)) := by
    change h⁻¹ (r (h (h.symm _))) = _
    rw [h.apply_symm_apply]
  rw [this]

end GlobalTheory.Proof.parahoric_le_integral_gl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.VectorsLinearMapsBoundedDenominatorsAtPrime
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

namespace GlobalTheory.Proof.vectors_linearMaps_bounded_denominators_atPrime

theorem exists_intAt_pow_mul {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (a : E) :
    ∃ m : ℕ, IntAt P ((qOf P : E) ^ m * a) := by
  have e : (qOf P : E) = algebraMap (𝓞 E) E (qOf P : 𝓞 E) := by rw [map_natCast]
  have h1 : P.valuation E (qOf P : E) < 1 := by
    rw [e, HeightOneSpectrum.valuation_of_algebraMap]
    exact (P.intValuation_lt_one_iff_mem _).2 (Ideal.absNorm_mem _)
  have key : ∃ m : ℕ, P.valuation E ((qOf P : E) ^ m * a) ≤ 1 := by
    rcases eq_or_ne (P.valuation E a) 0 with ha | ha
    · exact ⟨0, by simp [ha]⟩
    have hq : P.valuation E (qOf P : E) ≠ 0 := by
      simpa using GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero P
    refine ⟨(WithZero.log (P.valuation E a)).toNat, ?_⟩
    rw [map_mul, map_pow]
    rw [← WithZero.exp_log hq, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
    rw [← WithZero.exp_log hq, ← WithZero.exp_log ha, ← WithZero.exp_nsmul, ← WithZero.exp_add,
      ← WithZero.exp_zero, WithZero.exp_le_exp, WithZero.log_exp]
    set u := WithZero.log (P.valuation E (qOf P : E))
    set w := WithZero.log (P.valuation E a)
    have h2 : w ≤ (w.toNat : ℤ) := Int.self_le_toNat w
    have h3 : (0 : ℤ) ≤ (w.toNat : ℤ) := Int.natCast_nonneg _
    rw [nsmul_eq_mul]
    nlinarith
  obtain ⟨m, h⟩ := key
  obtain ⟨n, d, hnd⟩ := P.exists_primeCompl_mul_eq_of_integer _ h
  exact ⟨m, n, d, d.2, by rw [mul_comm]; exact hnd⟩

theorem exists_intAt_family {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) {ι : Type} [Fintype ι]
    (f : ι → E) : ∃ m : ℕ, ∀ m', m ≤ m' → ∀ i, IntAt P ((qOf P : E) ^ m' * f i) := by
  choose g hg using fun i => exists_intAt_pow_mul P (f i)
  exact ⟨Finset.univ.sup g, fun m' hm i =>
    GlobalTheory.Proof.NormalFormAtPrime.intAt_pow_mono ((Finset.le_sup (Finset.mem_univ i)).trans hm) (hg i)⟩

theorem bounded_denominators : ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (a b : ℕ), (∀ v : Fin a → E, ∃ m : ℕ, ∀ m', m ≤ m' → IntV P (((qOf P : E) ^ m') • v)) ∧ ∀ y : (Fin a → E) →ₗ[E] (Fin b → E), ∃ m : ℕ, ∀ m', m ≤ m' → IntHom P (((qOf P : E) ^ m') • y) := by
  intro E _ _ P a b
  refine ⟨fun v => ?_, fun y => ?_⟩
  · obtain ⟨m, hm⟩ := exists_intAt_family P v
    exact ⟨m, fun m' h l => hm m' h l⟩
  · obtain ⟨m, hm⟩ := exists_intAt_family P (fun p : Fin a × Fin b => y (Pi.single p.1 1) p.2)
    exact ⟨m, fun m' h => (intHom_iff _).2 fun s l => hm m' h (s, l)⟩

end GlobalTheory.Proof.vectors_linearMaps_bounded_denominators_atPrime
end

