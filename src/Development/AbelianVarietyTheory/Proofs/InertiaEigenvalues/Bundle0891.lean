import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NatCastMemPlaceAt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0099
import Formalism.LocalToGlobal.ProjectiveLattices.LocFld
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0026
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0885
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsLiftOfMemKO
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0013
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAlgebraicIntegerPointOfFiniteExtension
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GeoTie

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GeoTie.NumPt

section Val

variable {V : Type} {K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K]
  [Algebra V K] [IsFractionRing V K]

lemma vV_nonneg_of_mem (b : V) : 0 ≤ vV V (algebraMap V K b) := by
  by_cases hb : b = 0
  · subst hb; simp [vV]
  have h1 : valV V (algebraMap V K b) ≤ 1 := by
    simpa [valV] using (IsDiscreteValuationRing.maximalIdeal V).valuation_le_one (K := K) b
  have h0 : valV V (algebraMap V K b) ≠ 0 := valV_ne_zero (by simpa using hb)
  have := (WithZero.log_le_log h0 one_ne_zero).2 h1
  simp only [vV]
  simp at this
  omega

lemma vV_one : vV V (1 : K) = 0 := by simp [vV]

lemma vV_inv {x : K} (hx : x ≠ 0) : vV V x⁻¹ = - vV V x := by
  have := vV_mul (V := V) hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, vV_one] at this
  omega

lemma vV_eq_zero_of_mul {x y : K} (hx : x ∈ Set.range (algebraMap V K)) (hy : y ∈ Set.range (algebraMap V K))
    (h : x * y = 1) : vV V x = 0 := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  have ha : algebraMap V K a ≠ 0 := left_ne_zero_of_mul_eq_one h
  have hb : algebraMap V K b ≠ 0 := right_ne_zero_of_mul_eq_one h
  have := vV_mul (V := V) ha hb
  rw [h, vV_one] at this
  have h1 := vV_nonneg_of_mem (K := K) a
  have h2 := vV_nonneg_of_mem (K := K) b
  omega

lemma vV_irreducible {ϖ : V} (hϖ : Irreducible ϖ) : vV V (algebraMap V K ϖ) = 1 := by
  have hne : ϖ ≠ 0 := hϖ.ne_zero
  simp only [vV, valV]
  rw [HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_singleton _ hne ((IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ)]
  simp

end Val

section Cmp

variable {V : Type} {K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K]
  [Algebra V K] [IsFractionRing V K]
  {V' : Type} {K' : Type} [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] [Field K']
  [Algebra V' K'] [IsFractionRing V' K']

lemma exists_vV_map (ψ : K →+* K') (hψ : ∀ a : V, ψ (algebraMap V K a) ∈ Set.range (algebraMap V' K')) :
    ∃ r : ℕ, ∀ x, vV V' (ψ x) = (r : ℤ) * vV V x := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨b, hb⟩ := hψ ϖ
  have hr0 : 0 ≤ vV V' (ψ (algebraMap V K ϖ)) := hb ▸ vV_nonneg_of_mem b
  refine ⟨(vV V' (ψ (algebraMap V K ϖ))).toNat, ?_⟩
  rw [Int.toNat_of_nonneg hr0]
  have hint : ∀ a : V, a ≠ 0 → vV V' (ψ (algebraMap V K a)) = vV V' (ψ (algebraMap V K ϖ)) * vV V (algebraMap V K a) := by
    intro a ha
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
    have hu0 : algebraMap V K (u : V) ≠ 0 := by
      simpa using u.ne_zero
    have hϖ0 : algebraMap V K ϖ ≠ 0 := by simpa using hϖ.ne_zero
    have huK : vV V (algebraMap V K (u : V)) = 0 :=
      vV_eq_zero_of_mul ⟨_, rfl⟩ ⟨((u⁻¹ : Vˣ) : V), rfl⟩ (by rw [← map_mul]; simp)
    have huK' : vV V' (ψ (algebraMap V K (u : V))) = 0 :=
      vV_eq_zero_of_mul (hψ _) (hψ ((u⁻¹ : Vˣ) : V)) (by rw [← map_mul, ← map_mul]; simp)
    have hpow : ∀ (F : Type) [Field F] (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
        [Algebra W F] [IsFractionRing W F] (y : F), y ≠ 0 → ∀ m : ℕ, vV W (y ^ m) = m * vV W y := by
      intro F _ W _ _ _ _ _ y hy m
      induction m with
      | zero => simp [vV]
      | succ m ih => rw [pow_succ, vV_mul (pow_ne_zero _ hy) hy, ih]; push_cast; ring
    rw [map_mul, map_pow, map_mul, map_pow, vV_mul hu0 (pow_ne_zero _ hϖ0),
      vV_mul ((map_ne_zero ψ).2 hu0) (pow_ne_zero _ ((map_ne_zero ψ).2 hϖ0)), huK, huK',
      hpow K V _ hϖ0, hpow K' V' _ ((map_ne_zero ψ).2 hϖ0), vV_irreducible hϖ]
    ring
  intro x
  by_cases hx : x = 0
  · subst hx; simp [vV]
  obtain ⟨a, b, hb0, rfl⟩ := IsFractionRing.div_surjective (A := V) x
  have hb' : b ≠ 0 := nonZeroDivisors.ne_zero hb0
  have ha' : a ≠ 0 := by rintro rfl; simp at hx
  have haK : algebraMap V K a ≠ 0 := by simpa using ha'
  have hbK : algebraMap V K b ≠ 0 := by simpa using hb'
  rw [div_eq_mul_inv, map_mul, map_inv₀, vV_mul ((map_ne_zero ψ).2 haK) (inv_ne_zero ((map_ne_zero ψ).2 hbK)),
    vV_inv ((map_ne_zero ψ).2 hbK), vV_mul haK (inv_ne_zero hbK), vV_inv hbK, hint a ha', hint b hb']
  ring

end Cmp

section Main

open LocFldPf HeightOneSpectrum

theorem exists_ptC_of_finExt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (p : ℕ) [Fact p.Prime] (φ : c.F →+* ℂ_[p]), IntAll Xo c →
    ∀ (L : Type) [Field L] [Algebra c.F L] [FiniteDimensional c.F L] (σ : L →+* ℂ_[p]),
      (∀ a, σ (algebraMap c.F L a) = φ a) → ∀ (y : FrPt Xo c L) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ),
      ∃ (z : PtC Xo c φ) (u : ℂ_[p]), u ≠ 0 ∧ ∀ f ∈ sec Xo c a n, valC z.1 f = u * σ (evR Xo c f y) := by
  intro E _ _ _ H Dw l Xo c p _ φ hIA L _ _ _ σ hσ y a n
  haveI : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  haveI : NumberField L := NumberField.of_module_finite c.F L
  have hL : GlobalTheory.Reg.EvLaws Xo c := (GlobalTheory.Reg.evLaws_genFr_nonempty_comp E H Dw l Xo c).1

  let w : HeightOneSpectrum (𝓞 L) := placeAt σ
  haveI : Finite (𝓞 L ⧸ w.asIdeal) := w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot
  haveI : CharZero (adicCompletionIntegers L w) :=
    charZero_of_injective_algebraMap
      (FaithfulSMul.algebraMap_injective (𝓞 L) (adicCompletionIntegers L w))
  obtain ⟨e1, he1, h1⟩ := exists_e (L := L) w
  let T : CDVR := { V := adicCompletionIntegers L w, cpl := isAdicComplete w }
  let ι : L →+* T.Fr := kMap w
  have hOσ : OverLa (placeAt σ) T.V ι e1 := by
    refine ⟨he1, fun x => ?_⟩
    show vV (adicCompletionIntegers L w) (kMap w x) = _
    simp only [vV, vLa]
    rw [h1, WithZero.log_pow]
    push_cast
    ring
  have hFin : T.FinRes := finite_res w

  have hlies : w.asIdeal.LiesOver (placeAt φ).asIdeal := ⟨by
    ext b
    rw [Ideal.mem_comap, mem_placeAt, mem_placeAt]
    show _ ↔ ‖σ ((algebraMap (𝓞 c.F) (𝓞 L) b : 𝓞 L) : L)‖ < 1
    rw [show ((algebraMap (𝓞 c.F) (𝓞 L) b : 𝓞 L) : L) = algebraMap c.F L (b : c.F) from rfl, hσ]⟩
  let io : c.F →+* T.Fr := ι.comp (algebraMap c.F L)
  have he2 : (placeAt φ).asIdeal.ramificationIdx' w.asIdeal ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal (placeAt φ).ne_bot
  have hO : OverLa (placeAt φ) T.V io ((placeAt φ).asIdeal.ramificationIdx' w.asIdeal * e1) := by
    refine ⟨Nat.mul_pos (Nat.pos_of_ne_zero he2) he1, fun b => ?_⟩
    show vV (adicCompletionIntegers L w) (kMap w (algebraMap c.F L b)) = _
    simp only [vV, vLa]
    rw [h1, ← valuation_liesOver L (placeAt φ) w b, ← pow_mul, WithZero.log_pow]
    push_cast
    simp

  letI : Algebra c.F T.Fr := io.toAlgebra
  let ιA : L →ₐ[c.F] T.Fr := { ι with commutes' := fun _ => rfl }
  obtain ⟨yT, hyT⟩ := hL.bc L T.Fr ιA y

  obtain ⟨T', io', e', y', hO', hy'alg, φ', zz, t, hint, hmap, hbor⟩ := hIA (placeAt φ) T io _ hO hFin yT
  letI : Algebra c.F T'.Fr := io'.toAlgebra

  let ψ : T.Fr →+* T'.Fr := (φ' : T.Fr →+* T'.Fr)
  obtain ⟨r, hr⟩ := exists_vV_map (V := T.V) (V' := T'.V) ψ hint
  have hψio : ∀ b : c.F, ψ (io b) = io' b := fun b => φ'.commutes b
  have hp0 : vLa (placeAt φ) (p : c.F) ≠ 0 := by
    have hlt : (placeAt φ).valuation c.F (p : c.F) < 1 := by
      rw [show (p : c.F) = algebraMap (𝓞 c.F) c.F ((p : ℕ) : 𝓞 c.F) by simp,
        HeightOneSpectrum.valuation_lt_one_iff_mem]
      exact natCast_mem_placeAt φ
    have hne : (placeAt φ).valuation c.F (p : c.F) ≠ 0 := by
      rw [Valuation.ne_zero_iff]
      exact_mod_cast (Fact.out : p.Prime).ne_zero
    intro h0
    have : WithZero.log ((placeAt φ).valuation c.F (p : c.F)) = 0 := by
      simp only [vLa] at h0; omega
    have h2 := WithZero.exp_log hne
    rw [this, WithZero.exp_zero] at h2
    exact hlt.ne h2.symm
  have hrpos : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · exfalso
      have h3 := hO'.2 (p : c.F)
      rw [← hψio, hr, h0] at h3
      simp only [Nat.cast_zero, zero_mul] at h3
      have : (e' : ℤ) ≠ 0 := by exact_mod_cast hO'.1.ne'
      exact (mul_ne_zero this hp0) h3.symm
    · exact h0
  have hOσ' : OverLa (placeAt σ) T'.V (ψ.comp ι) (r * e1) := hOσ.bc ψ hrpos hr

  obtain ⟨k', hk'⟩ := GlobalTheory.T.exists_cdvrReadingInCp_of_finiteResidue p L σ T' (ψ.comp ι) (r * e1) hOσ' hy'alg
  have hk : IsReading φ T' io' k' := by
    refine ⟨fun b => ?_, hk'.int⟩
    rw [← hψio, ← hσ b]
    exact hk'.comp (algebraMap c.F L b)

  obtain ⟨z₀, hz₀⟩ := PtC.exists_of_reading hk y' hy'alg
  refine ⟨z₀, k' (wchar (ex Dw a n) t), ?_, fun f hf => ?_⟩
  · rw [map_ne_zero]
    simp [wchar, Finset.prod_ne_zero_iff]
  · rw [hz₀ a n f hf]
    obtain ⟨q, χ, y₀, hy₀⟩ := hL.test L y
    have e1' : evR Xo c f y = χ (f q y₀) := GlobalTheory.Reg.evR_eq_map_of_test_point hL hf q χ y₀ y hy₀
    have e2 : evR Xo c f zz = (φ'.comp (ιA.comp χ)) (f q y₀) :=
      GlobalTheory.Reg.evR_eq_map_of_test_point hL hf q _ y₀ zz
        (ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans _ φ' (ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans χ ιA hy₀ hyT) hmap)
    have e3 : evI y' f = wchar (ex Dw a n) t * evR Xo c f zz :=
      hL.wt a n f hf T'.Fr t zz y'.1 (hL.test _ _) (hL.test _ _) hbor
    rw [e3, map_mul, e2, e1']
    congr 1
    exact hk'.comp (χ (f q y₀))

end Main

end GlobalTheory.GeoTie.NumPt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFixedParahoricBlockVectorOfIdempotent
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BlockIdem

open ValuativeRel Matrix GlobalTheory.StepData

theorem conv_sum {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W] (T : G → W →ₗ[ℂ] W) (f : G → W)
    (hT : ∀ g h, T g (f h) = f (g * h)) (a b : MonoidAlgebra ℂ G) :
    (a.coeff.sum fun g c => c • T g (b.coeff.sum fun h d => d • f h)) = (a * b).coeff.sum fun k c => c • f k := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a a' ha ha' =>
    rw [add_mul, MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_add, Finsupp.sum_add_index', Finsupp.sum_add_index', ha, ha']
      <;> intros <;> simp [add_smul]
  | single g c =>
    rw [MonoidAlgebra.coeff_single, Finsupp.sum_single_index (by simp)]
    induction b using MonoidAlgebra.induction_linear with
    | zero => simp
    | add b b' hb hb' =>
      rw [mul_add, MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_add, Finsupp.sum_add_index', Finsupp.sum_add_index',
        map_add, smul_add, hb, hb'] <;> intros <;> simp [add_smul]
    | single h d =>
      rw [MonoidAlgebra.single_mul_single, MonoidAlgebra.coeff_single, MonoidAlgebra.coeff_single,
        Finsupp.sum_single_index, Finsupp.sum_single_index, map_smul, hT, smul_smul] <;> simp

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {r t : ℕ}

def ee (r t : ℕ) : Fin r ⊕ Fin t ≃ Fin (r + t) := stdSum (rfl : r + t = r + t)

theorem ee_inl (i : Fin r) : ee r t (Sum.inl i) = Fin.castAdd t i := by ext; simp [ee]

theorem ee_inr (j : Fin t) : ee r t (Sum.inr j) = Fin.natAdd r j := by ext; simp [ee]

variable (F) in

def dg (r t : ℕ) : GL (Fin r) F →* GL (Fin (r + t)) F := (emb₂ F (ee r t)).comp (MonoidHom.inl _ _)

variable (F) in

def bl (r t : ℕ) : GL (Fin (r + t)) F →* GL (Fin r ⊕ Fin t) F := reix F (ee r t).symm

theorem bl_apply (g : GL (Fin (r + t)) F) (a b : Fin r ⊕ Fin t) : (bl F r t g).val a b = g.val (ee r t a) (ee r t b) := by
  rw [bl, val_reix, Equiv.symm_symm]

theorem eq_of_bl {g g' : GL (Fin (r + t)) F} (H : (bl F r t g).val = (bl F r t g').val) : g = g' := by
  apply Units.ext
  ext a b
  obtain ⟨a, rfl⟩ := (ee r t).surjective a
  obtain ⟨b, rfl⟩ := (ee r t).surjective b
  have := congrFun (congrFun H a) b
  rwa [bl_apply, bl_apply] at this

theorem dg_bl (A : GL (Fin r) F) : (bl F r t (dg F r t A)).val = fromBlocks A.val 0 0 1 := by
  ext a b
  rw [bl_apply]
  have := val_emb₂ F (ee r t) (A, 1)
  simp only [dg, MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inl_apply]
  rw [this, reindex_apply, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rfl

theorem bl_21 (g : GL (Fin (r + t)) F) (i : Fin t) (j : Fin r) :
    (bl F r t g).val.toBlocks₂₁ i j = g.val (Fin.natAdd r i) (Fin.castAdd t j) := by
  simp only [toBlocks₂₁, of_apply, bl_apply, ee_inr, ee_inl]

theorem bl_11 (g : GL (Fin (r + t)) F) (i j : Fin r) :
    (bl F r t g).val.toBlocks₁₁ i j = g.val (Fin.castAdd t i) (Fin.castAdd t j) := by
  simp only [toBlocks₁₁, of_apply, bl_apply, ee_inl]

theorem bl_22 (g : GL (Fin (r + t)) F) :
    (bl F r t g).val.toBlocks₂₂ = g.val.submatrix (Fin.natAdd r) (Fin.natAdd r) := by
  ext i j
  simp only [toBlocks₂₂, of_apply, bl_apply, ee_inr, submatrix_apply]

theorem intM_dg {A : GL (Fin r) F} (hA : IntM A.val) : IntM (dg F r t A).val := by
  intro a b
  obtain ⟨a, rfl⟩ := (ee r t).surjective a
  obtain ⟨b, rfl⟩ := (ee r t).surjective b
  have := congrFun (congrFun (dg_bl (t := t) A) a) b
  rw [bl_apply] at this
  rw [this]
  exact intM_fromBlocks.2 ⟨hA, intM_zero, intM_zero, intM_one⟩ a b

theorem dg_mem_KO {A : GL (Fin r) F} (hA : A ∈ KO F (Fin r)) : dg F r t A ∈ KO F (Fin (r + t)) :=
  GlobalTheory.StepData.mem_KO.2 ⟨intM_dg (GlobalTheory.StepData.mem_KO.1 hA).1,
    by rw [← map_inv]; exact intM_dg (GlobalTheory.StepData.mem_KO.1 hA).2⟩

end GlobalTheory.BlockIdem

namespace GlobalTheory.BlockIdem

open ValuativeRel Matrix GlobalTheory.StepData

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {r t : ℕ}
  {χ : Fˣ →* ℂˣ} {W : Type} [AddCommGroup W] [Module ℂ W] {π : Representation ℂ (GL (Fin (r + t)) F) W}

theorem isBlockVec_add {v w : W} (hv : IsBlockVec χ π v) (hw : IsBlockVec χ π w) : IsBlockVec χ π (v + w) :=
  fun h hh h1 h2 u hu => by rw [map_add, hv h hh h1 h2 u hu, hw h hh h1 h2 u hu, smul_add]

theorem isBlockVec_smul (c : ℂ) {v : W} (hv : IsBlockVec χ π v) : IsBlockVec χ π (c • v) :=
  fun h hh h1 h2 u hu => by rw [map_smul, hv h hh h1 h2 u hu, smul_comm]

theorem isBlockVec_zero : IsBlockVec χ π (0 : W) := fun _ _ _ _ _ _ => by simp

theorem dg_fix {v : W} (hv : IsBlockVec χ π v) {κ : GL (Fin r) F} (hκ : κ ∈ KOne F (Fin r)) :
    π (dg F r t κ) v = v := by
  have key := hv _ (dg_mem_KO (GlobalTheory.StepData.KOne_le_KO hκ))
    (fun i j => by rw [← bl_21, dg_bl, toBlocks_fromBlocks₂₁]; simp)
    (fun i j => by
      rw [← bl_11, dg_bl, toBlocks_fromBlocks₁₁]
      have := (GlobalTheory.StepData.mem_KOne.1 hκ) i j
      rwa [Matrix.sub_apply, Matrix.one_apply] at this)
    1 (by rw [← bl_22, dg_bl, toBlocks_fromBlocks₂₂, det_one, Units.val_one])
  rw [key, map_one, Units.val_one, one_smul]

theorem dg_isBlockVec {v : W} (hv : IsBlockVec χ π v) {κ : GL (Fin r) F} (hκ : κ ∈ KO F (Fin r)) :
    IsBlockVec χ π (π (dg F r t κ) v) := by
  intro h hh h1 h2 u hu
  have hd := dg_mem_KO (t := t) hκ
  have hK : (dg F r t κ)⁻¹ * h * dg F r t κ ∈ KO F (Fin (r + t)) := mul_mem (mul_mem (inv_mem hd) hh) hd
  obtain ⟨A, B, C, D, hE⟩ : ∃ A B C D, (bl F r t h).val = fromBlocks A B C D :=
    ⟨_, _, _, _, (fromBlocks_toBlocks _).symm⟩
  have hΦ : (bl F r t ((dg F r t κ)⁻¹ * h * dg F r t κ)).val =
      fromBlocks ((κ⁻¹).val * A * κ.val) ((κ⁻¹).val * B) (C * κ.val) D := by
    rw [← map_inv (dg F r t) κ, map_mul, map_mul, Units.val_mul, Units.val_mul, dg_bl, dg_bl, hE,
      fromBlocks_multiply, fromBlocks_multiply]
    simp [Matrix.mul_assoc]
  have hC : MaxM C := fun i j => by
    rw [show C i j = h.val (Fin.natAdd r i) (Fin.castAdd t j) by rw [← bl_21, hE, toBlocks_fromBlocks₂₁]]
    exact h1 i j
  have hA : MaxM (A - 1) := fun i j => by
    rw [Matrix.sub_apply, Matrix.one_apply]
    rw [show A i j = h.val (Fin.castAdd t i) (Fin.castAdd t j) by rw [← bl_11, hE, toBlocks_fromBlocks₁₁]]
    exact h2 i j
  have key := hv _ hK
    (fun i j => by rw [← bl_21, hΦ, toBlocks_fromBlocks₂₁]; exact hC.mul_intM (intM_of_mem_KO hκ) i j)
    (fun i j => by
      rw [← bl_11, hΦ, toBlocks_fromBlocks₁₁]
      have e : (κ⁻¹).val * A * κ.val - 1 = (κ⁻¹).val * (A - 1) * κ.val := by
        rw [mul_sub, sub_mul, mul_one, Units.inv_mul]
      have := ((((GlobalTheory.StepData.mem_KO.1 hκ).2).mul_maxM hA).mul_intM (intM_of_mem_KO hκ)) i j
      rw [← e, Matrix.sub_apply, Matrix.one_apply] at this
      exact this)
    u (by
      rw [← bl_22, hΦ, toBlocks_fromBlocks₂₂]
      rw [← bl_22, hE, toBlocks_fromBlocks₂₂] at hu
      exact hu)
  have hh' : h * dg F r t κ = dg F r t κ * ((dg F r t κ)⁻¹ * h * dg F r t κ) := by group
  calc π h (π (dg F r t κ) v) = π (dg F r t κ) (π ((dg F r t κ)⁻¹ * h * dg F r t κ) v) := by
        rw [← Module.End.mul_apply, ← map_mul, hh', map_mul, Module.End.mul_apply]
    _ = (χ u : ℂ) • π (dg F r t κ) v := by rw [key, map_smul]

theorem exists_of_isLiftN {p : ℕ} {g : GL (Fin r) (ZMod p)} {h : GL (Fin (r + t)) F} (H : IsLiftN g h) :
    ∃ A : GL (Fin r) F, dg F r t A = h ∧ IsLift g A := by
  set M : Matrix (Fin r) (Fin r) F := fun i j => h.val (Fin.castAdd t i) (Fin.castAdd t j) with hM
  have hΦ : (bl F r t h).val = fromBlocks M 0 0 1 := by
    ext (a | a) (b | b)
    · rw [bl_apply, ee_inl, ee_inl, fromBlocks_apply₁₁]
    · have := H (Fin.castAdd t a) (Fin.natAdd r b)
      rw [dif_neg (by simp only [Fin.coe_castAdd, Fin.coe_natAdd]; omega)] at this
      have hne : Fin.castAdd t a ≠ Fin.natAdd r b := fun e => by
        have := congrArg Fin.val e; simp at this; omega
      simp [bl_apply, ee_inl, ee_inr, this, hne]
    · have := H (Fin.natAdd r a) (Fin.castAdd t b)
      rw [dif_neg (by simp only [Fin.coe_castAdd, Fin.coe_natAdd]; omega)] at this
      have hne : Fin.natAdd r a ≠ Fin.castAdd t b := fun e => by
        have := congrArg Fin.val e; simp at this; omega
      simp [bl_apply, ee_inl, ee_inr, this, hne]
    · have := H (Fin.natAdd r a) (Fin.natAdd r b)
      rw [dif_neg (by simp only [Fin.coe_castAdd, Fin.coe_natAdd]; omega)] at this
      simp [bl_apply, ee_inr, this, Matrix.one_apply]
  have hdet : IsUnit M.det := by
    have h1 : IsUnit (bl F r t h).val.det := (Matrix.isUnit_iff_isUnit_det _).1 (bl F r t h).isUnit
    rwa [hΦ, Matrix.det_fromBlocks_zero₂₁, det_one, mul_one] at h1
  refine ⟨Matrix.nonsingInvUnit M hdet, eq_of_bl ?_, fun a b => ?_⟩
  · rw [dg_bl, hΦ]; rfl
  · have := H (Fin.castAdd t a) (Fin.castAdd t b)
    rw [dif_pos (show ((Fin.castAdd t a : Fin (r + t)) : ℕ) < r ∧ ((Fin.castAdd t b : Fin (r + t)) : ℕ) < r
      from ⟨a.isLt, b.isLt⟩)] at this
    exact this

end GlobalTheory.BlockIdem

namespace GlobalTheory.BlockIdem

open ValuativeRel Matrix GlobalTheory.StepData

theorem exists_fixed_blockVec : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] (r t : ℕ) (χ : Fˣ →* ℂˣ) (W : Type) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin (r + t)) F) W) (z : MonoidAlgebra ℂ (GL (Fin r) (ZMod p))) (x : W), resCard F = p → z * z = z → IsBlockVec χ π x → NotKilled π z x → ∃ y : W, y ≠ 0 ∧ IsBlockVec χ π y ∧ ∃ ℓ : GL (Fin r) (ZMod p) → GL (Fin r) F, (∀ g, IsLift g (ℓ g)) ∧ (z.coeff.sum fun g c => c • π (emb₂ F (stdSum (rfl : r + t = r + t)) (ℓ g, 1)) y) = y := by
  intro F _ _ _ _ p _ r t χ W _ _ π z x hp hz hx hnk
  obtain ⟨ℓ', hℓ', hne⟩ := hnk
  have hA : ∀ g, ∃ A : GL (Fin r) F, dg F r t A = ℓ' g ∧ IsLift g A := fun g => exists_of_isLiftN (hℓ' g)
  choose ℓ hℓ1 hℓ2 using hA
  have hx1 : ∀ h ∈ KOne F (Fin r), (π.comp (dg F r t)) h x = x := fun h hh => dg_fix hx hh
  have hT : ∀ g h, π (dg F r t (ℓ g)) (π (dg F r t (ℓ h)) x) = π (dg F r t (ℓ (g * h))) x := by
    intro g h
    rw [← Module.End.mul_apply, ← map_mul, ← map_mul]
    exact IsLift.apply_eq hp (π := π.comp (dg F r t)) hx1 ((hℓ2 g).mul hp (hℓ2 h)) (hℓ2 (g * h))
  refine ⟨z.coeff.sum fun g c => c • π (dg F r t (ℓ g)) x, ?_, ?_, ℓ, hℓ2, ?_⟩
  · simpa only [hℓ1] using hne
  · rw [Finsupp.sum]
    exact Finset.sum_induction _ _ (fun a b => isBlockVec_add) isBlockVec_zero
      (fun g _ => isBlockVec_smul _ (dg_isBlockVec hx ((hℓ2 g).mem_KO hp)))
  · have := conv_sum (fun g => π (dg F r t (ℓ g))) (fun h => π (dg F r t (ℓ h)) x) hT z z
    rw [hz] at this
    exact this

end GlobalTheory.BlockIdem
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStandardTypeVectorOfParabolicTypeVector
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.LevelType
open Matrix

theorem exists_stdVec_of_parVec : ∀ (p : ℕ) [Fact p.Prime] (r : ℕ) (α : Type) [Fintype α] [LinearOrder α] (m : α → Type) [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] (e : (Σ a, m a) ≃ Fin r) (a : α) (θ : (ZMod p)ˣ →* ℂˣ) (U : Type) [AddCommGroup U] [Module ℂ U] (ρ : Representation ℂ (GL (Fin r) (ZMod p)) U) (v : U), Fintype.card (m a) = 1 → v ≠ 0 → ParVec ρ e a θ v → ∃ (c : ℕ) (v' : U), c < r ∧ v' ≠ 0 ∧ StdVec ρ c θ v' := by
  intro p _ r α _ _ m _ _ e a θ U _ _ ρ v hm hv hpar
  obtain ⟨k0⟩ : Nonempty (m a) := Fintype.card_pos_iff.1 (by omega)
  let σ := Tuple.sort (blk e)
  let i₀ := e ⟨a, k0⟩
  have hi₀ : blk e i₀ = a := blk_apply e a k0
  have hmono := Tuple.monotone_sort (blk e)
  have hlt : ∀ i, blk e i < a → σ.symm i < σ.symm i₀ := fun i h => hmono.reflect_lt (by
    show blk e (σ (σ.symm i)) < blk e (σ (σ.symm i₀))
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, hi₀]; exact h)
  have hgt : ∀ i, a < blk e i → σ.symm i₀ < σ.symm i := fun i h => hmono.reflect_lt (by
    show blk e (σ (σ.symm i₀)) < blk e (σ (σ.symm i))
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, hi₀]; exact h)
  have hlo : ∀ i, (σ.symm i).val ≤ (σ.symm i₀).val → blk e i ≤ a := fun i h => by
    by_contra h'
    exact absurd h (not_le.2 (Fin.lt_def.1 (hgt i (not_le.1 h'))))
  have hhi : ∀ j, (σ.symm i₀).val ≤ (σ.symm j).val → a ≤ blk e j := fun j h => by
    by_contra h'
    exact absurd h (not_le.2 (Fin.lt_def.1 (hlt j (not_le.1 h'))))
  refine ⟨(σ.symm i₀).val, ρ (GlobalTheory.Parabolic.permGL (ZMod p) σ.symm) v, (σ.symm i₀).isLt, ?_, ?_⟩
  · intro h0
    apply hv
    have := congrArg (ρ (GlobalTheory.Parabolic.permGL (ZMod p) σ.symm)⁻¹) h0
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply, map_zero] at this
  · intro x hx
    set y := (GlobalTheory.Parabolic.permGL (ZMod p) σ.symm)⁻¹ * x * GlobalTheory.Parabolic.permGL (ZMod p) σ.symm with hy
    have hyij : ∀ i j, ¬ (blk e i ≤ a ∧ a ≤ blk e j) → y.val i j = if i = j then 1 else 0 := by
      intro i j hij
      have hyv : y.val i j = x.val (σ.symm i) (σ.symm j) := by
        rw [← GlobalTheory.Parabolic.conj_permGL_apply σ.symm y i j, hy]
        congr 2
        group
      rw [hyv, hx _ _ (fun h => hij ⟨hlo i h.1, hhi j h.2⟩)]
      simp
    have hyP : y ∈ parab (ZMod p) e := mem_parab.2 fun i j hji => by
      rw [hyij i j (fun h => absurd (h.1.trans h.2) (not_le.2 hji)), if_neg]
      rintro rfl
      exact lt_irrefl _ hji
    have hlev : ∀ b, b ≠ a → leviProj (ZMod p) e ⟨y, hyP⟩ b = 1 := by
      intro b hb
      refine Units.ext (Matrix.ext fun k l => ?_)
      rw [leviProj_apply, Units.val_one]
      rw [hyij _ _ (fun h => hb (le_antisymm (by simpa using h.1) (by simpa using h.2)))]
      simp [Matrix.one_apply]
    have h1 := hpar ⟨y, hyP⟩ hlev
    change ρ y v = (θ (GeneralLinearGroup.det y) : ℂ) • v at h1
    have hdet : GeneralLinearGroup.det y = GeneralLinearGroup.det x := by
      rw [hy, map_mul, map_mul, map_inv, mul_comm, mul_inv_cancel_left]
    have hxP : x * GlobalTheory.Parabolic.permGL (ZMod p) σ.symm = GlobalTheory.Parabolic.permGL (ZMod p) σ.symm * y := by rw [hy]; group
    rw [← Module.End.mul_apply, ← map_mul, hxP, map_mul, Module.End.mul_apply, h1, hdet, map_smul]

end GlobalTheory.LevelType
end
end

