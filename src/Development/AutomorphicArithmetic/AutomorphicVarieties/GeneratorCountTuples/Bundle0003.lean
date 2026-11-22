import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.Bridge
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LengthEqLengthInvariantsOfTorsionLevels
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.Bundle0001
import Mathlib

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.CardH2QuotientLeSha
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology GlobalTheory.TateLimit UpperTheory.V UpperTheory.V.Kum UpperTheory.V.K

theorem UpperTheory.V.K.card_H2_quotient_le_sha :
    GlobalTheory.Published.PoitouTateDuality → LocalFinitenessK → LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (D : LData L Ω l) (e : ℤ), IsTotallyComplex L → let n := e + 1; Nat.card (H2 (zlTw D n) ⧸ lpow l (H2 (zlTw D n)) 1) ≤ Nat.card (Sha1 (zd D n 1) (locFam D.S D.A) (continuous_locFam D.S D.A)) * l ^ Module.finrank ℚ L := by
  intro hP hF hT l hl L Ω _ _ _ _ _ D e hc
  classical
  have hcase : PTCase L l := Or.inr (NumberField.nrRealPlaces_eq_zero_iff.2 hc)
  have hS := fun r hr => (finite_level D e hP hcase r hr).2.1
  have h3 := (finite_level D e hP hcase 1 one_pos).2.2
  have hg := (global_lim D e hF hT hS h3).2 1
  intro n
  have : NeZero (l ^ 1) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  have hfd : Finite (TDual (ZMod (l ^ 1)) (ZMod (l ^ 1))) := DFunLike.finite _
  have hcd : Nat.card (TDual (ZMod (l ^ 1)) (ZMod (l ^ 1))) = l :=
    (GlobalTheory.T.card_dual_zmod_module_eq_card (l ^ 1) (ZMod (l ^ 1))).trans ((Nat.card_zmod _).trans (pow_one l))
  have hfin := fun v => (local_zr hF hT D (e + 1) v 1 one_pos).2.1
  have hloc : ∀ v : D.S, Nat.card (H2 ((zr D (e + 1) 1).comp (locFam D.S D.A v))) ≤ l := fun v => by
    rw [(local_zr hF hT D (e + 1) v 1 one_pos).2.2.2]
    refine le_trans ?_ hcd.le
    exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hpi : Nat.card (∀ v : D.S, H2 ((zr D (e + 1) 1).comp (locFam D.S D.A v))) ≤
      l ^ Module.finrank ℚ L := by
    rw [Nat.card_pi]
    refine le_trans (Finset.prod_le_pow_card _ _ l fun v _ => hloc v) ?_
    refine Nat.pow_le_pow_right hl.out.pos ?_
    rw [Finset.card_univ, Fintype.card_coe]
    exact UpperTheory.V.LDataCardLeFinrank.cardAbove L Ω l D
  have hker : LinearMap.ker (GlobalTheory.Published.PoitouTate.loc2 D.S D.A (zr D (e + 1) 1)) =
      Sha2 (zr D (e + 1) 1) (locFam D.S D.A) (continuous_locFam D.S D.A) := by
    rw [GlobalTheory.Published.PoitouTate.loc2, LinearMap.ker_pi]; rfl
  refine (card_quot_lpow 1 _ hg.1 hg.2).le.trans ?_
  rw [Submodule.card_eq_card_quotient_mul_card
    (LinearMap.ker (GlobalTheory.Published.PoitouTate.loc2 D.S D.A (zr D (e + 1) 1))),
    Nat.card_congr (LinearMap.quotKerEquivRange _).toEquiv, hker, ← (hS 1 one_pos).1.2.2.2]
  first
  | exact Nat.mul_le_mul_left _ (le_trans (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective) hpi)
  | (rw [mul_comm]; exact Nat.mul_le_mul_left _ (le_trans (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective) hpi))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.CardQuotPow
section
open scoped TensorProduct
open GlobalTheory.TateLimit

private theorem step (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X] [Module ℤ_[l] X] [Finite X]
    (c : ℕ) : Nat.card (X ⧸ lpow l X (c + 1)) ≤
      Nat.card (X ⧸ lpow l X 1) * Nat.card (X ⧸ lpow l X c) := by
  haveI : ∀ P : Submodule ℤ_[l] X, Finite (X ⧸ P) := fun P =>
    Finite.of_surjective _ P.mkQ_surjective
  let f : X →ₗ[ℤ_[l]] X ⧸ lpow l X (c + 1) :=
    (lpow l X (c + 1)).mkQ ∘ₗ LinearMap.lsmul ℤ_[l] X ((l : ℤ_[l]) ^ c)
  have hf : lpow l X 1 ≤ LinearMap.ker f := by
    rintro _ ⟨y, rfl⟩
    simp only [f, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, LinearMap.lsmul_apply]
    exact ⟨y, by rw [LinearMap.lsmul_apply, pow_add, mul_smul]⟩
  let g := (lpow l X 1).liftQ f hf
  let R := LinearMap.range g
  have h1 : Nat.card R ≤ Nat.card (X ⧸ lpow l X 1) :=
    Nat.card_le_card_of_surjective g.rangeRestrict g.surjective_rangeRestrict
  let p : X →ₗ[ℤ_[l]] (X ⧸ lpow l X (c + 1)) ⧸ R := R.mkQ ∘ₗ (lpow l X (c + 1)).mkQ
  have hp : lpow l X c ≤ LinearMap.ker p := by
    rintro _ ⟨y, rfl⟩
    simp only [p, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact ⟨Submodule.Quotient.mk y, rfl⟩
  have hps : Function.Surjective p :=
    R.mkQ_surjective.comp (lpow l X (c + 1)).mkQ_surjective
  have h2 : Nat.card ((X ⧸ lpow l X (c + 1)) ⧸ R) ≤ Nat.card (X ⧸ lpow l X c) := by
    refine Nat.card_le_card_of_surjective ((lpow l X c).liftQ p hp) fun z => ?_
    obtain ⟨x, rfl⟩ := hps z
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  rw [Submodule.card_eq_card_quotient_mul_card R]
  first
    | exact Nat.mul_le_mul h1 h2
    | exact (Nat.mul_le_mul h2 h1).trans_eq (mul_comm _ _)

theorem UpperTheory.V.K.cardQuotPow :
    ∀ (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X] [Module ℤ_[l] X] [Finite X] (c : ℕ), Nat.card (X ⧸ lpow l X c) ≤ Nat.card (X ⧸ lpow l X 1) ^ c := by
  intro l _ X _ _ _ c
  induction c with
  | zero =>
    have h : lpow l X 0 = ⊤ := by
      rw [eq_top_iff]
      intro x _
      exact ⟨x, by simp⟩
    haveI : Subsingleton (X ⧸ lpow l X 0) := Submodule.Quotient.subsingleton_iff.2 h
    rw [pow_zero]
    exact (Nat.card_of_subsingleton (0 : X ⧸ lpow l X 0)).le
  | succ c ih =>
    rw [pow_succ']
    exact (step l X c).trans (Nat.mul_le_mul_left _ ih)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.ChiTriv
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology GlobalTheory.TateLimit UpperTheory.V UpperTheory.V.Kum UpperTheory.V.K

theorem UpperTheory.V.K.chiTriv :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (D : LData L Ω l), HasMuQ l L → ∀ g, redChar D.chi 1 g = 1 := by
  intro l hl L Ω _ _ _ _ _ D hμ g
  obtain ⟨ζ, hζ⟩ : ∃ ζ : L, IsPrimitiveRoot ζ (l ^ 1) := by
    obtain ⟨ζ, hζ⟩ := hμ
    rw [pow_one]
    by_cases h2 : l = 2
    · rw [if_pos h2] at hζ
      exact ⟨ζ ^ 2, hζ.pow (by norm_num) (by rw [h2])⟩
    · rw [if_neg h2] at hζ
      exact ⟨ζ, hζ⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed L
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap L Ω).injective
  haveI : NeZero l := ⟨hl.out.ne_zero⟩
  haveI hE : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  have hζ' : IsPrimitiveRoot (algebraMap L Ω ζ) (l ^ 1) := hζ.map_of_injective (algebraMap L Ω).injective
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
  have hc : D.chi (QuotientGroup.mk g) = cyclotomicCharacter Ω l g.toRingEquiv := DFunLike.congr_fun D.hchi g
  apply Units.ext
  rw [redChar_coe, hc, Units.val_one, cyclotomicCharacter.toZModPow]
  refine (modularCyclotomicCharacter.unique Ω _ _ fun t ht => ?_).symm
  have ht' : (t : Ω) ^ l ^ 1 = 1 := by
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 ht, Units.val_one]
  rw [ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ ht', pow_one]
  obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one ht'
  rw [← hi, ← map_pow]
  exact g.commutes _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.ShaDualCard
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology GlobalTheory.TateLimit UpperTheory.V UpperTheory.V.Kum UpperTheory.V.K

private theorem mapH1_mem_sha {R G M M' I : Type} {Dd : I → Type} [CommRing R] [Group G] [TopologicalSpace G]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
    [AddCommGroup M'] [Module R M'] [TopologicalSpace M'] [IsTopologicalAddGroup M'] [ContinuousConstSMul R M']
    [∀ i, Group (Dd i)] [∀ i, TopologicalSpace (Dd i)] (φ : ∀ i, Dd i →* G) (hφ : ∀ i, Continuous (φ i))
    (ρ : Representation R G M) (ρ' : Representation R G M') (u : M →ₗ[R] M') (hu : Continuous u)
    (he : ∀ g m, u (ρ g m) = ρ' g (u m)) (x : H1 ρ) (hx : x ∈ Sha1 ρ φ hφ) :
    mapH1 ρ ρ' u hu he x ∈ Sha1 ρ' φ hφ := by
  simp only [Sha1, Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
  intro i
  have key : resH1 ρ' (φ i) (hφ i) (mapH1 ρ ρ' u hu he x) =
      mapH1 (ρ.comp (φ i)) (ρ'.comp (φ i)) u hu (fun g m => he _ m) (resH1 ρ (φ i) (hφ i) x) := by
    induction x using Submodule.Quotient.induction_on with
    | H z => rfl
  rw [key, hx i, map_zero]

private theorem mapH1_comp {R G M M' : Type} [CommRing R] [Group G] [TopologicalSpace G]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
    [AddCommGroup M'] [Module R M'] [TopologicalSpace M'] [IsTopologicalAddGroup M'] [ContinuousConstSMul R M']
    (ρ : Representation R G M) (ρ' : Representation R G M') (u : M →ₗ[R] M') (hu : Continuous u)
    (he : ∀ g m, u (ρ g m) = ρ' g (u m)) (w : M' →ₗ[R] M) (hw : Continuous w)
    (he' : ∀ g m, w (ρ' g m) = ρ g (w m)) (h : ∀ m, w (u m) = m) (x : H1 ρ) :
    mapH1 ρ' ρ w hw he' (mapH1 ρ ρ' u hu he x) = x := by
  induction x using Submodule.Quotient.induction_on with
  | H z => exact congrArg Submodule.Quotient.mk (Subtype.ext (funext fun g => h _))

private theorem card_sha_congr {R G M M' I : Type} {Dd : I → Type} [CommRing R] [Group G] [TopologicalSpace G]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
    [AddCommGroup M'] [Module R M'] [TopologicalSpace M'] [IsTopologicalAddGroup M'] [ContinuousConstSMul R M']
    [∀ i, Group (Dd i)] [∀ i, TopologicalSpace (Dd i)] (φ : ∀ i, Dd i →* G) (hφ : ∀ i, Continuous (φ i))
    (ρ : Representation R G M) (ρ' : Representation R G M') (u : M ≃ₗ[R] M') (hu : Continuous u)
    (hw : Continuous u.symm) (he : ∀ g m, u (ρ g m) = ρ' g (u m)) :
    Nat.card (Sha1 ρ φ hφ) = Nat.card (Sha1 ρ' φ hφ) := by
  have he' : ∀ g m, u.symm (ρ' g m) = ρ g (u.symm m) := fun g m => by
    rw [LinearEquiv.symm_apply_eq, he, LinearEquiv.apply_symm_apply]
  exact Nat.card_congr
    { toFun := fun x => ⟨_, mapH1_mem_sha φ hφ ρ ρ' u.toLinearMap hu he x.1 x.2⟩
      invFun := fun x => ⟨_, mapH1_mem_sha φ hφ ρ' ρ u.symm.toLinearMap hw he' x.1 x.2⟩
      left_inv := fun x => Subtype.ext (mapH1_comp ρ ρ' u.toLinearMap hu he u.symm.toLinearMap hw he'
        u.symm_apply_apply x.1)
      right_inv := fun x => Subtype.ext (mapH1_comp ρ' ρ u.symm.toLinearMap hw he' u.toLinearMap hu he
        u.apply_symm_apply x.1) }

theorem UpperTheory.V.K.shaDualCard :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (D : LData L Ω l) (n : ℤ), (∀ g, redChar D.chi 1 g = 1) → Nat.card (Sha1 (zd D n 1) (locFam D.S D.A) (continuous_locFam D.S D.A)) = Nat.card (ShaZm D 1 0) := by
  intro l _ L Ω _ _ _ _ _ D n h
  let ev : TDual (ZMod (l ^ 1)) (ZMod (l ^ 1)) →ₗ[ZMod (l ^ 1)] ZMod (l ^ 1) :=
    { toFun := fun φ => φ 1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hlin : ∀ (φ : TDual (ZMod (l ^ 1)) (ZMod (l ^ 1))) (m : ZMod (l ^ 1)), φ m = m * φ 1 :=
    fun φ m => by
      have := LinearMap.map_smul (show ZMod (l ^ 1) →ₗ[ZMod (l ^ 1)] ZMod (l ^ 1) from φ) m 1
      rw [smul_eq_mul, mul_one, smul_eq_mul] at this
      exact this
  have hev : Function.Bijective ev := by
    refine ⟨fun φ ψ h => TDual.ext fun m => ?_, fun y => ⟨y • TDual.mk LinearMap.id, ?_⟩⟩
    · rw [hlin φ, hlin ψ]; exact congrArg _ h
    · exact mul_one y
  have hn : ∀ g, redChar (D.chi ^ n) 1 g = 1 := fun g => by
    have : redChar (D.chi ^ n) 1 g = redChar D.chi 1 g ^ n := by
      simp only [redChar, MonoidHom.comp_apply, MonoidHom.zpow_apply, map_zpow]
    rw [this, h, one_zpow]
  refine card_sha_congr _ _ _ (zmTw D 1 0) (LinearEquiv.ofBijective ev hev) continuous_of_discreteTopology
    continuous_of_discreteTopology fun g m => ?_
  have h0 : ∀ x, zmTw D 1 0 g x = x := fun x => by simp [zmTw]
  rw [h0]
  change ((redChar D.chi 1 g : (ZMod (l ^ 1))ˣ) : ZMod (l ^ 1)) *
    m (((redChar (D.chi ^ n) 1 g⁻¹ : (ZMod (l ^ 1))ˣ) : ZMod (l ^ 1)) * 1) = m 1
  rw [h, hn, Units.val_one, one_mul, one_mul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.TensSurj
section
open scoped TensorProduct
open GlobalTheory.TateLimit

private theorem UpperTheory.V.K.padic_int_eq_int_add_mul (l : ℕ) [Fact l.Prime] (a : ℤ_[l]) (N : ℕ) (hN : 0 < N) :
    ∃ (k : ℤ) (b : ℤ_[l]), a = (k : ℤ_[l]) + (N : ℤ_[l]) * b := by
  have hN0 : (N : ℤ_[l]) ≠ 0 := by exact_mod_cast hN.ne'
  have h1 := PadicInt.unitCoeff_spec hN0
  have h2 := PadicInt.appr_spec (N : ℤ_[l]).valuation a
  rw [Ideal.mem_span_singleton] at h2
  obtain ⟨c, hc⟩ := h2
  refine ⟨(a.appr (N : ℤ_[l]).valuation : ℕ), ((PadicInt.unitCoeff hN0)⁻¹ : ℤ_[l]ˣ) * c, ?_⟩
  have h3 : (N : ℤ_[l]) * (((PadicInt.unitCoeff hN0)⁻¹ : ℤ_[l]ˣ) * c)
      = (l : ℤ_[l]) ^ (N : ℤ_[l]).valuation * c := by
    generalize PadicInt.unitCoeff hN0 = u at h1 ⊢
    generalize (l : ℤ_[l]) ^ (N : ℤ_[l]).valuation = q at h1 ⊢
    rw [h1]
    calc (u : ℤ_[l]) * q * (((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) * c)
        = ((u : ℤ_[l]) * ((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l])) * (q * c) := by ring
      _ = q * c := by rw [Units.mul_inv, one_mul]
  rw [h3, ← hc]
  push_cast
  ring

theorem UpperTheory.V.K.tensSurj :
    ∀ (l : ℕ) [Fact l.Prime] (T : Type) [AddCommGroup T], AddMonoid.IsTorsion T → Function.Surjective (fun t : T => ((1 : ℤ_[l]) ⊗ₜ[ℤ] t : ℤ_[l] ⊗[ℤ] T)) := by
  intro l _ T _ hT x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | add x y hx hy =>
    obtain ⟨s, rfl⟩ := hx
    obtain ⟨t, rfl⟩ := hy
    exact ⟨s + t, by simp [TensorProduct.tmul_add]⟩
  | tmul a t =>
    obtain ⟨N, hN, hNt⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 (hT t)
    obtain ⟨k, b, rfl⟩ := UpperTheory.V.K.padic_int_eq_int_add_mul l a N hN
    refine ⟨k • t, ?_⟩
    have e1 : ((N : ℤ_[l]) * b) ⊗ₜ[ℤ] t = (0 : ℤ_[l] ⊗[ℤ] T) := by
      have : (N : ℤ_[l]) * b = (N : ℤ) • b := by simp
      rw [this, TensorProduct.smul_tmul, natCast_zsmul, hNt, TensorProduct.tmul_zero]
    have e2 : (k : ℤ_[l]) = k • (1 : ℤ_[l]) := by simp
    show (1 : ℤ_[l]) ⊗ₜ[ℤ] (k • t) = _
    rw [TensorProduct.add_tmul, e1, add_zero, e2, TensorProduct.smul_tmul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.TensTors
section
open scoped TensorProduct
open GlobalTheory.TateLimit

theorem UpperTheory.V.K.tensTors :
    ∀ (l : ℕ) [Fact l.Prime] (H : Type) [AddCommGroup H] (x : ℤ_[l] ⊗[ℤ] H), IsOfFinAddOrder x → x ∈ LinearMap.range (LinearMap.lTensor ℤ_[l] (AddCommGroup.torsion H).subtype.toIntLinearMap) := by
  intro l _ H _ x hx
  let T := AddCommGroup.torsion H
  let g : H →ₗ[ℤ] (H ⧸ T) := (QuotientAddGroup.mk' T).toIntLinearMap
  have hg : Function.Surjective g := QuotientAddGroup.mk'_surjective T
  have hex : Function.Exact T.subtype.toIntLinearMap g := by
    intro h
    constructor
    · intro hh
      exact ⟨⟨h, (QuotientAddGroup.eq_zero_iff h).1 hh⟩, rfl⟩
    · rintro ⟨t, rfl⟩
      exact (QuotientAddGroup.eq_zero_iff _).2 t.2
  have hE := lTensor_exact ℤ_[l] hex hg
  haveI : IsAddTorsionFree (H ⧸ T) := inferInstance
  haveI : Module.Flat ℤ (H ⧸ T) := inferInstance
  obtain ⟨n, hn, hnx⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 hx
  let m : ℤ_[l] →ₗ[ℤ] ℤ_[l] := n • LinearMap.id
  have hm : Function.Injective m := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have : (n : ℤ_[l]) * a = 0 := by simpa [m] using ha
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (Nat.cast_eq_zero.1 h) hn.ne'
    · exact h
  have hinj := Module.Flat.rTensor_preserves_injective_linearMap (M := H ⧸ T) m hm
  have h0 : LinearMap.lTensor ℤ_[l] g x = 0 := by
    apply hinj
    have : LinearMap.rTensor (H ⧸ T) m = n • LinearMap.id := by
      ext a b
      simp [m, ← nsmul_eq_mul, TensorProduct.smul_tmul']
    rw [map_zero, this, LinearMap.smul_apply, LinearMap.id_apply, ← map_nsmul, hnx, map_zero]
  exact (hE x).1 h0
end

