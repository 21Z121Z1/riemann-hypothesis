import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0130
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0265
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0266
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0268
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0300
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0249
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0263
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0296
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0026
import GroundTheory.Brauer.Splitting
import GroundTheory.Brauer.SkolemNoether
import GroundTheory.Brauer.BaseChangeCSA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0287
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0135
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0230
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0306
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0223
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0285
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMaximumPrincipleWeightFiniteMvPolynomial

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFamConstLevelOne
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

namespace GlobalTheory.QFam

theorem isFam_const_of_isMF (ι : Type) (act : ι → SL(2, ℤ) → ι) (k : ℤ) (F : ℍ → ℂ)
    (h : IsMF k F) : IsFam act k fun _ => F := by
  intro i γ
  funext τ
  have hne : UpperHalfPlane.denom γ τ ^ k ≠ 0 := zpow_ne_zero _ (UpperHalfPlane.denom_ne_zero _ _)
  rw [ModularForm.SL_slash_apply]
  beta_reduce
  rw [h.smul_eq γ τ, zpow_neg, mul_right_comm, mul_inv_cancel₀ hne, one_mul]

theorem isFam_const_E4 (ι : Type) (act : ι → SL(2, ℤ) → ι) : IsFam act 4 (fun _ => ⇑E₄) :=
  isFam_const_of_isMF ι act 4 _ ⟨E₄, fun _ => rfl⟩

theorem isFam_const_E6 (ι : Type) (act : ι → SL(2, ℤ) → ι) : IsFam act 6 (fun _ => ⇑E₆) :=
  isFam_const_of_isMF ι act 6 _ ⟨E₆, fun _ => rfl⟩

theorem isFam_const_DD (ι : Type) (act : ι → SL(2, ℤ) → ι) : IsFam act 12 fun _ => DD :=
  isFam_const_of_isMF ι act 12 _ ReciprocityTheory.ChartRestriction.L1.isMF_DD

theorem isFam_const_level_one (ι : Type) (act : ι → SL(2, ℤ) → ι) :
    (∀ (k : ℤ) (F : ℍ → ℂ), IsMF k F → IsFam act k fun _ => F) ∧ IsFam act 4 (fun _ => ⇑E₄) ∧
      IsFam act 6 (fun _ => ⇑E₆) ∧ IsFam act 12 fun _ => DD :=
  ⟨isFam_const_of_isMF ι act, isFam_const_E4 ι act, isFam_const_E6 ι act, isFam_const_DD ι act⟩

end GlobalTheory.QFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHilbertSchemeRepresentableOfOpenCover
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch GlobalTheory.HilbGlue Opposite

theorem GlobalTheory.HilbGlue.isSheaf_hilbFunctor {S Z : Scheme.{0}} (z : Z ⟶ S) (r : ℕ) :
    Presieve.IsSheaf Scheme.zariskiTopology (hilbFunctor z r) := by
  rw [Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  rintro Y P hP
  obtain ⟨(𝒰 : Scheme.OpenCover Y), rfl⟩ := Scheme.exists_cover_of_mem_pretopology hP
  rw [Presieve.isSheafFor_arrows_iff]
  intro x hx
  exact existsUnique_of_exists_of_unique (GlobalTheory.T.hilbert_point_glue_open_cover z r Y 𝒰 x fun i j R b c h => hx i j R b c h)
    fun y y' h h' => GlobalTheory.T.hilbert_point_eq_of_open_cover z r Y 𝒰 y y' fun i => (h i).trans (h' i).symm

theorem GlobalTheory.HilbGlue.isHilbRep_of_cover : ∀ (S Z : Scheme.{0}) (z : Z ⟶ S), IsFinite z → Flat z →
    LocallyOfFinitePresentation z → ∀ r : ℕ, (∀ s : S, ∃ W : S.Opens, s ∈ W ∧ IsHilbRep (z ∣_ W) r) →
    IsHilbRep z r := by
  intro S Z z _ _ _ r hS
  have hloc : ∀ s : S, ∃ W : S.Opens, s ∈ W ∧ ∃ (T : Scheme.{0}) (y : HPt z r T) (π : T ⟶ W.toScheme),
      IsProper π ∧ y.1 = π ≫ W.ι ∧ ∀ (Y : Scheme.{0}) (x : HPt z r Y) (b : Y ⟶ W.toScheme),
        x.1 = b ≫ W.ι → ∃! c : Y ⟶ T, HPt.map c y = x := fun s => by
    obtain ⟨W, hs, hW⟩ := hS s
    exact ⟨W, hs, GlobalTheory.T.hilbertFunctor_local_representing_data_of_restrict z r W hW⟩
  have hloc' := hloc
  choose W hsW T y π _ hπ huniq using hloc
  have hrep : (hilbFunctor z r).IsRepresentable :=
    GlobalTheory.GenTorsor.isRepresentable_of_cover (hilbFunctor z r) (GlobalTheory.HilbGlue.isSheaf_hilbFunctor z r) (hilbProj z r) W
      (eq_top_iff.2 fun s _ => TopologicalSpace.Opens.mem_iSup.2 ⟨s, hsW s⟩) T y π hπ huniq
  obtain ⟨H, u, hu⟩ : ∃ (H : Scheme.{0}) (u : HPt z r H), ∀ (T : Scheme.{0}) (x : HPt z r T),
      ∃! c : T ⟶ H, HPt.map c u = x := by
    obtain ⟨H, ⟨e⟩⟩ := hrep.has_representation
    have h : ∀ {T : Scheme.{0}} (c : T ⟶ H), HPt.map c (e.homEquiv (𝟙 H)) = e.homEquiv c :=
      fun c => (e.homEquiv_eq c).symm
    exact ⟨H, e.homEquiv (𝟙 H), fun T x => ⟨e.homEquiv.symm x, (h _).trans (e.homEquiv.apply_symm_apply x),
      fun c hc => e.homEquiv.eq_symm_apply.2 ((h c).symm.trans hc)⟩⟩
  have hprop : IsProper u.1 := GlobalTheory.T.isProper_of_represents_hilbertFunctor_of_local z r H u hu hloc'
  obtain ⟨h, I⟩ := u
  refine ⟨H, h, I.1.subscheme, I.1.subschemeι, hprop, inferInstance, I.2.1, I.2.2.1, I.2.2.2, ?_⟩
  intro T g V v _ h1 h2 h3
  have hv' : IsFinFlatRk (v ≫ pullback.snd z g) r := ⟨h1, h2, h3⟩
  obtain ⟨c, hc, hcu⟩ := hu T (mkPt g v hv')
  have key : ∀ (f : T ⟶ H) (hf : f ≫ h = g), HPt.map f ⟨h, I⟩ = mkPt g v hv' ↔
      ∃ w : V ⟶ I.1.subscheme, IsPullback v w (bc z f h g hf) I.1.subschemeι := by
    intro f hf
    rw [mkPt, HPt.map_eq_mk_iff f ⟨h, I⟩ hf]
    exact GlobalTheory.HilbGlue.comap_eq_ker_iff (bc z f h g hf) I.1 v
  have hcg : c ≫ h = g := congrArg Sigma.fst hc
  exact ⟨c, ⟨hcg, (key c hcg).1 hc⟩, fun f ⟨hf, hw⟩ => hcu f ((key f hf).2 hw)⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegrallyClosedInClosureLocalizationStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegrallyClosedIn_etale_genFib_of_injective : ∀ (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Algebra A R], Function.Injective (algebraMap A R) →
    ∀ (D : Type) [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib A R) D]
    [Module.Finite (GlobalTheory.LocAcyc.GenFib A R) D] [Algebra.Etale (GlobalTheory.LocAcyc.GenFib A R) D],
    letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D
    IsIntegrallyClosedIn (GlobalTheory.KeyOriginNoeth.closure A R D)
      (Localization (Algebra.algebraMapSubmonoid (GlobalTheory.KeyOriginNoeth.closure A R D)
        (nonZeroDivisors R))) := by
  first | (exact @GlobalTheory.KeyOriginNoeth.isIntegrallyClosedIn_closure_localization) | (exact GlobalTheory.KeyOriginNoeth.isIntegrallyClosedIn_closure_localization) | (intros; apply GlobalTheory.KeyOriginNoeth.isIntegrallyClosedIn_closure_localization  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsModularFormLevelOneOfInvariantQExpansion
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

namespace GlobalTheory.QFam

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in

theorem _root_.GlobalTheory.QFam.isMF_of_invariant_of_hasQ : ∀ (N : ℕ) (k : ℤ) (f : ℍ → ℂ)
    (a : ℕ → ℂ), 0 < N →
    (∀ γ : SL(2, ℤ), f ∣[k] γ = f) → _root_.GlobalTheory.QFam.HasQ N f a → _root_.ReciprocityTheory.ChartRestriction.L1.IsMF k f := by
  intro N k f a hN hinv h
  refine ⟨{ toFun := f, slash_action_eq' := ?_, holo' := ?_, bdd_at_cusps' := ?_ },
    fun _ => rfl⟩
  · rintro _ ⟨γ, rfl⟩
    exact (ModularForm.SL_slash f γ).symm.trans (hinv γ)
  · exact h.mdifferentiable hN
  · intro c hc
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    rw [hinv γ]
    exact (_root_.GlobalTheory.QFam.hasQ_mdifferentiable_and_isBoundedAtImInfty N f a hN h).2

end GlobalTheory.QFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenStabilizerSchwartzBruhat
section
open Matrix Topology GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM

namespace GlobalTheory.OmAStab

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isLocallyConstant_of_isOpen_ker {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] (χ : G →* H) (hχ : IsOpen (χ.ker : Set G)) : IsLocallyConstant χ := by
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun g0 => ?_
  have hn : (fun g => g0⁻¹ * g) ⁻¹' (χ.ker : Set G) ∈ 𝓝 g0 :=
    (hχ.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp)
  filter_upwards [hn] with g hg
  have hg' : χ (g0⁻¹ * g) = 1 := hg
  rw [map_mul, map_inv, inv_mul_eq_one] at hg'
  exact hg'.symm

theorem continuous_invT_val {D : Type} [Fintype D] [DecidableEq D] :
    Continuous fun h : GL D k => (invT h).val :=
  (Units.continuous_coe_inv (M := Matrix D D k)).matrix_transpose

theorem continuous_invT_inv_val {D : Type} [Fintype D] [DecidableEq D] :
    Continuous fun h : GL D k => ((invT h)⁻¹).val :=
  (Units.continuous_val (M := Matrix D D k)).matrix_transpose

theorem isLocallyConstant_comp_invT {A D : Type} [Fintype A] [Fintype D] [DecidableEq D]
    {Φ : Matrix A D k → ℂ} (hΦ : Φ ∈ SB (Matrix A D k)) :
    IsLocallyConstant fun h : GL D k => fun X : Matrix A D k => Φ (X * (invT h).val) := by
  obtain ⟨hl, hK⟩ : IsLocallyConstant Φ ∧ HasCompactSupport Φ := hΦ
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun h0 => ?_
  set M : GL D k → Matrix D D k := fun h => (invT h).val with hM
  set N : GL D k → Matrix D D k := fun h => ((invT h)⁻¹).val with hN
  have hMc : Continuous M := continuous_invT_val
  have hNc : Continuous N := continuous_invT_inv_val
  have hMN : ∀ h, M h * N h = 1 := fun h => Units.mul_inv (invT h)
  have hNM : ∀ h, N h * M h = 1 := fun h => Units.inv_mul (invT h)
  have hq : IsLocallyConstant fun p : GL D k × Matrix A D k => Φ (p.2 * M p.1) :=
    hl.comp_continuous (continuous_snd.matrix_mul (hMc.comp continuous_fst))
  have hr : IsLocallyConstant fun p : GL D k × Matrix A D k => Φ (p.2 * N p.1 * M h0) :=
    hl.comp_continuous ((continuous_snd.matrix_mul (hNc.comp continuous_fst)).matrix_mul continuous_const)
  have hK1 : IsCompact ((fun Y => Y * N h0) '' tsupport Φ) :=
    hK.isCompact.image (continuous_id.matrix_mul continuous_const)
  have htend : ∀ X : Matrix A D k, Filter.Tendsto (fun p : GL D k × Matrix A D k => (h0, p.2))
      (𝓝 (h0, X)) (𝓝 (h0, X)) := fun X => (continuous_const.prodMk continuous_snd).tendsto' _ _ rfl
  have e1 : ∀ᶠ h in 𝓝 h0, ∀ X ∈ (fun Y => Y * N h0) '' tsupport Φ, Φ (X * M h) = Φ (X * M h0) := by
    refine hK1.eventually_forall_of_forall_eventually fun X _ => ?_
    have a1 := hq.eventually_eq (h0, X)
    have a2 := (htend X).eventually (hq.eventually_eq (h0, X))
    filter_upwards [a1, a2] with p hp1 hp2
    exact hp1.trans hp2.symm
  have e2 : ∀ᶠ h in 𝓝 h0, ∀ Y ∈ tsupport Φ, Φ (Y * N h * M h0) = Φ Y := by
    refine hK.isCompact.eventually_forall_of_forall_eventually fun Y _ => ?_
    have a2 := (continuous_snd.tendsto (h0, Y)).eventually (hl.eventually_eq Y)
    filter_upwards [hr.eventually_eq (h0, Y), a2] with p hp hp2
    refine hp.trans (Eq.trans ?_ hp2.symm)
    show Φ (Y * N h0 * M h0) = Φ Y
    rw [Matrix.mul_assoc, hNM, Matrix.mul_one]
  filter_upwards [e1, e2] with h h1 h2
  funext X
  show Φ (X * M h) = Φ (X * M h0)
  by_cases hA : X * M h0 ∈ tsupport Φ
  · exact h1 X ⟨X * M h0, hA, by simp only [Matrix.mul_assoc, hMN, Matrix.mul_one]⟩
  by_cases hB : X * M h ∈ tsupport Φ
  · have := h2 _ hB
    rw [Matrix.mul_assoc X, hMN, Matrix.mul_one] at this
    exact this.symm
  rw [image_eq_zero_of_notMem_tsupport hA, image_eq_zero_of_notMem_tsupport hB]

theorem isOpen_omA_stab : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a d : ℕ) (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar β → ∀ Φ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k),
      IsOpen {h : GL (Fin d) k | GlobalTheory.SplitFlip.omA ν β 1 h Φ = Φ} := by
  intro k _ _ _ _ a d ν β hβ Φ hΦ
  have hb : IsLocallyConstant fun h : GL (Fin d) k => β (gdet h) :=
    (isLocallyConstant_of_isOpen_ker β hβ).comp_continuous Matrix.GeneralLinearGroup.continuous_det
  have hn : IsLocallyConstant fun h : GL (Fin d) k => GlobalTheory.SplitWeil.nabs k (gdet h) :=
    (GlobalTheory.SplitWeil.isLocallyConstant_nabs k).comp_continuous Matrix.GeneralLinearGroup.continuous_det
  have hc : IsLocallyConstant fun h : GL (Fin d) k => omA ν β 1 h Φ := by
    refine (IsLocallyConstant.iff_eventually_eq _).mpr fun h0 => ?_
    filter_upwards [hb.eventually_eq h0, hn.eventually_eq h0,
      (isLocallyConstant_comp_invT hΦ).eventually_eq h0] with h e1 e2 e3
    funext X
    have e4 := congrFun e3 X
    simp only [omA, apow, inv_one, Units.val_one, Matrix.one_mul, e1, e2, e4]
  exact hc.isOpen_fiber Φ

end GlobalTheory.OmAStab
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReducedNormOfReducedNorm
section
noncomputable section

namespace GlobalTheory.Nrd

open scoped TensorProduct

section Def

variable (F C : Type) [Field F] [Ring C] [Algebra F C]

def deg : ℕ := Nat.sqrt (Module.finrank F C)

def IsReducedNormOf (x : C) (a : F) : Prop :=
  ∀ (L : Type) [Field L] (ι : F →+* L) (Ψ : C →+* Matrix (Fin (deg F C)) (Fin (deg F C)) L),
    (∀ c : F, Ψ (algebraMap F C c) = Matrix.scalar (Fin (deg F C)) (ι c)) → (Ψ x).det = ι a

open Classical in

def reducedNorm (x : C) : F :=
  if h : ∃ a, IsReducedNormOf F C x a then Classical.choose h else 0

end Def

theorem det_eq_det_of_semilinear {F C : Type} [Field F] [Ring C] [Algebra F C] [FiniteDimensional F C]
    [Algebra.IsCentral F C] [IsSimpleRing C] {L : Type} [Field L] (ι : F →+* L) {n : ℕ}
    (Ψ₁ Ψ₂ : C →+* Matrix (Fin n) (Fin n) L)
    (h₁ : ∀ c, Ψ₁ (algebraMap F C c) = Matrix.scalar (Fin n) (ι c))
    (h₂ : ∀ c, Ψ₂ (algebraMap F C c) = Matrix.scalar (Fin n) (ι c)) (x : C) :
    (Ψ₁ x).det = (Ψ₂ x).det := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Matrix.det_fin_zero]
  haveI : NeZero n := ⟨hn.ne'⟩
  letI : Algebra F L := ι.toAlgebra
  have hsc : ∀ c : F, Matrix.scalar (Fin n) (ι c) = algebraMap F (Matrix (Fin n) (Fin n) L) c := by
    intro c
    ext i j
    simp [Matrix.algebraMap_matrix_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
    rfl
  let f₁ : C →ₐ[F] Matrix (Fin n) (Fin n) L := { Ψ₁ with commutes' := fun c ↦ by simp [h₁, hsc] }
  let f₂ : C →ₐ[F] Matrix (Fin n) (Fin n) L := { Ψ₂ with commutes' := fun c ↦ by simp [h₂, hsc] }
  let g₁ : L ⊗[F] C →ₐ[L] Matrix (Fin n) (Fin n) L :=
    Algebra.TensorProduct.lift (Algebra.ofId L _) f₁ (fun l y ↦ Algebra.commute_algebraMap_left l _)
  let g₂ : L ⊗[F] C →ₐ[L] Matrix (Fin n) (Fin n) L :=
    Algebra.TensorProduct.lift (Algebra.ofId L _) f₂ (fun l y ↦ Algebra.commute_algebraMap_left l _)
  obtain ⟨u, hu⟩ := GroundTheory.Brauer.exists_unit_conj g₁ g₂
  have h := hu ((1 : L) ⊗ₜ x)
  have e₁ : g₁ ((1 : L) ⊗ₜ x) = Ψ₁ x := by
    simp only [g₁]; erw [Algebra.TensorProduct.lift_tmul]; simp [f₁]
  have e₂ : g₂ ((1 : L) ⊗ₜ x) = Ψ₂ x := by
    simp only [g₂]; erw [Algebra.TensorProduct.lift_tmul]; simp [f₂]
  rw [e₁, e₂] at h
  rw [h, Matrix.det_units_conj]

end GlobalTheory.Nrd

namespace GlobalTheory.Nrd
open scoped TensorProduct

variable {F C : Type} [Field F] [Ring C] [Algebra F C] [FiniteDimensional F C]
    [Algebra.IsCentral F C] [IsSimpleRing C]

theorem exists_galois_split : ∃ (E : Type) (_ : Field E) (_ : Algebra F E), FiniteDimensional F E ∧ IsGalois F E ∧
    ∃ Ψ : C →+* Matrix (Fin (deg F C)) (Fin (deg F C)) E,
      (∀ c, Ψ (algebraMap F C c) = Matrix.scalar _ (algebraMap F E c)) ∧ ∀ x, IsUnit (Ψ x) ↔ IsUnit x := by
  obtain ⟨E, _, _, hfin, hgal, n, ⟨φ⟩⟩ := GroundTheory.Brauer.exists_isGalois_splits (K := F) C
  have h : Module.finrank F C = n ^ 2 := by
    have := φ.toLinearEquiv.finrank_eq
    rw [Module.finrank_baseChange, Module.finrank_matrix, Fintype.card_fin,
      Module.finrank_self, mul_one] at this
    rw [this, sq]
  have hd : deg F C = n := by rw [deg, h, Nat.sqrt_eq']
  subst hd
  refine ⟨E, inferInstance, inferInstance, hfin, hgal,
    (φ : E ⊗[F] C →+* _).comp (Algebra.TensorProduct.includeRight : C →ₐ[F] E ⊗[F] C).toRingHom, ?_, ?_⟩
  · intro c
    have h1 : (Algebra.TensorProduct.includeRight : C →ₐ[F] E ⊗[F] C) (algebraMap F C c)
        = algebraMap E (E ⊗[F] C) (algebraMap F E c) := by
      rw [AlgHom.commutes, IsScalarTower.algebraMap_apply F E (E ⊗[F] C)]
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at *
    rw [h1]
    erw [AlgEquiv.commutes]
    ext i j
    simp [Matrix.algebraMap_matrix_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
  · intro x
    change IsUnit (φ ((1 : E) ⊗ₜ x)) ↔ IsUnit x
    rw [MulEquiv.isUnit_map φ, GlobalTheory.ReducedNormExists.isUnit_one_tmul_iff]

theorem exists_isReducedNormOf (x : C) : ∃ a, IsReducedNormOf F C x a := by
  obtain ⟨E, _, _, _, _, Ψ, hΨ, -⟩ := exists_galois_split (F := F) (C := C)
  have hfix : (Ψ x).det ∈ (⊥ : IntermediateField F E) := by
    refine (IsGalois.mem_bot_iff_fixed _).mpr fun g ↦ ?_
    have := det_eq_det_of_semilinear (algebraMap F E) Ψ (((g : E →+* E)).mapMatrix.comp Ψ) hΨ
      (fun c ↦ by
        simp only [RingHom.coe_comp, Function.comp_apply, hΨ]
        ext i j; simp [Matrix.scalar_apply, Matrix.diagonal_apply]; split_ifs <;> simp) x
    have h2 := RingHom.map_det (g : E →+* E) (Ψ x)
    calc g (Ψ x).det = (g : E →+* E) (Ψ x).det := rfl
      _ = _ := h2
      _ = (Ψ x).det := this.symm
  obtain ⟨a, ha⟩ := IntermediateField.mem_bot.mp hfix
  refine ⟨a, fun L _ ι Φ hΦ ↦ ?_⟩
  letI : Algebra F L := ι.toAlgebra
  let M := AlgebraicClosure L
  let jE : E →ₐ[F] M := IsAlgClosed.lift
  have hιM : ∀ c : F, algebraMap F M c = algebraMap L M (ι c) := fun c ↦
    IsScalarTower.algebraMap_apply F L M c
  have key := det_eq_det_of_semilinear (algebraMap F M) ((jE : E →+* M).mapMatrix.comp Ψ)
    ((algebraMap L M).mapMatrix.comp Φ)
    (fun c ↦ by
      simp only [RingHom.coe_comp, Function.comp_apply, hΨ]
      ext i j; simp [Matrix.scalar_apply, Matrix.diagonal_apply]; split_ifs <;> simp)
    (fun c ↦ by
      simp only [RingHom.coe_comp, Function.comp_apply, hΦ]
      ext i j; simp [Matrix.scalar_apply, Matrix.diagonal_apply, hιM]; split_ifs <;> simp) x
  simp only [RingHom.coe_comp, Function.comp_apply, ← RingHom.map_det] at key
  rw [← ha] at key
  have : (jE : E →+* M) (algebraMap F E a) = algebraMap L M (ι a) := by
    change jE (algebraMap F E a) = _
    rw [AlgHom.commutes, hιM]
  rw [this] at key
  exact ((algebraMap L M).injective key).symm

end GlobalTheory.Nrd

namespace GlobalTheory.Nrd
open scoped TensorProduct

variable {F C : Type} [Field F] [Ring C] [Algebra F C] [FiniteDimensional F C]
    [Algebra.IsCentral F C] [IsSimpleRing C]

theorem isReducedNormOf_reducedNorm (x : C) : IsReducedNormOf F C x (reducedNorm F C x) := by
  classical
  have h := exists_isReducedNormOf (F := F) (C := C) x
  unfold reducedNorm
  rw [dif_pos h]
  exact Classical.choose_spec h

theorem det_eq_reducedNorm {n : Type} [Fintype n] [DecidableEq n] (hn : Fintype.card n = deg F C)
    {L : Type} [Field L] (ι : F →+* L) (Ψ : C →+* Matrix n n L)
    (hΨ : ∀ c, Ψ (algebraMap F C c) = Matrix.scalar n (ι c)) (x : C) :
    (Ψ x).det = ι (reducedNorm F C x) := by
  let e : n ≃ Fin (deg F C) := Fintype.equivFinOfCardEq hn
  let Ψ' : C →+* Matrix (Fin (deg F C)) (Fin (deg F C)) L :=
    (Matrix.reindexAlgEquiv L L e).toRingEquiv.toRingHom.comp Ψ
  have h := isReducedNormOf_reducedNorm (F := F) (C := C) x L ι Ψ' (fun c ↦ by
    simp only [Ψ', RingHom.coe_comp, Function.comp_apply, hΨ]
    ext i j
    simp [Matrix.reindexAlgEquiv_apply, Matrix.scalar_apply, Matrix.diagonal_apply])
  rw [← h]
  simp [Ψ', Matrix.reindexAlgEquiv_apply, Matrix.det_reindex_self]

theorem reducedNorm_mul (x y : C) :
    reducedNorm F C (x * y) = reducedNorm F C x * reducedNorm F C y := by
  obtain ⟨E, _, _, _, _, Ψ, hΨ, -⟩ := exists_galois_split (F := F) (C := C)
  have hc : Fintype.card (Fin (deg F C)) = deg F C := Fintype.card_fin _
  apply (algebraMap F E).injective
  rw [map_mul, ← det_eq_reducedNorm hc _ Ψ hΨ, ← det_eq_reducedNorm hc _ Ψ hΨ,
    ← det_eq_reducedNorm hc _ Ψ hΨ, map_mul, Matrix.det_mul]

theorem reducedNorm_algebraMap (c : F) :
    reducedNorm F C (algebraMap F C c) = c ^ deg F C := by
  obtain ⟨E, _, _, _, _, Ψ, hΨ, -⟩ := exists_galois_split (F := F) (C := C)
  have hc : Fintype.card (Fin (deg F C)) = deg F C := Fintype.card_fin _
  apply (algebraMap F E).injective
  rw [← det_eq_reducedNorm hc _ Ψ hΨ, hΨ, map_pow]
  simp [Matrix.scalar_apply, Matrix.det_diagonal]

theorem reducedNorm_one : reducedNorm F C 1 = 1 := by
  simpa using reducedNorm_algebraMap (F := F) (C := C) 1

end GlobalTheory.Nrd

namespace GlobalTheory.Nrd
open scoped TensorProduct
open NumberField

section Inv
variable {F C : Type} [Field F] [NumberField F] [IsCMField F] [Ring C] [Algebra F C]
    [FiniteDimensional F C] [Algebra.IsCentral F C] [IsSimpleRing C]

end Inv

section BaseChange
variable {F C : Type} [Field F] [Ring C] [Algebra F C] [FiniteDimensional F C]
    [Algebra.IsCentral F C] [IsSimpleRing C]

end BaseChange

end GlobalTheory.Nrd

namespace GlobalTheory.Nrd
open scoped TensorProduct

section Map
variable {F C : Type} [Field F] [Ring C] [Algebra F C] [FiniteDimensional F C]
    [Algebra.IsCentral F C] [IsSimpleRing C]

def reducedNormHom (F C : Type) [Field F] [Ring C] [Algebra F C] [FiniteDimensional F C]
    [Algebra.IsCentral F C] [IsSimpleRing C] : C →* F where
  toFun := reducedNorm F C
  map_one' := reducedNorm_one
  map_mul' := reducedNorm_mul

@[simp] theorem reducedNormHom_apply (x : C) : reducedNormHom F C x = reducedNorm F C x := rfl

end Map

end GlobalTheory.Nrd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerAffineHilbertTensorPullbackEqMap
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace GlobalTheory.HilbAff

theorem ker_kappa_xI_comap : ∀ (A B C : Type) [CommRing A] [CommRing B] [Algebra A B] [CommRing C] [Algebra A C] (J : Ideal (C ⊗[A] B)) (Z : Scheme.{0}) (h : Z ⟶ Spec (CommRingCat.of C)) (U : Z.affineOpens), letI := (GlobalTheory.HilbAff.secAlg A (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C))) U).toAlgebra; ∃ φ : C →ₐ[A] Γ(Z, U), φ.toRingHom = GlobalTheory.HilbAff.secAlg C h U ∧ RingHom.ker (GlobalTheory.HilbAff.kappa A B (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C))) ((GlobalTheory.HilbAff.xI A B C J).comap (GlobalTheory.HilbAff.bc A B (Spec.map (CommRingCat.ofHom (algebraMap A C))) h)) U) = J.map (Algebra.TensorProduct.map φ (AlgHom.id A B)) := by
  intro A B C _ _ _ _ _ J Z h U
  letI := (secAlg A (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C))) U).toAlgebra
  let φ : C →ₐ[A] Γ(Z, U) :=
    { toRingHom := secAlg C h U
      commutes' := fun a => by
        show secAlg C h U (algebraMap A C a) = secAlg A (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C))) U a
        rw [secAlg_comp]; rfl }
  refine ⟨φ, rfl, ?_⟩
  haveI : IsAffineHom (pullback.snd (str A B) (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)))) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) inferInstance
  have hW : IsAffineOpen ((pullback.snd (str A B) (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)))) ⁻¹ᵁ (U : Z.Opens)) :=
    U.2.preimage _
  have hk := Scheme.IdealSheafData.ker_subschemeι_app
    ((xI A B C J).comap (bc A B (Spec.map (CommRingCat.ofHom (algebraMap A C))) h)) ⟨_, hW⟩
  rw [ker_kappa_eq]
  erw [hk]
  rw [GlobalTheory.T.idealSheaf_comap_ideal_affineOpen_of_isAffine, GlobalTheory.T.affineHilbertIdealSheafOfQuotient_ideal_top, Ideal.map_map, GlobalTheory.T.affineHilbertBaseChange_appLE_comp_specTensor A B C Z h U φ rfl, ← Ideal.map_map,
    Ideal.comap_map_of_bijective _ (GlobalTheory.T.sectionTensorPullbackRingHom_bijective A B _ U)]
  rfl

end GlobalTheory.HilbAff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMaximumPrincipleWeightFiniteMvPolynomialStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_maximum_principle_weight_finite_mvPolynomial : ∀ (d : ℕ) (B : Type) [CommRing B] [IsDomain B] [Algebra (MvPolynomial (Fin d) ℚ) B] [Module.Finite (MvPolynomial (Fin d) ℚ) B], Function.Injective (algebraMap (MvPolynomial (Fin d) ℚ) B) → (letI : TopologicalSpace (B →+* ℂ) := TopologicalSpace.induced (fun x : B →+* ℂ => (x : B → ℂ)) inferInstance; ∀ (ψ : (B →+* ℂ) → ℝ), Continuous ψ → ∀ s : B, s ≠ 0 → ∀ (x₀ : B →+* ℂ) (δ : ℝ), 0 < δ → ∃ (W K : Set (B →+* ℂ)), W ∈ nhds x₀ ∧ IsCompact K ∧ (∀ x ∈ K, x s ≠ 0) ∧ ∀ (N : ℕ) (f : B) (R : ℝ), (∀ x ∈ K, ‖x f‖ * Real.exp (-(N * ψ x)) ≤ R) → ∀ y ∈ W, ‖y f‖ * Real.exp (-(N * ψ y)) ≤ Real.exp (δ * N) * R) := by
  first | exact @GlobalTheory.local_maximum_principle_weight_finite_mvPolynomial_algebra | exact GlobalTheory.local_maximum_principle_weight_finite_mvPolynomial_algebra | (intros; apply GlobalTheory.local_maximum_principle_weight_finite_mvPolynomial_algebra <;> assumption)
end

