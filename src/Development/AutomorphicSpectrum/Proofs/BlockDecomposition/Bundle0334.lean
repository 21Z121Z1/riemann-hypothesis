import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import GroundTheory.AutomorphicForms.Bundle0020
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0324
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeRationalSubspace
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.Degree

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ}

theorem basisMat_transpose_eq (W : Submodule E (Fin n → E)) :
    ((basisMat W)ᵀ : Fin (Module.finrank E W) → Fin n → E) =
      W.subtype ∘ (Module.finBasis E W) := by
  funext j i
  rfl

theorem basisMat_linearIndependent (W : Submodule E (Fin n → E)) :
    LinearIndependent E (basisMat W)ᵀ := by
  rw [basisMat_transpose_eq]
  exact (Module.finBasis E W).linearIndependent.map' W.subtype W.ker_subtype

theorem span_basisMat (W : Submodule E (Fin n → E)) :
    Submodule.span E (Set.range (basisMat W)ᵀ) = W := by
  rw [basisMat_transpose_eq, Set.range_comp, ← Submodule.map_span, (Module.finBasis E W).span_eq,
    Submodule.map_top, Submodule.range_subtype]

theorem mul_transpose_apply {κ : Type} [Fintype κ] (g : GL (Fin n) E) (M : Matrix (Fin n) κ E) (j : κ) :
    (g.val * M)ᵀ j = Matrix.toLin' g.val (Mᵀ j) := by
  funext i
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem ker_toLin'_eq_bot (g : GL (Fin n) E) : LinearMap.ker (Matrix.toLin' g.val) = ⊥ := by
  refine LinearMap.ker_eq_bot.2 fun a b hab => ?_
  have h := congrArg (Matrix.toLin' (g⁻¹ : GL (Fin n) E).val) hab
  simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec] using h

theorem frame_rat {κ : Type} [Fintype κ] (x : GA E n) (g : GL (Fin n) E) (M : Matrix (Fin n) κ E) :
    ((ratGL E n g * x)⁻¹ : GA E n).val * (g.val * M).map (algebraMap E (Ad E)) =
      (x⁻¹ : GA E n).val * M.map (algebraMap E (Ad E)) := by
  have hr : (g.val * M).map (algebraMap E (Ad E)) =
      (ratGL E n g).val * M.map (algebraMap E (Ad E)) := by
    rw [Matrix.map_mul]
    rfl
  rw [hr, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (ratGL E n g)⁻¹.val,
    Units.inv_mul, Matrix.one_mul]

theorem degG_rat {κ : Type} [Fintype κ] [DecidableEq κ] (x : GA E n) (g : GL (Fin n) E)
    (M : Matrix (Fin n) κ E) : degG (ratGL E n g * x) (g.val * M) = degG x M := by
  simp only [degG, frame_rat]

theorem degRat_of_degBasisG : DegBasisG → DegRat := by
  intro h E _ _ _ n x g W
  have hli : LinearIndependent E (g.val * basisMat W)ᵀ := by
    have e : (fun j => (g.val * basisMat W)ᵀ j) = Matrix.toLin' g.val ∘ fun j => (basisMat W)ᵀ j :=
      funext (mul_transpose_apply g (basisMat W))
    have l : LinearIndependent E (fun j => (g.val * basisMat W)ᵀ j) :=
      e ▸ (basisMat_linearIndependent W).map' _ (ker_toLin'_eq_bot g)
    exact l
  have hspan : Submodule.span E (Set.range (g.val * basisMat W)ᵀ) = img g W := by
    have e : Set.range (g.val * basisMat W)ᵀ = Matrix.toLin' g.val '' Set.range (basisMat W)ᵀ :=
      Set.ext fun y => ⟨fun ⟨j, hj⟩ => ⟨(basisMat W)ᵀ j, ⟨j, rfl⟩,
          (mul_transpose_apply g (basisMat W) j).symm.trans hj⟩,
        fun ⟨_, ⟨j, hj⟩, hy⟩ => ⟨j, (mul_transpose_apply g (basisMat W) j).trans (hj ▸ hy)⟩⟩
    rw [e, ← Submodule.map_span, span_basisMat]
    rfl
  have key := h E n (Fin (Module.finrank E W)) (ratGL E n g * x) (g.val * basisMat W) hli
  rw [hspan] at key
  rw [← key, degG_rat]
  rfl

end GlobalTheory.CompanionTheory.Degree

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeSubmoduleBound
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.DegreeSubmod

theorem exists_leftInv {K ι κ : Type} [Field K] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (M : Matrix ι κ K) (h : LinearIndependent K Mᵀ) : ∃ Y : Matrix κ ι K, Y * M = 1 := by
  have hinj : Function.Injective M.mulVecLin := by
    have : Function.Injective M.mulVec := Matrix.mulVec_injective_iff.2 h
    exact this
  obtain ⟨g, hg⟩ := M.mulVecLin.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have h2 : LinearMap.toMatrix' (g ∘ₗ M.mulVecLin) = LinearMap.toMatrix' g * M := by
    rw [LinearMap.toMatrix'_comp, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']
  rw [← h2, hg]
  simp

theorem map_fromCols {R S ι κ κ' : Type} (f : R → S) (P : Matrix ι κ R) (Q : Matrix ι κ' R) :
    (fromCols P Q).map f = fromCols (P.map f) (Q.map f) := by
  ext i (j | j) <;> rfl

theorem log_ineq {K ι : Type} [Field K] [Fintype ι] [DecidableEq ι] (N : Fam K ι) (hN : IsWedge N) (hS : WedgeSub)
    {κ₀ κ₁ κ₂ : Type} [Fintype κ₀] [DecidableEq κ₀] [Fintype κ₁] [DecidableEq κ₁] [Fintype κ₂] [DecidableEq κ₂]
    (B : Matrix ι κ₀ K) (A : Matrix ι κ₁ K) (C : Matrix ι κ₂ K)
    (h0 : N (κ₀ ⊕ (κ₁ ⊕ κ₂)) (fromCols B (fromCols A C)) ≠ 0) (h1 : N κ₀ B ≠ 0)
    (h2 : N (κ₀ ⊕ κ₁) (fromCols B A) ≠ 0) (h3 : N (κ₀ ⊕ κ₂) (fromCols B C) ≠ 0) :
    Real.log (N (κ₀ ⊕ (κ₁ ⊕ κ₂)) (fromCols B (fromCols A C))) + Real.log (N κ₀ B) ≤
      Real.log (N (κ₀ ⊕ κ₁) (fromCols B A)) + Real.log (N (κ₀ ⊕ κ₂) (fromCols B C)) := by
  have p0 := lt_of_le_of_ne (hN.nonneg _ (fromCols B (fromCols A C))) h0.symm
  have p1 := lt_of_le_of_ne (hN.nonneg _ B) h1.symm
  rw [← Real.log_mul h0 h1, ← Real.log_mul h2 h3]
  exact Real.log_le_log (mul_pos p0 p1) (hS K ι N hN _ _ _ B A C)

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ}

theorem frame_leftInv {κ : Type} [Fintype κ] [DecidableEq κ] (x : GA E n) (M : Matrix (Fin n) κ E)
    (h : LinearIndependent E Mᵀ) :
    ∃ Y : Matrix κ (Fin n) (Ad E), Y * ((x⁻¹ : GA E n).val * M.map (algebraMap E (Ad E))) = 1 := by
  obtain ⟨Y, hY⟩ := exists_leftInv M h
  refine ⟨Y.map (algebraMap E (Ad E)) * x.val, ?_⟩
  have hx : x.val * (x⁻¹ : GA E n).val = 1 := Units.mul_inv x
  have hm : Y.map (algebraMap E (Ad E)) * M.map (algebraMap E (Ad E)) = 1 := by
    rw [← Matrix.map_mul, hY, Matrix.map_one _ (map_zero _) (map_one _)]
  calc Y.map (algebraMap E (Ad E)) * x.val * ((x⁻¹ : GA E n).val * M.map (algebraMap E (Ad E)))
      = Y.map (algebraMap E (Ad E)) * (x.val * (x⁻¹ : GA E n).val) * M.map (algebraMap E (Ad E)) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hx, Matrix.mul_one, hm]

theorem frame_fromCols {κ κ' : Type} [Fintype κ] [Fintype κ'] (x : GA E n) (P : Matrix (Fin n) κ E)
    (Q : Matrix (Fin n) κ' E) :
    (x⁻¹ : GA E n).val * (fromCols P Q).map (algebraMap E (Ad E)) =
      fromCols ((x⁻¹ : GA E n).val * P.map (algebraMap E (Ad E))) ((x⁻¹ : GA E n).val * Q.map (algebraMap E (Ad E))) := by
  rw [map_fromCols, Matrix.mul_fromCols]

theorem sum_ineq (hF : WedgeF) (hI : WedgeI) (hS : WedgeSub) (hFS : FinSupp)
    {κ₀ κ₁ κ₂ : Type} [Fintype κ₀] [DecidableEq κ₀] [Fintype κ₁] [DecidableEq κ₁] [Fintype κ₂] [DecidableEq κ₂]
    (P : Matrix (Fin n) κ₀ (Ad E)) (Q : Matrix (Fin n) κ₁ (Ad E)) (R : Matrix (Fin n) κ₂ (Ad E))
    {Y₀ : Matrix (κ₀ ⊕ (κ₁ ⊕ κ₂)) (Fin n) (Ad E)} (h₀ : Y₀ * fromCols P (fromCols Q R) = 1)
    {Y₁ : Matrix κ₀ (Fin n) (Ad E)} (h₁ : Y₁ * P = 1)
    {Y₂ : Matrix (κ₀ ⊕ κ₁) (Fin n) (Ad E)} (h₂ : Y₂ * fromCols P Q = 1)
    {Y₃ : Matrix (κ₀ ⊕ κ₂) (Fin n) (Ad E)} (h₃ : Y₃ * fromCols P R = 1) :
    (∑ v, Real.log (nI ((fromCols P (fromCols Q R)).map (cV v))) +
        ∑ᶠ w, Real.log (nF ((fromCols P (fromCols Q R)).map (cW w)))) +
      (∑ v, Real.log (nI (P.map (cV v))) + ∑ᶠ w, Real.log (nF (P.map (cW w)))) ≤
    (∑ v, Real.log (nI ((fromCols P Q).map (cV v))) + ∑ᶠ w, Real.log (nF ((fromCols P Q).map (cW w)))) +
      (∑ v, Real.log (nI ((fromCols P R).map (cV v))) + ∑ᶠ w, Real.log (nF ((fromCols P R).map (cW w)))) := by
  obtain ⟨i₀, f₀, s₀⟩ := hFS E _ _ _ Y₀ h₀
  obtain ⟨i₁, f₁, s₁⟩ := hFS E _ _ _ Y₁ h₁
  obtain ⟨i₂, f₂, s₂⟩ := hFS E _ _ _ Y₂ h₂
  obtain ⟨i₃, f₃, s₃⟩ := hFS E _ _ _ Y₃ h₃
  have fin : ∀ {κ : Type} [Fintype κ] [DecidableEq κ] (T : Matrix (Fin n) κ (Ad E)),
      {w | nF (T.map (cW w)) ≠ 1}.Finite →
      (Function.support fun w => Real.log (nF (T.map (cW w)))).Finite := by
    intro κ _ _ T hT
    refine hT.subset fun w hw h1 => hw ?_
    simp only [Function.mem_support] at hw
    exact absurd (by rw [h1, Real.log_one]) hw
  have inf : ∑ v, Real.log (nI ((fromCols P (fromCols Q R)).map (cV v))) + ∑ v, Real.log (nI (P.map (cV v))) ≤
      ∑ v, Real.log (nI ((fromCols P Q).map (cV v))) + ∑ v, Real.log (nI ((fromCols P R).map (cV v))) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun v _ => ?_
    have a₀ := i₀ v
    have a₂ := i₂ v
    have a₃ := i₃ v
    rw [map_fromCols] at a₂ a₃
    rw [map_fromCols, map_fromCols] at a₀
    rw [map_fromCols, map_fromCols, map_fromCols, map_fromCols]
    exact log_ineq (fun _ _ _ A => nI A) (hI _) hS _ _ _ a₀ (i₁ v) a₂ a₃
  have finp : ∑ᶠ w, Real.log (nF ((fromCols P (fromCols Q R)).map (cW w))) + ∑ᶠ w, Real.log (nF (P.map (cW w))) ≤
      ∑ᶠ w, Real.log (nF ((fromCols P Q).map (cW w))) + ∑ᶠ w, Real.log (nF ((fromCols P R).map (cW w))) := by
    rw [← finsum_add_distrib (fin _ s₀) (fin _ s₁), ← finsum_add_distrib (fin _ s₂) (fin _ s₃)]
    refine finsum_le_finsum' ((fin _ s₀).union (fin _ s₁) |>.subset (Function.support_add _ _))
      ((fin _ s₂).union (fin _ s₃) |>.subset (Function.support_add _ _)) fun w => ?_
    have a₀ := f₀ w
    have a₂ := f₂ w
    have a₃ := f₃ w
    rw [map_fromCols] at a₂ a₃
    rw [map_fromCols, map_fromCols] at a₀
    simp only [Pi.add_apply]
    rw [map_fromCols, map_fromCols, map_fromCols, map_fromCols]
    exact log_ineq (fun _ _ _ A => nF A) (hF _ _) hS _ _ _ a₀ (f₁ w) a₂ a₃
  linarith

theorem degG_ineq (hF : WedgeF) (hI : WedgeI) (hS : WedgeSub) (hFS : FinSupp) (x : GA E n)
    {κ₀ κ₁ κ₂ : Type} [Fintype κ₀] [DecidableEq κ₀] [Fintype κ₁] [DecidableEq κ₁] [Fintype κ₂] [DecidableEq κ₂]
    (B : Matrix (Fin n) κ₀ E) (A : Matrix (Fin n) κ₁ E) (C : Matrix (Fin n) κ₂ E)
    (l₀ : LinearIndependent E (fromCols B (fromCols A C))ᵀ) (l₁ : LinearIndependent E Bᵀ)
    (l₂ : LinearIndependent E (fromCols B A)ᵀ) (l₃ : LinearIndependent E (fromCols B C)ᵀ) :
    degG x (fromCols B A) + degG x (fromCols B C) ≤ degG x B + degG x (fromCols B (fromCols A C)) := by
  obtain ⟨Y₀, h₀⟩ := frame_leftInv x _ l₀
  obtain ⟨Y₁, h₁⟩ := frame_leftInv x _ l₁
  obtain ⟨Y₂, h₂⟩ := frame_leftInv x _ l₂
  obtain ⟨Y₃, h₃⟩ := frame_leftInv x _ l₃
  rw [frame_fromCols, frame_fromCols] at h₀
  rw [frame_fromCols] at h₂ h₃
  have key := sum_ineq hF hI hS hFS _ _ _ h₀ h₁ h₂ h₃
  simp only [degG, frame_fromCols]
  linarith

theorem degSubmod_of (hF : WedgeF) (hI : WedgeI) (hS : WedgeSub) (hFS : FinSupp) (hB : DegBasisG) (hT : TwoBases) :
    DegSubmod := by
  intro E _ _ _ n x W W'
  obtain ⟨a, b, c, B, A, C, l₀, e₁, e₂, e₃, e₄⟩ := hT E n W W'
  have l₂ : LinearIndependent E (fromCols B A)ᵀ := by
    have : (fromCols B A)ᵀ = (fromCols B (fromCols A C))ᵀ ∘ Sum.map id Sum.inl := by
      funext j; rcases j with j | j <;> rfl
    rw [this]
    exact l₀.comp _ (Sum.map_injective.2 ⟨Function.injective_id, Sum.inl_injective⟩)
  have l₃ : LinearIndependent E (fromCols B C)ᵀ := by
    have : (fromCols B C)ᵀ = (fromCols B (fromCols A C))ᵀ ∘ Sum.map id Sum.inr := by
      funext j; rcases j with j | j <;> rfl
    rw [this]
    exact l₀.comp _ (Sum.map_injective.2 ⟨Function.injective_id, Sum.inr_injective⟩)
  have l₁ : LinearIndependent E Bᵀ := by
    have : Bᵀ = (fromCols B (fromCols A C))ᵀ ∘ Sum.inl := by
      funext j; rfl
    rw [this]
    exact l₀.comp _ Sum.inl_injective
  have d₀ := hB E n _ x _ l₀
  have d₁ := hB E n _ x _ l₁
  have d₂ := hB E n _ x _ l₂
  have d₃ := hB E n _ x _ l₃
  rw [e₄] at d₀
  rw [e₁] at d₁
  rw [e₂] at d₂
  rw [e₃] at d₃
  rw [← d₀, ← d₁, ← d₂, ← d₃]
  exact degG_ineq hF hI hS hFS x B A C l₀ l₁ l₂ l₃

end GlobalTheory.CompanionTheory.DegreeSubmod

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeUnderTranslation
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.DegMoveProof

theorem log_step {a b c : ℝ} {k n : ℕ} (hkn : k ≤ n) (ha : 0 < a) (hb : 0 < b) (h : a ≤ c ^ k * b) :
    Real.log a ≤ n * Real.posLog c + Real.log b := by
  have hp : 0 < c ^ k * b := lt_of_lt_of_le ha h
  have hck : c ^ k ≠ 0 := fun h0 => by simp [h0] at hp
  have h1 : Real.log a ≤ Real.log (c ^ k * b) := Real.log_le_log ha h
  rw [Real.log_mul hck hb.ne', Real.log_pow] at h1
  have h2 : Real.log c ≤ Real.posLog c := le_max_right 0 (Real.log c)
  have h3 : (0 : ℝ) ≤ Real.posLog c := Real.posLog_nonneg
  have h4 : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have h5 : (k : ℝ) * Real.log c ≤ n * Real.posLog c :=
    (mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg k)).trans (mul_le_mul_of_nonneg_right h4 h3)
  linarith

theorem finsum_bound {α : Type} {f g s : α → ℝ} {c : ℝ} (hf : (Function.support f).Finite)
    (hg : (Function.support g).Finite) (hs : (Function.support s).Finite) (h : ∀ a, f a ≤ c * s a + g a) :
    ∑ᶠ a, f a ≤ c * ∑ᶠ a, s a + ∑ᶠ a, g a := by
  classical
  let T : Finset α := hf.toFinset ∪ hg.toFinset ∪ hs.toFinset
  rw [finsum_eq_sum_of_support_subset f (s := T) (fun a ha => by simp [T, Set.mem_toFinset] at ha ⊢; tauto),
    finsum_eq_sum_of_support_subset g (s := T) (fun a ha => by simp [T, Set.mem_toFinset] at ha ⊢; tauto),
    finsum_eq_sum_of_support_subset s (s := T) (fun a ha => by simp [T, Set.mem_toFinset] at ha ⊢; tauto),
    Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun a _ => h a

theorem sz_sq_le {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : sz g ^ 2 ≤ ⨆ p : Fin n × Fin n, ‖g p.1 p.2‖ ^ 2 := by
  rcases isEmpty_or_nonempty (Fin n × Fin n) with he | hne
  · simp [sz, Real.iSup_of_isEmpty]
  · obtain ⟨p, hp⟩ := exists_eq_ciSup_of_finite (f := fun p : Fin n × Fin n => ‖g p.1 p.2‖)
    rw [sz, ← hp]
    exact le_ciSup (f := fun p : Fin n × Fin n => ‖g p.1 p.2‖ ^ 2) (Set.finite_range _).bddAbove p

theorem nI_nonneg {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ] (A : Matrix ι κ ℂ) : 0 ≤ nI A := by
  open ComplexOrder in
  have h : 0 ≤ (Aᴴ * A).det := (Matrix.posSemidef_conjTranspose_mul_self A).det_nonneg
  exact (Complex.le_def.1 h).1

theorem nF_nonneg {K ι κ : Type} [NormedField K] [Fintype κ] [DecidableEq κ] (A : Matrix ι κ K) : 0 ≤ nF A :=
  Real.iSup_nonneg fun _ => norm_nonneg _

theorem exists_left_inv {K : Type} [Field K] {n k : ℕ} (M : Matrix (Fin n) (Fin k) K)
    (h : LinearIndependent K Mᵀ) : ∃ N : Matrix (Fin k) (Fin n) K, N * M = 1 := by
  have hinj : Function.Injective M.mulVecLin := Matrix.mulVec_injective_iff.2 h
  obtain ⟨f, hf⟩ := LinearMap.exists_leftInverse_of_injective M.mulVecLin (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨LinearMap.toMatrix' f, ?_⟩
  have h1 : LinearMap.toMatrix' (f ∘ₗ M.mulVecLin) = 1 := by rw [hf]; exact LinearMap.toMatrix'_id
  rwa [LinearMap.toMatrix'_comp, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin'] at h1

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n k : ℕ}

theorem ultra (w : HeightOneSpectrum (𝓞 E)) : IsUltrametricDist (w.adicCompletion E) :=
  inferInstanceAs (@IsUltrametricDist (w.adicCompletion E)
    (Valued.toNormedField (w.adicCompletion E) (WithZero (Multiplicative ℤ))).toDist)

theorem inf_step (hI : MulI) (hkn : k ≤ n) (h : Matrix (Fin n) (Fin n) (Ad E)) (A : Matrix (Fin n) (Fin k) (Ad E))
    (v : InfinitePlace E) (h0 : nI ((h * A).map (cV v)) ≠ 0) (h1 : nI (A.map (cV v)) ≠ 0) :
    Real.log (nI ((h * A).map (cV v))) ≤
      n * (Real.posLog ((n : ℝ) * n) + Real.posLog (⨆ p : Fin n × Fin n, ‖cV v (h p.1 p.2)‖ ^ 2)) +
        Real.log (nI (A.map (cV v))) := by
  have hm : (h * A).map (cV v) = h.map (cV v) * A.map (cV v) := Matrix.map_mul
  have hle := (hI (Fin n) (Fin n) (Fin k) (A.map (cV v))).1 (h.map (cV v))
  simp only [Fintype.card_fin] at hle
  rw [← hm] at hle
  have hs := log_step hkn (lt_of_le_of_ne (nI_nonneg _) h0.symm) (lt_of_le_of_ne (nI_nonneg _) h1.symm) hle
  refine hs.trans ?_
  have h2 : Real.posLog ((n : ℝ) * n * sz (h.map (cV v)) ^ 2) ≤
      Real.posLog ((n : ℝ) * n) + Real.posLog (⨆ p : Fin n × Fin n, ‖cV v (h p.1 p.2)‖ ^ 2) :=
    Real.posLog_mul.trans (add_le_add le_rfl (Real.posLog_le_posLog (by positivity) (sz_sq_le _)))
  have := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg (α := ℝ) n)
  linarith

theorem fin_step (hF : MulF) (hkn : k ≤ n) (h : Matrix (Fin n) (Fin n) (Ad E)) (A : Matrix (Fin n) (Fin k) (Ad E))
    (w : HeightOneSpectrum (𝓞 E)) (h0 : nF ((h * A).map (cW w)) ≠ 0) (h1 : nF (A.map (cW w)) ≠ 0) :
    Real.log (nF ((h * A).map (cW w))) ≤
      n * Real.posLog (⨆ p : Fin n × Fin n, ‖cW w (h p.1 p.2)‖) + Real.log (nF (A.map (cW w))) := by
  haveI := ultra w
  have hm : (h * A).map (cW w) = h.map (cW w) * A.map (cW w) := Matrix.map_mul
  have hle := (hF (w.adicCompletion E) (Fin n) (Fin n) (Fin k) (A.map (cW w))).1 (h.map (cW w))
  simp only [Fintype.card_fin] at hle
  rw [← hm] at hle
  exact log_step hkn (lt_of_le_of_ne (nF_nonneg _) h0.symm) (lt_of_le_of_ne (nF_nonneg _) h1.symm) hle

theorem logSizeM_nonneg (A : Matrix (Fin n) (Fin n) (Ad E)) : 0 ≤ logSizeM A :=
  add_nonneg (Finset.sum_nonneg fun _ _ => Real.posLog_nonneg) (finsum_nonneg fun _ => Real.posLog_nonneg)

theorem frame_move (x : GA E n) (g : GL (Fin n) E) (M : Matrix (Fin n) (Fin k) E) :
    (x⁻¹ * ratGL E n g * x : GA E n).val * ((x⁻¹ : GA E n).val * M.map (algebraMap E (Ad E))) =
      (x⁻¹ : GA E n).val * (g.val * M).map (algebraMap E (Ad E)) := by
  have h1 : (ratGL E n g).val = g.val.map (algebraMap E (Ad E)) := rfl
  rw [Matrix.map_mul, ← h1, Units.val_mul, Units.val_mul, Matrix.mul_assoc, Matrix.mul_assoc,
    ← Matrix.mul_assoc x.val, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]

theorem core (hF : MulF) (hI : MulI) (hSz : SzFin) (hFS : FinSupp) (hkn : k ≤ n) (h : GA E n)
    (A : Matrix (Fin n) (Fin k) (Ad E)) (Y : Matrix (Fin k) (Fin n) (Ad E)) (hY : Y * A = 1) :
    ∑ v, Real.log (nI ((h.val * A).map (cV v))) + ∑ᶠ w, Real.log (nF ((h.val * A).map (cW w))) ≤
      (∑ v, Real.log (nI (A.map (cV v))) + ∑ᶠ w, Real.log (nF (A.map (cW w)))) +
        n * ((Fintype.card (InfinitePlace E) : ℝ) * Real.posLog ((n : ℝ) * n)) + n * logSizeM h.val := by
  have hY' : (Y * (h⁻¹ : GA E n).val) * (h.val * A) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (h⁻¹ : GA E n).val, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mul, hY]
  obtain ⟨a1, a2, a3⟩ := hFS E (Fin n) (Fin k) A Y hY
  obtain ⟨b1, b2, b3⟩ := hFS E (Fin n) (Fin k) (h.val * A) _ hY'
  have hinf := Finset.sum_le_sum (s := Finset.univ) fun v (_ : v ∈ Finset.univ) =>
    inf_step (E := E) hI hkn h.val A v (b1 v) (a1 v)
  have hfin := finsum_bound (c := (n : ℝ))
    (f := fun w => Real.log (nF ((h.val * A).map (cW w))))
    (g := fun w => Real.log (nF (A.map (cW w))))
    (s := fun w => Real.posLog (⨆ p : Fin n × Fin n, ‖cW w (h.val p.1 p.2)‖))
    (b3.subset fun w hw hne => hw ((congrArg Real.log hne).trans Real.log_one))
    (a3.subset fun w hw hne => hw ((congrArg Real.log hne).trans Real.log_one))
    ((hSz E (Fin n) (Fin n) h.val).subset fun w hw => by
      by_contra hc
      apply hw
      exact max_eq_left (Real.log_nonpos (Real.iSup_nonneg fun _ => norm_nonneg _) (not_lt.1 hc)))
    fun w => fin_step hF hkn h.val A w (b2 w) (a2 w)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at hinf
  have hS : logSizeM h.val = ∑ v, Real.posLog (⨆ p : Fin n × Fin n, ‖cV v (h.val p.1 p.2)‖ ^ 2) +
      ∑ᶠ w, Real.posLog (⨆ p : Fin n × Fin n, ‖cW w (h.val p.1 p.2)‖) := rfl
  rw [hS]
  nlinarith [hinf, hfin]

theorem lin_basisMat (W : Submodule E (Fin n → E)) : LinearIndependent E (basisMat W)ᵀ ∧
    Submodule.span E (Set.range (basisMat W)ᵀ) = W := by
  have hM : (basisMat W)ᵀ = W.subtype ∘ (Module.finBasis E W) := by
    funext j i
    rfl
  rw [hM]
  refine ⟨(Module.finBasis E W).linearIndependent.map' W.subtype W.ker_subtype, ?_⟩
  rw [Set.range_comp, ← Submodule.map_span, Module.Basis.span_eq, Submodule.map_top, Submodule.range_subtype]

theorem linearIndependent_image_span (g : GL (Fin n) E) (f : Fin k → Fin n → E) (hf : LinearIndependent E f) :
    LinearIndependent E (Matrix.toLin' g.val ∘ f) ∧
      Submodule.span E (Set.range (Matrix.toLin' g.val ∘ f)) = img g (Submodule.span E (Set.range f)) := by
  have inj : Function.Injective (Matrix.toLin' g.val) := fun a b hab => by
    have h1 := congrArg (fun y => (g⁻¹ : GL (Fin n) E).val *ᵥ y) hab
    simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Units.val_mul] using h1
  refine ⟨hf.map' _ (LinearMap.ker_eq_bot.2 inj), ?_⟩
  rw [Set.range_comp, ← Submodule.map_span]
  rfl

theorem lin_moved (g : GL (Fin n) E) (M : Matrix (Fin n) (Fin k) E) (hM : LinearIndependent E Mᵀ) :
    LinearIndependent E (g.val * M)ᵀ ∧
      Submodule.span E (Set.range (g.val * M)ᵀ) = img g (Submodule.span E (Set.range Mᵀ)) := by
  have hG : (Matrix.toLin' g.val ∘ (Mᵀ : Fin k → Fin n → E)) = ((g.val * M)ᵀ : Fin k → Fin n → E) := by
    funext j i
    change (Matrix.toLin' g.val (fun i' => M i' j)) i = (g.val * M) i j
    rw [Matrix.toLin'_apply]
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  have h1 := linearIndependent_image_span g Mᵀ hM
  rw [hG] at h1
  exact h1

theorem degMove_of : MulF → MulI → SzFin → FinSupp → DegBasisG → DegMove := by
  intro hF hI hSz hFS hB E _ _ _ n
  refine ⟨n * (1 + (Fintype.card (InfinitePlace E) : ℝ) * Real.posLog ((n : ℝ) * n)), fun x g W => ?_⟩
  obtain ⟨hLI, hspan⟩ := lin_basisMat W
  obtain ⟨hLI', hspan'⟩ := lin_moved g (basisMat W) hLI
  rw [hspan] at hspan'
  have hkn : Module.finrank E W ≤ n := by simpa using Submodule.finrank_le W
  obtain ⟨N, hN⟩ := exists_left_inv (basisMat W) hLI
  have e1 : deg x (img g W) = degG x (g.val * basisMat W) := by rw [hB E n _ x _ hLI', hspan']
  have e2 : deg x W = degG x (basisMat W) := rfl
  have hY : (N.map (algebraMap E (Ad E)) * x.val) * ((x⁻¹ : GA E n).val * (basisMat W).map (algebraMap E (Ad E))) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc x.val, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul,
      ← Matrix.map_mul, hN, Matrix.map_one _ (map_zero _) (map_one _)]
  have hc := core hF hI hSz hFS hkn (x⁻¹ * ratGL E n g * x) _ _ hY
  rw [frame_move] at hc
  rw [e1, e2]
  simp only [degG]
  have hS := logSizeM_nonneg (x⁻¹ * ratGL E n g * x : GA E n).val
  have hS' := logSizeM_nonneg ((x⁻¹ * ratGL E n g * x)⁻¹ : GA E n).val
  have hL : (0 : ℝ) ≤ (Fintype.card (InfinitePlace E) : ℝ) * Real.posLog ((n : ℝ) * n) :=
    mul_nonneg (Nat.cast_nonneg _) Real.posLog_nonneg
  have hsz : logSize (x⁻¹ * ratGL E n g * x) = logSizeM (x⁻¹ * ratGL E n g * x : GA E n).val +
    logSizeM ((x⁻¹ * ratGL E n g * x)⁻¹ : GA E n).val := rfl
  rw [hsz]
  generalize logSizeM (x⁻¹ * ratGL E n g * x : GA E n).val = S at *
  generalize logSizeM ((x⁻¹ * ratGL E n g * x)⁻¹ : GA E n).val = S' at *
  generalize (Fintype.card (InfinitePlace E) : ℝ) * Real.posLog ((n : ℝ) * n) = b at *
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hpos : 0 ≤ (n : ℝ) * (1 + S' + b * S + b * S') := by positivity
  nlinarith [hc, hpos]

end GlobalTheory.CompanionTheory.DegMoveProof

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPermBlockMatrix
section
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.SizeCells

theorem exists_perm_cell_sizes : ∀ {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {β' : Type} [Fintype β'] [LinearOrder β'] {m' : β' → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)] (e : (Σ i, m i) ≃ Fin N) (e' : (Σ j, m' j) ≃ Fin N) (b : SizeMatrix m m'), ∃ w : Equiv.Perm (Fin N), ∀ i j, ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card) = b.1 i j := by
  intro α _ _ N m _ _ β' _ _ m' _ _ e e' b
  obtain ⟨f⟩ := b.nonempty_rows
  obtain ⟨g⟩ := b.nonempty_cols
  let A : (Σ i, Σ j, Fin (b.1 i j)) ≃ Fin N := (Equiv.sigmaCongrRight f).trans e
  let B : (Σ j, Σ i, Fin (b.1 i j)) ≃ Fin N := (Equiv.sigmaCongrRight g).trans e'
  let S : (Σ i, Σ j, Fin (b.1 i j)) ≃ (Σ j, Σ i, Fin (b.1 i j)) :=
    { toFun := fun p => ⟨p.2.1, p.1, p.2.2⟩
      invFun := fun p => ⟨p.2.1, p.1, p.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let w : Equiv.Perm (Fin N) := (B.symm.trans S.symm).trans A
  have hA : ∀ p, blk e (A p) = p.1 := by
    intro p
    simp [A, blk]
  have hB : ∀ p, blk e' (B p) = p.1 := by
    intro p
    simp [B, blk]
  have hw : ∀ p, w.symm (A p) = B (S p) := by
    intro p
    simp [w]
  refine ⟨w, fun i j => ?_⟩
  have himg : (Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j) =
      Finset.univ.image (fun t : Fin (b.1 i j) => A ⟨i, j, t⟩) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨⟨i', j', t⟩, rfl⟩ := A.surjective x
      rw [hA] at h1
      rw [hw, hB] at h2
      dsimp only [S, Equiv.coe_fn_mk] at h1 h2
      subst h1
      subst h2
      exact ⟨t, rfl⟩
    · rintro ⟨t, rfl⟩
      refine ⟨hA _, ?_⟩
      rw [hw, hB]
      rfl
  rw [himg, Finset.card_image_of_injective _ (fun s t h => by simpa using A.injective h)]
  simp

end GlobalTheory.CompanionTheory.SizeCells
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiltrationUniqueSubquotientStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.filtration_unique_subquotient : ∀ {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (π : Representation ℂ G V) (σ : Representation ℂ G W) (N : ℕ) (S : Fin (N + 1) → Subrepresentation π), Monotone S → S 0 = ⊥ → S (Fin.last N) = ⊤ → ∀ t₀ : Fin N, (∀ φ ψ : (subQuot (S t₀.succ) (S t₀.castSucc)).IntertwiningMap σ, φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap) → (∀ t : Fin N, t ≠ t₀ → ∀ φ : (subQuot (S t.succ) (S t.castSucc)).IntertwiningMap σ, φ.toLinearMap = 0) → ∀ φ ψ : π.IntertwiningMap σ, φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap := by
  first | exact @GlobalTheory.CompanionTheory.Filtration.intertwining_proportional | exact GlobalTheory.CompanionTheory.Filtration.intertwining_proportional | (intros; apply GlobalTheory.CompanionTheory.Filtration.intertwining_proportional <;> assumption)
end

