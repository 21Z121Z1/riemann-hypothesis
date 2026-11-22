import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InductionContragredient
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0034
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParIndJacPlacing
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0037
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0160
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0004
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0131
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0159
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactTypePrime
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0155

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIrreducibleSubquotient
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.BoundaryMaps

section General

variable {G H V W U : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]

theorem exists_irreducible_subquotient [Nontrivial V] (ρ : Representation ℂ G V) :
    ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (τ : Representation ℂ G Y),
      τ.IsIrreducible ∧ IsSubquotient τ ρ := by
  let φ := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)
  haveI : Nontrivial ρ.asModule := inferInstanceAs (Nontrivial V)
  obtain ⟨v, hv⟩ := exists_ne (0 : ρ.asModule)
  have hc := CompleteLattice.Iic_coatomic_of_compact_element
    (Submodule.singleton_span_isCompactElement (R := MonoidAlgebra ℂ G) v)
  rcases hc.eq_top_or_exists_le_coatom ⊥ with h | ⟨T, hT, -⟩
  · have h1 : (⊥ : Submodule (MonoidAlgebra ℂ G) ρ.asModule) = Submodule.span _ {v} :=
      congrArg Subtype.val h
    exact absurd (Submodule.span_singleton_eq_bot.1 h1.symm) hv
  · have h1 : T.1 ⋖ Submodule.span _ {v} := (covBy_iff_coatom_Iic T.2).2 hT
    have h2 : φ.symm T.1 ⋖ φ.symm (Submodule.span _ {v}) := (apply_covBy_apply_iff φ.symm).2 h1
    exact ⟨_, _, _, _, isIrreducible_subQuot h2, _,
      ⟨Submodule.mkQ _, fun g => LinearMap.ext fun x => rfl⟩, Submodule.mkQ_surjective _⟩

def transpose [TopologicalSpace G] [IsTopologicalGroup G] {ρ : Representation ℂ G V}
    {π : Representation ℂ G W} (hπ : IsSmooth π) (f : ρ.IntertwiningMap (contra π)) :
    π.IntertwiningMap (contra ρ) :=
  have key : ∀ g w, ((smoothPart π.dual).subtype ∘ₗ f.toLinearMap).flip (π g w) =
      ρ.dual g (((smoothPart π.dual).subtype ∘ₗ f.toLinearMap).flip w) := fun g w =>
    LinearMap.ext fun v => by
      show (f v).1 (π g w) = (f (ρ g⁻¹ v)).1 w
      rw [f.isIntertwining, contra_apply, inv_inv]
  { toLinearMap := (((smoothPart π.dual).subtype ∘ₗ f.toLinearMap).flip).codRestrict _ fun w =>
      mem_smoothPart_of_nhds (Filter.mem_of_superset ((hπ w).mem_nhds (by simp)) fun g hg => by
        have hg' : π g w = w := hg
        rw [Set.mem_ofPred_eq, ← key, hg'])
    isIntertwining' := fun g => LinearMap.ext fun w => Subtype.ext (key g w) }

end General

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem exists_jac_map {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n)
    {ρ : Representation ℂ (Levi k m) W} (hρ : IsSmooth ρ) {π : Representation ℂ (GL n k) V}
    (hπ : IsSmooth π) (f : (parInd e ρ).IntertwiningMap (contra π)) (hf : f.toLinearMap ≠ 0) :
    ∃ φ : (jac e π).IntertwiningMap (contra ρ), φ.toLinearMap ≠ 0 := by
  obtain ⟨Φ⟩ := (IndDual.inductionContragredient k).nonempty_equiv e hρ
  let g := Φ.symm.toIntertwiningMap.comp (transpose hπ f)
  refine ⟨Model.evalOne e g, fun h => hf (LinearMap.ext fun x => Subtype.ext (LinearMap.ext fun v => ?_))⟩
  have h1 : g v = 0 := Subtype.ext (Subtype.ext (funext fun y => by
    have h2 : (g (π y v)).1.1 1 = 0 := LinearMap.congr_fun h (Submodule.Quotient.mk (π y v))
    rwa [g.isIntertwining, parInd_apply, one_mul] at h2))
  have h2 : transpose hπ f v = 0 := (map_eq_zero_iff Φ.symm Φ.symm.injective).1 h1
  exact LinearMap.congr_fun (congrArg Subtype.val h2) x

theorem exists_jac₂_map {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype n] [DecidableEq n] (e : a ⊕ b ≃ n) (e' : b ⊕ a ≃ n) {R : Representation ℂ (GL a k) W}
    (hR : IsSmooth R) {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) {π : Representation ℂ (GL n k) V}
    (hπ : IsSmooth π) (f : (ind₂Lower e (extTensor R (detRep b χ))).IntertwiningMap (contra π))
    (hf : f.toLinearMap ≠ 0) :
    ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (σ : Representation ℂ (Levi k (Two b a)) Y)
      (φ : (jac (two e') π).IntertwiningMap σ), φ.toLinearMap ≠ 0 ∧
        ∀ g : Levi k (Two b a), g true = 1 → ∀ y, σ g y = (detChar b χ⁻¹ (g false) : ℂ) • y := by
  obtain ⟨Φ⟩ := (SwapBlocks.lower_equiv_upper_swap k a b n e _).1 (extTensor R (detRep b χ))
  let ρ : Representation ℂ (Levi k (Two b a)) (W ⊗[ℂ] ℂ) := ((extTensor R (detRep b χ)).comp
    (MulEquiv.prodComm : GL b k × GL a k ≃* GL a k × GL b k).toMonoidHom).comp
      (leviTwo k b a).symm.toMonoidHom
  obtain ⟨Ψ⟩ := (Placing.parInd_jac_placing k _ n _ (two e') (two ((Equiv.sumComm b a).trans e)) _).1 ρ
  have hρ : IsSmooth ρ := isSmooth_comp (isSmooth_comp
    (isSmooth_extTensor hR ((isSmooth_ofChar_iff _).2 hχ.detChar)) _ continuous_swap) _
      ((continuous_apply false).prodMk (continuous_apply true))
  obtain ⟨φ, hφ⟩ := exists_jac_map (two e') hρ hπ (f.comp (Ψ.trans Φ.symm).toIntertwiningMap) fun h =>
    hf (LinearMap.ext fun x => by
      obtain ⟨y, rfl⟩ := (Ψ.trans Φ.symm).surjective x
      exact LinearMap.congr_fun h y)
  refine ⟨_, _, _, _, φ, hφ, fun g hg l => Subtype.ext (LinearMap.ext fun w => ?_)⟩
  have key : ρ g⁻¹ w = (detChar b χ⁻¹ (g false) : ℂ) • w := by
    show extTensor R (detRep b χ) ((g true)⁻¹, (g false)⁻¹) w = _
    rw [hg]
    induction w with
    | zero => simp
    | add x y hx hy => rw [map_add, hx, hy, smul_add]
    | tmul x y =>
      rw [extTensor_tmul, ← TensorProduct.tmul_smul]
      simp [detRep]
  rw [contra_apply, key, map_smul]
  rfl

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem hasCentralChar_detRep (β : ℕ) (χ : kˣ →* ℂˣ) : HasCentralChar (detRep (Fin β) χ) (χ ^ β) :=
  fun z v => by
    have : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin β) z) = z ^ β := by
      ext; simp [Matrix.GeneralLinearGroup.scalar]
    simp [detRep, this]

end Local

section Products

open Matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem piTensor_scalar {α : Type} [Fintype α] {Γ X : α → Type} [∀ a, Group (Γ a)]
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a))
    (g : ∀ a, Γ a) (c : α → ℂ) (h : ∀ a x, ρ a (g a) x = c a • x) (y : ⨂[ℂ] a, X a) :
    piTensor ρ g y = (∏ a, c a) • y := by
  induction y using PiTensorProduct.induction_on with
  | add x y hx hy => rw [map_add, hx, hy, smul_add]
  | smul_tprod r x =>
    rw [map_smul, smul_comm, piTensor_tprod, ← MultilinearMap.map_smul_univ]
    simp only [h]

theorem deltaHalf_scalar {α : Type} (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] (z : kˣ) :
    deltaHalf k m (fun a => GeneralLinearGroup.scalar (m a) z) = 1 := by
  have h1 : ∀ a, GeneralLinearGroup.det (GeneralLinearGroup.scalar (m a) z) = z ^ Fintype.card (m a) :=
    fun a => by ext; simp [GeneralLinearGroup.scalar]
  have h2 : ∑ a, modExp m a * (Fintype.card (m a) : ℤ) = 0 := by
    simp only [modExp, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, Finset.sum_filter, ite_mul,
      zero_mul]
    rw [Finset.sum_comm, sub_eq_zero]
    simp only [mul_comm]
  apply Units.ext
  rw [val_deltaHalf, modulus]
  have h3 : ∀ a, nabs k (z ^ Fintype.card (m a)) ^ modExp m a =
      nabs k z ^ (modExp m a * (Fintype.card (m a) : ℤ)) := fun a => by
    rw [mul_comm, _root_.zpow_mul, zpow_natCast]
    simp [nabs]
  simp only [h1, h3, ← Real.rpow_intCast]
  rw [← Real.rpow_sum_of_pos (nabs_pos' k z), ← Int.cast_sum, h2]
  simp

theorem multiProd_scalar {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) {X : α → Type}
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (m a) k) (X a))
    (ω : α → kˣ →* ℂˣ) (h : ∀ a, HasCentralChar (ρ a) (ω a)) (z : kˣ) (f) :
    multiProd e ρ (GeneralLinearGroup.scalar n z) f = (∏ a, (ω a z : ℂ)) • f := by
  have h1 : leviEmb k e (fun a => GeneralLinearGroup.scalar (m a) z) = GeneralLinearGroup.scalar n z := by
    ext i j
    obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
    by_cases hab : a = b
    · subst hab
      rw [leviEmb_apply_same]
      simp [GeneralLinearGroup.scalar, diagonal_apply]
    · rw [leviEmb_apply_ne k e _ hab]
      simp [GeneralLinearGroup.scalar, diagonal_apply, hab]
  refine Subtype.ext (Subtype.ext (funext fun x => ?_))
  have h2 := parInd_law e _ f ⟨_, leviEmb_mem_parab k e fun a => GeneralLinearGroup.scalar (m a) z⟩ x
  rw [leviProj_leviEmb, deltaHalf_scalar, piTensor_scalar ρ _ _ fun a => h a z] at h2
  have h3 : x * GeneralLinearGroup.scalar n z = GeneralLinearGroup.scalar n z * x := by
    ext i j
    simp [GeneralLinearGroup.scalar, mul_comm]
  show f.1.1 (x * GeneralLinearGroup.scalar n z) = (_ : ℂ) • f.1.1 x
  rw [h3, ← h1]
  simpa using h2

end Products

end GlobalTheory.BoundaryMaps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLieAlgebraExpEqOfCommuteCartanInvolution
section
open Matrix

namespace GlobalTheory.ExpCartan

open scoped Matrix.Norms.L2Operator ComplexOrder

open scoped MatrixOrder in

theorem exists_posDef_mul_self {n : ℕ} {P : Matrix (Fin n) (Fin n) ℂ} (hP : P.PosDef) :
    ∃ S : Matrix (Fin n) (Fin n) ℂ, S.PosDef ∧ S * S = P := by
  refine ⟨CFC.sqrt P, ?_, CFC.sqrt_mul_sqrt_self _ hP.posSemidef.nonneg⟩
  have hP' := hP
  rw [← isStrictlyPositive_iff_posDef] at hP' ⊢
  exact IsStrictlyPositive.sqrt _ hP'

theorem im_star_dotProduct_mulVec {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (hM : Mᴴ = M)
    (x : Fin n → ℂ) : (star x ⬝ᵥ M *ᵥ x).im = 0 := by
  have h : star (star x ⬝ᵥ M *ᵥ x) = star x ⬝ᵥ M *ᵥ x := by
    rw [← Matrix.star_dotProduct, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hM]
  exact Complex.conj_eq_iff_im.1 h

theorem exists_exp_eq_of_commute_cartan : ∀ {n : ℕ} {G C g : Matrix (Fin n) (Fin n) ℂ}, Gᴴ = G →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan Gᵀ C → gᴴ * G * g = G → Commute g C →
    ∃ Z : Matrix (Fin n) (Fin n) ℂ, Zᴴ * G + G * Z = 0 ∧ Commute Z C ∧ NormedSpace.exp Z = g := by
  intro n G C g hG hC hg hgC
  obtain ⟨hCC, hCG, hpos⟩ := hC
  have hCG' : Cᴴ * G * C = G := by
    have h := congrArg Matrix.transpose hCG
    simpa [Matrix.transpose_mul, Matrix.conjTranspose, Matrix.transpose_map, Matrix.mul_assoc] using h
  have hCG2 : Cᴴ * G = G * C := by
    calc Cᴴ * G = Cᴴ * G * (C * C) := by rw [hCC, Matrix.mul_one]
      _ = G * C := by rw [← Matrix.mul_assoc, hCG']
  set P := G * C with hPdef
  have hPh : Pᴴ = P := by rw [hPdef, Matrix.conjTranspose_mul, hG, hCG2]
  have hPpd : P.PosDef := by
    refine Matrix.posDef_iff_dotProduct_mulVec.2 ⟨hPh, fun x hx => ?_⟩
    have h1 := hpos x hx
    have he : (C *ᵥ x) ⬝ᵥ Gᵀ *ᵥ star x = star x ⬝ᵥ P *ᵥ x := by
      rw [dotProduct_comm, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec,
        hPdef, ← Matrix.mulVec_mulVec]
    rw [he] at h1
    exact Complex.lt_def.2 ⟨by simpa using h1, by simpa using (im_star_dotProduct_mulVec hPh x).symm⟩
  obtain ⟨S, hSpd, hSS⟩ := exists_posDef_mul_self hPpd
  have hSh : Sᴴ = S := hSpd.isHermitian
  have hSu : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).1 hSpd.isUnit
  set Si := S⁻¹ with hSidef
  have h1 : S * Si = 1 := Matrix.mul_nonsing_inv _ hSu
  have h2 : Si * S = 1 := Matrix.nonsing_inv_mul _ hSu
  have hSih : Siᴴ = Si := by rw [hSidef, Matrix.conjTranspose_nonsing_inv, hSh]
  have hgP : gᴴ * P * g = P := by
    calc gᴴ * P * g = gᴴ * G * (C * g) := by rw [hPdef]; simp only [Matrix.mul_assoc]
      _ = gᴴ * G * g * C := by rw [← hgC.eq]; simp only [Matrix.mul_assoc]
      _ = P := by rw [hg]
  set u := S * g * Si with hudef
  have hsu : star u = Si * gᴴ * S := by
    rw [hudef, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hSh, hSih,
      Matrix.mul_assoc]
  have huu : star u * u = 1 := by
    rw [hsu, hudef]
    calc Si * gᴴ * S * (S * g * Si) = Si * (gᴴ * (S * S) * g) * Si := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hSS, hgP, ← hSS, ← Matrix.mul_assoc, h2, Matrix.one_mul, h1]
  have hu : u ∈ unitary (Matrix (Fin n) (Fin n) ℂ) := ⟨huu, mul_eq_one_comm.1 huu⟩
  set C' := S * C * Si with hC'def
  have hSC : S * C = C' * S := by rw [hC'def, Matrix.mul_assoc _ Si, h2, Matrix.mul_one]
  have hSiC' : Si * C' = C * Si := by
    rw [hC'def, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  have huC : Commute u C' := by
    show u * C' = C' * u
    rw [hudef, hC'def]
    calc S * g * Si * (S * C * Si) = S * g * (Si * S) * C * Si := by simp only [Matrix.mul_assoc]
      _ = S * (C * g) * Si := by rw [h2, Matrix.mul_one, Matrix.mul_assoc S g C, hgC.eq]
      _ = S * C * (Si * S) * g * Si := by rw [h2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = S * C * Si * (S * g * Si) := by simp only [Matrix.mul_assoc]
  have huC' : Commute (star u) C' := by
    have hus : u * star u = 1 := mul_eq_one_comm.1 huu
    show star u * C' = C' * star u
    calc star u * C' = star u * (C' * (u * star u)) := by rw [hus, Matrix.mul_one]
      _ = star u * (u * C' * star u) := by rw [huC.eq]; simp only [Matrix.mul_assoc]
      _ = (star u * u) * C' * star u := by simp only [Matrix.mul_assoc]
      _ = C' * star u := by rw [huu, Matrix.one_mul]
  have hN : IsStarNormal u := ⟨by
    show star u * u = u * star u
    rw [huu, mul_eq_one_comm.1 huu]⟩
  have hfin : (spectrum ℂ u).Finite := Matrix.finite_spectrum u
  have hsph : ∀ z ∈ spectrum ℂ u, ‖z‖ = 1 := fun z hz => by
    simpa using spectrum.subset_circle_of_unitary hu hz
  set Y := cfc Complex.log u with hYdef
  have hlog : ContinuousOn Complex.log (spectrum ℂ u) := hfin.continuousOn _
  have hexp : NormedSpace.exp Y = u := by
    rw [hYdef, ← CFC.exp_eq_normedSpace_exp (𝕜 := ℂ), ← Complex.exp_eq_exp_ℂ,
      ← cfc_comp Complex.exp Complex.log u (hf := hlog) (ha := hN)]
    conv_rhs => rw [← cfc_id' ℂ u hN]
    refine cfc_congr fun z hz => ?_
    have hz0 : z ≠ 0 := by intro h; have := hsph z hz; rw [h] at this; simp at this
    simp [Complex.exp_log hz0]
  have hstar : star Y = -Y := by
    rw [hYdef, ← cfc_star, ← cfc_neg]
    refine cfc_congr fun z hz => ?_
    apply Complex.ext
    · simp [Complex.log_re, hsph z hz]
    · simp
  have hYC : Commute Y C' := huC.cfc huC' Complex.log
  have hYh : Yᴴ = -Y := by rw [← Matrix.star_eq_conjTranspose, hstar]
  refine ⟨Si * Y * S, ?_, ?_, ?_⟩
  · have hGP : G = S * S * C := by
      rw [hSS, hPdef, Matrix.mul_assoc, hCC, Matrix.mul_one]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hSh, hSih, hYh, hGP]
    calc S * (-Y * Si) * (S * S * C) + S * S * C * (Si * Y * S)
        = -(S * Y * (Si * S) * (S * C)) + S * ((S * C) * Si) * Y * S := by
          simp only [Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul]
      _ = -(S * (Y * C') * S) + S * (C' * Y) * S := by
          rw [h2, Matrix.mul_one, hSC, Matrix.mul_assoc C' S Si, h1, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hYC.eq, neg_add_cancel]
  · show Si * Y * S * C = C * (Si * Y * S)
    calc Si * Y * S * C = Si * (Y * C') * S := by rw [Matrix.mul_assoc _ S C, hSC]; simp only [Matrix.mul_assoc]
      _ = (Si * C') * Y * S := by rw [hYC.eq]; simp only [Matrix.mul_assoc]
      _ = C * (Si * Y * S) := by rw [hSiC']; simp only [Matrix.mul_assoc]
  · have hSun : IsUnit S := hSpd.isUnit
    rw [hSidef, Matrix.exp_conj' S Y hSun, hexp, hudef, ← hSidef]
    calc Si * (S * g * Si) * S = (Si * S) * g * (Si * S) := by simp only [Matrix.mul_assoc]
      _ = g := by rw [h2, Matrix.one_mul, Matrix.mul_one]

end GlobalTheory.ExpCartan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMaxValuationIdealSplitPlaceAndConjugateStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_max_valuation_ideal_splitPlace_and_conjugate : ∀ (D : D7) (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → (∃ a : D.host.E, a ∈ D.host.AA ∧ a ≠ 0 ∧ ∀ a' : D.host.E, a' ∈ D.host.AA → Valued.v (rdQ φ a') ≤ Valued.v (rdQ φ a)) ∧ (∃ a : D.host.E, a ∈ D.host.AA ∧ a ≠ 0 ∧ ∀ a' : D.host.E, a' ∈ D.host.AA → Valued.v (rdQ φ (star a')) ≤ Valued.v (rdQ φ (star a))) := by
  first | exact @GlobalTheory.SplitIdealMax.exists_max_both | exact GlobalTheory.SplitIdealMax.exists_max_both | (intros; apply GlobalTheory.SplitIdealMax.exists_max_both <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSchwartzArchimedeanSliceAdelicSchwartz
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.ArchSlice

theorem exists_schwartz_slice : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ], ∀ Φ ∈ schA F κ, ∃ g : SInf F κ, ∀ t : κ → mixedEmbedding.mixedSpace F,
    g t = Φ (fun i => (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t i), (0 : FiniteAdeleRing (𝓞 F) F)) : AF F)) := by
  intro F _ _ κ _ Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, -, rfl⟩ := hx
    refine ⟨g 0 • f, fun t => ?_⟩
    simp only [SchwartzMap.smul_apply, smul_eq_mul, pureA, RingEquiv.apply_symm_apply]
    rw [mul_comm]
    rfl
  | zero => exact ⟨0, fun t => rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨g₁, h₁⟩ := hx
    obtain ⟨g₂, h₂⟩ := hy
    exact ⟨g₁ + g₂, fun t => by rw [SchwartzMap.add_apply, h₁, h₂]; rfl⟩
  | smul c x _ hx =>
    obtain ⟨g₁, h₁⟩ := hx
    exact ⟨c • g₁, fun t => by rw [SchwartzMap.smul_apply, h₁]; rfl⟩

end GlobalTheory.ArchSlice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnramifiedExponentOfIwahoriFixedVector
section
open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel

namespace GlobalTheory.SmGL

theorem exists_expMult_ne_zero_of_fixed_iwahori (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (hπ : IsAdmissible π)
    (h : fixed π (iwahori k (Fin n)) ≠ ⊥) : ∃ χ : (Fin n → kˣ) →* ℂˣ, expMult π χ ≠ 0 := by
  haveI := hπ.2 _ (IwahoriOnto.isOpen_iwahori k (Fin n)) (IwahoriOnto.isCompact_iwahori k (Fin n))
  have hb := GlobalTheory.Published.BorelCasselman_holds k (Fin n) V π hπ
  haveI : FiniteDimensional ℂ (fixed (jacBU π) (torusO k (Fin n))) :=
    Module.Finite.of_surjective _ hb.2
  haveI : Nontrivial (fixed π (iwahori k (Fin n))) := Submodule.nontrivial_iff_ne_bot.2 h
  haveI : Nontrivial (fixed (jacBU π) (torusO k (Fin n))) := hb.1.nontrivial
  obtain ⟨ψ, v, hv, hψ⟩ := GlobalTheory.exists_character_eigenvector_of_commute ℂ (Fin n → kˣ) _
    (jacBUFixed π) fun a b => by rw [← map_mul, mul_comm, map_mul]
  let ι : (ofChar ψ).IntertwiningMap (jacBUFixed π) :=
    ⟨LinearMap.toSpanSingleton ℂ _ v, fun g => by
      refine LinearMap.ext_ring ?_
      simp [hψ]⟩
  exact ⟨ψ, JHMult.jhMult_ne_zero_iff.2 (IsSubquotient.of_injective ι (smul_left_injective ℂ hv))⟩

end GlobalTheory.SmGL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteGroupActsUnitarilyHilbertMultiplicityModel
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem finiteGroup_acts_unitarily_hilbertMultiplicityModel : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S), ∀ (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) J χ, ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (e : H →ₗ[ℂ] MMap M) (d : ℂ) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), (∀ x y, inner ℂ x y = d * ipM M μ 𝓕 (e x) (e y)) → Function.Injective e → (∀ x, e x ∈ Mult θ M J χ) → μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → ∀ (g0 : G0 L.Pg L.r) (u : H ≃ₗ[ℂ] H), (∀ x v, e (u x) v = actG0 V β L g0 (e x v)) → ∀ x, ‖u x‖ = ‖x‖ := by
  intro D V S θ M β L J χ H _ _ e d μ 𝓕 hin hinj hmem hμ h𝓕 g0 u hact x
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hμ

  have hchoose : ∀ (P Q : ℂ → Prop) (hP : ∃ c, P c) (hQ : ∃ c, Q c), P = Q → hP.choose = hQ.choose := by
    rintro P Q hP hQ rfl; rfl
  have hip : ipM M μ 𝓕 (e (u x)) (e (u x)) = ipM M μ 𝓕 (e x) (e x) := by
    by_cases hk : ∃ κ, IsLevelLift V β L g0 κ
    · obtain ⟨hcpt, hlift⟩ := GlobalTheory.T.isCompact_parahoricLevel_and_contains_lifts V β L
      have hκ : hk.choose ∈ levG V β (flagL L) := hlift g0 _ hk.choose_spec
      have hκi : hk.choose⁻¹ ∈ levG V β (flagL L) := inv_mem hκ
      set a : ℂ := (levChi V β (flagL L) hk.choose)⁻¹ with ha_def
      have ha : ‖a‖ = 1 := by rw [ha_def, norm_inv, GlobalTheory.norm_levChi_flagL_eq_one V β L _ hκ, inv_one]
      have ha0 : a ≠ 0 := by intro h; rw [h, norm_zero] at ha; exact zero_ne_one ha
      have hai : ‖a⁻¹‖ = 1 := by rw [norm_inv, ha, inv_one]
      have hU : ∀ v g, e (u x) v g = a * e x v (g * hk.choose) := by
        intro v g
        rw [hact x v]
        simp only [actG0, dif_pos hk, ha_def]
      have hV : ∀ v g, e x v g = a⁻¹ * e (u x) v (g * hk.choose⁻¹) := by
        intro v g
        rw [hU, mul_assoc g, inv_mul_cancel, mul_one, ← mul_assoc, inv_mul_cancel₀ ha0, one_mul]
      have hm1 := GlobalTheory.haar_map_mul_right_of_mem_compact_subgroup μ _ hcpt _ hκ
      have hm2 := GlobalTheory.haar_map_mul_right_of_mem_compact_subgroup μ _ hcpt _ hκi
      have hiff : ∀ c, IsMultIP M μ 𝓕 (e (u x)) (e (u x)) c ↔ IsMultIP M μ 𝓕 (e x) (e x) c := by
        intro c
        constructor
        · intro hc
          exact GlobalTheory.T.multiplicityInnerProduct_unit_twisted_right_translation θ M J χ μ 𝓕 hμ h𝓕 _ _ hai hm2 _ (hmem (u x)) _ (hmem (u x)) _ _ hV hV c hc
        · intro hc
          exact GlobalTheory.T.multiplicityInnerProduct_unit_twisted_right_translation θ M J χ μ 𝓕 hμ h𝓕 _ _ ha hm1 _ (hmem x) _ (hmem x) _ _ hU hU c hc
      unfold ipM
      split_ifs with h1 h2 h2
      · exact hchoose _ _ h1 h2 (funext fun c => propext (hiff c))
      · exact absurd (let ⟨c, hc⟩ := h1; ⟨c, (hiff c).1 hc⟩) h2
      · exact absurd (let ⟨c, hc⟩ := h2; ⟨c, (hiff c).2 hc⟩) h1
      · rfl
    ·
      have h0 : e (u x) = 0 := by
        ext v g
        rw [hact x v]
        simp only [actG0, dif_neg hk]
        rfl
      have hux : u x = 0 := hinj (by rw [h0, map_zero])
      have hx : x = 0 := by
        have := congrArg u.symm hux
        simpa using this
      rw [hux, hx]
  have hsq' : ‖u x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ), hin, hin, hip]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsq'

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteGroupLiftsToParahoricLevelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_group_lifts_to_parahoric_level : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (Λ : Submodule (NumberField.RingOfIntegers D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsBaseFrame V β Λ N → L.Q = ∅ → (∀ PP ∈ L.Pg, ∀ PP' ∈ L.Pg, ¬ IsConjPl PP PP') → LiftsExist V β L := by
  first | exact @GlobalTheory.FiniteGroupLifts.liftsExist_of_twist_empty | exact GlobalTheory.FiniteGroupLifts.liftsExist_of_twist_empty | (intros; apply GlobalTheory.FiniteGroupLifts.liftsExist_of_twist_empty <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinrankEqCardMulAndTraceEqZeroOfFreeValuesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_eq_card_mul_and_trace_eq_zero_of_free_values_alt : ∀ (Y X B W : Type) [Finite X] [AddCommGroup B] [Module ℂ B] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (cls : Y → X) (ev : Y → (B →ₗ[ℂ] W)) (S : Submodule ℂ B), Function.Surjective cls → (∀ T : B, (∀ h, ev h T = 0) → T = 0) → (∀ h h', cls h = cls h' → ∃ φ : Module.End ℂ W, ∀ T ∈ S, ev h' T = φ (ev h T)) → (∀ h (ℓ : W), ∃ T ∈ S, ev h T = ℓ ∧ ∀ h', cls h' ≠ cls h → ev h' T = 0) → FiniteDimensional ℂ S ∧ Module.finrank ℂ S = Nat.card X * Module.finrank ℂ W ∧ ∀ (H : Type) [AddCommGroup H] [Module ℂ H] (e : H →ₗ[ℂ] B), Function.Injective e → LinearMap.range e = S → ∀ (A : Module.End ℂ H) (t : Y → Y), (∀ x h, ev h (e (A x)) = ev (t h) (e x)) → (∀ h, cls (t h) ≠ cls h) → LinearMap.trace ℂ H A = 0 := by
  first | exact @GlobalTheory.finrank_eq_card_mul_and_trace_eq_zero_of_free_values | exact GlobalTheory.finrank_eq_card_mul_and_trace_eq_zero_of_free_values | (intros; apply GlobalTheory.finrank_eq_card_mul_and_trace_eq_zero_of_free_values <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameMatrixMovedHomIntegralReductionsStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameMatrix_movedHom_integral_reductions : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (g : GA D S) (h : GA D T), finE S g ∈ St βS → finE T h ∈ St βT → ∀ x : WO S T, (IsIntM (frMapO S T βS βT (actO S T g⁻¹ h⁻¹ x)) ↔ IsIntM (frMapO S T βS βT x)) ∧ (IsIntM (frMapO S T βS βT x) → ∀ PP : Pl D.host.E, redM PP (frMapO S T βS βT (actO S T g⁻¹ h⁻¹ x)) = ((redFn βT PP (finE T h))⁻¹).val * redM PP (frMapO S T βS βT x) * (redFn βS PP (finE S g)).val) := by
  first | exact @GlobalTheory.FrameRed.frMapO_actO_int_red | exact GlobalTheory.FrameRed.frMapO_actO_int_red | (intros; apply GlobalTheory.FrameRed.frMapO_actO_int_red <;> assumption)
end

