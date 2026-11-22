import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1088
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToVInjective
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0031
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothVectorAutomorphicDerivatives
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1089
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SameBlockIffIsLeft
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem eab_mul_eab {p q : ℕ} (a b c d : Ix p q) :
    Eab a b * Eab c d = if b = c then Eab a d else 0 := by
  unfold Eab
  split_ifs with h
  · subst h; rw [Matrix.single_mul_single_same, mul_one]
  · exact Matrix.single_mul_single_of_ne _ _ _ _ h _

theorem mat_eq_sum_eab {p q : ℕ} (X : Mat p q) : X = ∑ a, ∑ b, X a b • Eab a b := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  unfold Eab; rw [Matrix.smul_single, smul_eq_mul, mul_one]

theorem act_eq_sum_units {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (X : Mat p q) (v : V) :
    act X v = ∑ a, ∑ b, X a b • units act a b v := by
  conv_lhs => rw [mat_eq_sum_eab X]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, units]

theorem sameBlock_iff_isLeft {p q : ℕ} (a b : Ix p q) : sameBlock a b ↔ a.isLeft = b.isLeft := by
  cases a <;> cases b <;> simp [sameBlock]

theorem lie_units_stab : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V),
    (IsLieAct act → IsGl (units act)) ∧
    (∀ N : Submodule ℂ V, (∀ a b : Ix p q, a.isLeft = b.isLeft → ∀ u ∈ N, units act a b u ∈ N) ↔ KStable act N) ∧
    ∀ N : Submodule ℂ V, (∀ a b, ∀ u ∈ N, units act a b u ∈ N) → Stab act N := by
  intro p q V _ _ act
  refine ⟨fun hL a b c d => ?_, fun N => ⟨fun h X hX w hw => ?_, fun h a b hab u hu => ?_⟩, fun N h Z y hy => ?_⟩
  · simp only [units]
    rw [← hL, eab_mul_eab, eab_mul_eab, map_sub]
    congr 1
    · split_ifs <;> simp
    · split_ifs <;> simp
  · rw [act_eq_sum_units]
    refine N.sum_mem fun a _ => N.sum_mem fun b _ => ?_
    by_cases hab : a.isLeft = b.isLeft
    · exact N.smul_mem _ (h a b hab w hw)
    · rw [hX a b (fun hs => hab ((sameBlock_iff_isLeft a b).1 hs)), zero_smul]; exact N.zero_mem
  · refine h (Eab a b) (fun c d hcd => ?_) u hu
    unfold Eab
    rw [Matrix.single_apply]
    split_ifs with h'
    · obtain ⟨rfl, rfl⟩ := h'; exact absurd ((sameBlock_iff_isLeft _ _).2 hab) hcd
    · rfl
  · rw [act_eq_sum_units]
    exact N.sum_mem fun a _ => N.sum_mem fun b _ => N.smul_mem _ (h a b y hy)

end GlobalTheory.HoweR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SameDivisorTrans
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.LogPair

private theorem resG_resG_sameDiv {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (a : Γ(X, U)) :
    resG X h₂ (resG X h₁ a) = resG X (h₂.trans h₁) a := by
  simp only [resG, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem SameDiv.trans_of_isLB : ∀ (X : Scheme.{0}) (L M N : LB X) (σ : L.Sec) (τ : M.Sec) (υ : N.Sec),
    M.IsLB → SameDiv σ τ → SameDiv τ υ → SameDiv σ υ := by
  intro X L M N σ τ υ _ h₁ h₂ x
  obtain ⟨U₁, i, j, hi, hj, u₁, hx₁, e₁⟩ := h₁ x
  obtain ⟨U₂, j', k, hj', hk, u₂, hx₂, e₂⟩ := h₂ x
  have hV : U₁ ⊓ U₂ ≤ M.U j ⊓ M.U j' := le_inf (inf_le_left.trans hj) (inf_le_right.trans hj')
  have c := congrArg (resG X hV) (τ.compat j j')
  have e₁' := congrArg (resG X (inf_le_left : U₁ ⊓ U₂ ≤ U₁)) e₁
  have e₂' := congrArg (resG X (inf_le_right : U₁ ⊓ U₂ ≤ U₂)) e₂
  change resG X hV (resG X inf_le_left (τ.f j)) =
    resG X hV ((M.g j j' : Γ(X, M.U j ⊓ M.U j')) * resG X inf_le_right (τ.f j')) at c
  simp only [map_mul, resG_resG_sameDiv] at c e₁' e₂'
  refine ⟨U₁ ⊓ U₂, i, k, inf_le_left.trans hi, inf_le_right.trans hk,
    res inf_le_left u₁ * res hV (M.g j j') * res inf_le_right u₂, ⟨hx₁, hx₂⟩, ?_⟩
  simp only [Units.val_mul, res, Units.coe_map, MonoidHom.coe_coe]
  rw [e₁', c, e₂']
  simp only [resG, mul_assoc]

end GlobalTheory.LogPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchubertCellPointImmersion
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FlagZ GlobalTheory.FlagPoly Formalism.DegreeFormula
open GlobalTheory.ProjSpace

namespace GlobalTheory.FlagZ

theorem isImmersion_of_X_mem_range {σ : Type} {Y : Scheme.{0}} (f : Sp (MvPolynomial σ ℤ) ⟶ Y) (U : Y.Opens)
    (h : ⊤ ≤ f ⁻¹ᵁ U) (hX : ∀ s, fnOn ⊤ (MvPolynomial.X s) ∈ (f.appLE U ⊤ h).hom.range) : IsImmersion f := by
  choose t ht using hX
  let ψ : CommRingCat.of (MvPolynomial σ ℤ) ⟶ Γ(Y, U) :=
    CommRingCat.ofHom (MvPolynomial.eval₂Hom (Int.castRingHom _) t)
  have e : ψ ≫ f.appLE U ⊤ h = CommRingCat.ofHom (fnOn ⊤) := by
    ext1
    refine MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun s => ?_
    rw [CommRingCat.hom_ofHom, ← ht s]
    simp [ψ]
  have i₁ : IsIso (CommRingCat.ofHom (fnOn (A := MvPolynomial σ ℤ) ⊤)) :=
    (ConcreteCategory.isIso_iff_bijective _).2 fnOn_top_bijective
  have i₂ : IsIso (⊤ : (Sp (MvPolynomial σ ℤ)).Opens).toSpecΓ :=
    (isAffineOpen_top _).isoSpec.isIso_hom
  have i₃ : IsImmersion (f.resLE U ⊤ h ≫ U.toSpecΓ ≫ Spec.map ψ) := by
    rw [← Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc, ← Spec.map_comp, e]
    infer_instance
  have i₄ : IsImmersion (f.resLE U ⊤ h) := IsImmersion.of_comp _ (U.toSpecΓ ≫ Spec.map ψ)
  have e₂ : f = (Sp (MvPolynomial σ ℤ)).topIso.inv ≫ f.resLE U ⊤ h ≫ U.ι := by
    rw [Scheme.Hom.resLE_comp_ι, ← Scheme.topIso_hom, Iso.inv_hom_id_assoc]
  rw [e₂]
  infer_instance

variable {N : ℕ} {A : Type} [CommRing A]

theorem exists_det_eq_sign_mul_minor (g : Matrix (Fin N) (Fin N) A) (l : Fin (N + 1)) (e : Fin l → Fin N)
    (he : Function.Injective e) :
    ∃ (I : Rows N l) (ε : ℤˣ), (g.submatrix e (Fin.castLE l.is_le)).det = ((ε : ℤ) : A) * minor g l I := by
  let I : Rows N l := ⟨Finset.univ.map ⟨e, he⟩, by simp [Set.powersetCard.mem_iff]⟩
  have hr : Set.range e = Set.range (subsetEnum I) := by
    rw [range_subsetEnum]
    simp [I]
  let p : Equiv.Perm (Fin l) := (Equiv.ofInjective e he).trans
    ((Equiv.setCongr hr).trans (Equiv.ofInjective _ (subsetEnum_injective I)).symm)
  have hp : subsetEnum I ∘ p = e := funext fun x => Equiv.apply_ofInjective_symm (subsetEnum_injective I) _
  refine ⟨I, Equiv.Perm.sign p, ?_⟩
  rw [minor, ← det_permute, submatrix_submatrix, hp]
  rfl

theorem det_updateRow_of_col_eq {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n A) (hM : M.det = 1) (j : n)
    (hj : ∀ c, M c j = (1 : Matrix n n A) c j) (r : n → A) : (M.updateRow j r).det = r j := by
  have h := congrFun (mulVec_cramer Mᵀ r) j
  rw [det_transpose, hM, one_smul] at h
  rw [← h, ← cramer_transpose_apply]
  simp [mulVec, dotProduct, hj, one_apply]

variable {ι κ : Type} (a : κ → ι) (l : κ → Fin (N + 1))

theorem det_lowMat_lead (τ : ι) (m : Fin (N + 1)) :
    ((lowMat a l τ).submatrix (Fin.castLE m.is_le) (Fin.castLE m.is_le)).det = 1 := by
  have h {i j : Fin N} (hij : i ≤ j) : lowMat a l τ i j = (1 : Matrix _ _ _) i j :=
    dif_neg fun ⟨_, _, h₁, h₂⟩ => (h₁.trans_le h₂).not_ge hij
  have ht : ((lowMat a l τ).submatrix (Fin.castLE m.is_le) (Fin.castLE m.is_le)).BlockTriangular
      OrderDual.toDual := fun i j hij =>
    (h (le_of_lt (show i < j from hij))).trans
      (one_apply_ne ((Fin.castLE_injective _).ne (ne_of_lt (show i < j from hij))))
  rw [det_of_isLowerTriangular _ ht]
  simp [h le_rfl]

theorem exists_det_lowMat_eq (w : ι → Equiv.Perm (Fin N)) (τ : ι) (m : Fin (N + 1)) (e : Fin m → Fin N)
    (he : Function.Injective e) : ∃ (c : Fin (plDim N m + 1)) (ε : ℤˣ),
      ((lowMat a l τ).submatrix e (Fin.castLE m.is_le)).det =
        ((ε : ℤ) : CellRing a l) * plVec (cellGL a l w τ).1 m c := by
  obtain ⟨I, ε, h⟩ := exists_det_eq_sign_mul_minor (cellGL a l w τ).1 m ((w τ).symm ∘ e)
    ((w τ).symm.injective.comp he)
  refine ⟨rowsEquiv N m I, ε, ?_⟩
  rw [plVec_rowsEquiv, ← h]
  congr 1
  refine Matrix.ext fun i j => ?_
  change _ = lowMat a l τ (w τ ((w τ).symm (e i))) _
  rw [Equiv.apply_symm_apply]
  rfl

theorem exists_X_eq_plVec [Finite κ] (w : ι → Equiv.Perm (Fin N)) (x : CellVar a l) :
    ∃ (k : κ) (c : Fin (plDim N (l k) + 1)) (ε : ℤˣ),
      MvPolynomial.X x = ((ε : ℤ) : CellRing a l) * plVec (cellGL a l w (a k)).1 (l k) c := by
  obtain ⟨⟨τ, i, j⟩, k₀, hk₀, h₁, h₂⟩ := x
  obtain ⟨k, ⟨rfl, hj⟩, hmin⟩ := Set.exists_min_image {k | a k = τ ∧ (j : ℕ) < l k} (fun k => (l k : ℕ))
    (Set.toFinite _) ⟨k₀, hk₀, h₁⟩
  have hi : (l k : ℕ) ≤ i := (hmin k₀ ⟨hk₀, h₁⟩).trans h₂
  have hinj : Function.Injective (Function.update (Fin.castLE (l k).is_le) ⟨j, hj⟩ i) := by
    intro s t hst
    by_cases hs : s = ⟨j, hj⟩ <;> by_cases ht : t = ⟨j, hj⟩
    · rw [hs, ht]
    · rw [hs, Function.update_self, Function.update_of_ne ht] at hst
      exact absurd (hi.trans_eq (congrArg Fin.val hst)) t.2.not_ge
    · rw [ht, Function.update_self, Function.update_of_ne hs] at hst
      exact absurd (hi.trans_eq (congrArg Fin.val hst.symm)) s.2.not_ge
    · rw [Function.update_of_ne hs, Function.update_of_ne ht] at hst
      exact Fin.castLE_injective _ hst
  obtain ⟨c, ε, h⟩ := exists_det_lowMat_eq a l w (a k) (l k) _ hinj
  refine ⟨k, c, ε, Eq.trans ?_ h⟩
  have hd := det_updateRow_of_col_eq _ (det_lowMat_lead a l (a k) (l k)) ⟨j, hj⟩ (fun c => by
    refine (dif_neg fun ⟨k', hk', h₃, h₄⟩ => ((hmin k' ⟨hk', h₃⟩).trans h₄).not_gt c.2).trans ?_
    simp only [one_apply, (Fin.castLE_injective _).eq_iff]) fun c => lowMat a l (a k) i (Fin.castLE (l k).is_le c)
  refine Eq.trans (Eq.trans ?_ hd.symm) ?_
  · change _ = lowMat a l (a k) i j
    rw [lowMat, of_apply, dif_pos ⟨k₀, hk₀, h₁, h₂⟩]
  · congr 1
    refine Matrix.ext fun s t => ?_
    by_cases hs : s = ⟨j, hj⟩
    · simp [hs]
    · simp [updateRow_ne hs, Function.update_of_ne hs]

theorem isImmersion_plPt_cellGL : ∀ (ι κ : Type) [Fintype ι] [Finite κ] (N : ℕ) (a : κ → ι) (l : κ → Fin (N + 1))
    (w : ι → Equiv.Perm (Fin N)), IsImmersion (plPt a l (cellGL a l w)) := by
  intro ι κ _ _ N a l w
  choose b η hb using fun k => exists_det_lowMat_eq a l w (a k) (l k) _ (Fin.castLE_injective (l k).is_le)
  simp only [det_lowMat_lead] at hb
  let U : (Amb l).Opens := ⟨⋂ k, (Pi.π (fun k => PSpace ℤ (plDim N (l k))) k ⁻¹ᵁ chart ℤ _ (b k)).1,
    isOpen_iInter_of_finite fun k => (Pi.π (fun k => PSpace ℤ (plDim N (l k))) k ⁻¹ᵁ chart ℤ _ (b k)).2⟩
  have hU (k) : U ≤ Pi.π (fun k => PSpace ℤ (plDim N (l k))) k ⁻¹ᵁ chart ℤ _ (b k) :=
    fun y hy => Set.mem_iInter.1 hy k
  have hu (k) : IsUnit (plVec (cellGL a l w (a k)).1 (l k) (b k)) := IsUnit.of_mul_eq_one_right _ (hb k).symm
  have h₀ (k) : ⊤ ≤ (plPt a l (cellGL a l w) ≫ Pi.π _ k) ⁻¹ᵁ chart ℤ _ (b k) := by
    rw [plPt_π, pt_preimage_chart]
    exact fun y _ => mem_spOpen.2 fun hy => y.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hy (hu k))
  have h : ⊤ ≤ plPt a l (cellGL a l w) ⁻¹ᵁ U := fun y hy => Set.mem_iInter.2 fun k => h₀ k hy
  refine isImmersion_of_X_mem_range _ U h fun x => ?_
  obtain ⟨k, c, ε, hx⟩ := exists_X_eq_plVec a l w x
  have e₁ := pullRatio_pt_top_mul (Int.castRingHom _) _ (span_plVec (cellGL a l w (a k)) (l k)) (b k) c (hu k)
    (plPt_π a l (cellGL a l w) k ▸ h₀ k)
  rw [← pullRatio_of_eq (plPt_π a l (cellGL a l w) k) (h₀ k), ← appLE_pullRatio (hi := hU k) _ h] at e₁
  have e₂ : plVec (cellGL a l w (a k)).1 (l k) (b k) = ((η k : ℤ) : CellRing a l) := by
    have := congrArg (((η k : ℤ) : CellRing a l) * ·) (hb k)
    simp only [mul_one, ← mul_assoc, ← Int.cast_mul, Int.units_coe_mul_self, Int.cast_one, one_mul] at this
    exact this.symm
  rw [hx, map_mul, ← e₁, e₂, map_intCast, map_intCast]
  exact mul_mem (intCast_mem _ _) (mul_mem ⟨_, rfl⟩ (intCast_mem _ _))

end GlobalTheory.FlagZ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualHermitianLatticeExistsNonzeroPairing
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

namespace GlobalTheory

theorem sesquilinearFormOfGram_eq_conj_swap : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    (∀ e, σ (σ e) = e) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (x w : Fin n → E),
    (∀ i j, σ (J j i) = J i j) → form σ J x w = σ (form σ J w x) := by
  intro F E _ _ _ _ _ σ hσ n J x w hJ
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hJ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem not_fg_top_ringOfIntegers (E : Type) [Field E] [NumberField E] :
    ¬ (⊤ : Submodule (𝓞 E) E).FG := by
  intro h
  haveI : Module.Finite (𝓞 E) E := ⟨h⟩
  haveI : Module.Finite ℤ E := Module.Finite.trans (𝓞 E) E
  have hi : IsIntegral ℤ (algebraMap ℚ E (2⁻¹ : ℚ)) := Algebra.IsIntegral.isIntegral _
  rw [isIntegral_algebraMap_iff (algebraMap ℚ E).injective] at hi
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hi
  have h2 : ((2 * y : ℤ) : ℚ) = 1 := by
    push_cast
    rw [show (algebraMap ℤ ℚ y) = (y : ℚ) from rfl] at hy
    rw [hy]; norm_num
  have : 2 * y = 1 := by exact_mod_cast h2
  omega

theorem selfDual_pair_nondeg : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    (∀ e, σ (σ e) = e) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)), L.FG →
    (∀ i j, σ (J j i) = J i j) → (∀ y, y ∈ L ↔ ∀ x ∈ L, IsIntegral ℤ (form σ J y x)) →
    ∀ x : Fin n → E, x ≠ 0 → ∃ z ∈ L, form σ J z x ≠ 0 := by
  intro F E _ _ _ _ _ σ hσ n J L hL hJ hdual x hx
  by_contra hcon
  push_neg at hcon
  have hxw : ∀ w ∈ L, form σ J x w = 0 := fun w hw => by
    rw [sesquilinearFormOfGram_eq_conj_swap F E σ hσ n J x w hJ, hcon w hw, map_zero]
  have hmem : ∀ c : E, c • x ∈ L := fun c => by
    rw [hdual]
    intro w hw
    have : form σ J (c • x) w = c * form σ J x w := by
      simp [form, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
    rw [this, hxw w hw, mul_zero]
    exact isIntegral_zero
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h; push_neg at h; exact hx (funext h)
  let f : (Fin n → E) →ₗ[𝓞 E] E := (LinearMap.proj i : (Fin n → E) →ₗ[E] E).restrictScalars (𝓞 E)
  have htop : L.map f = ⊤ := by
    rw [eq_top_iff]
    intro e _
    refine ⟨(e / x i) • x, hmem _, ?_⟩
    simp [f, div_mul_cancel₀ _ hi]
  exact not_fg_top_ringOfIntegers E (htop ▸ hL.map f)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeminormBallFamilyPowLeEncardOfLinearIndependent
section
open Filter Topology
open GlobalTheory GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem isBallFam_pow_le_encard :
    ∀ (G : Type) [AddCommGroup G] (Λ : AddSubgroup G) (B : ℝ → Set G), IsBallFam Λ B → ∀ (r Q : ℕ) (R : ℝ)
      (v : Fin r → G), 0 ≤ R → LinearIndependent ℤ v → (∀ j, v j ∈ B R) →
      ((Q ^ r : ℕ) : ℕ∞) ≤ (B (r * Q * R)).encard := by
  classical
  intro G _ Λ B hB r Q R v hR hv hvB
  obtain ⟨hmono, -, hadd⟩ := isBallFam_mono_neg_add G Λ B hB
  let f : (Fin r → Fin Q) → G := fun c => ∑ j, ((c j : ℕ) • v j)

  have hterm : ∀ (n : ℕ) (j : Fin r), n • v j ∈ B (n * R) := by
    intro n j
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simpa using hB.zero_mem 0 le_rfl
    · exact (hB.nsmul_iff n R (v j) hn (hB.subset R (hvB j))).2 (hvB j)
  have hsum : ∀ (c : Fin r → Fin Q) (s : Finset (Fin r)),
      ∑ j ∈ s, ((c j : ℕ) • v j) ∈ B (∑ j ∈ s, ((c j : ℕ) : ℝ) * R) := by
    intro c s
    induction s using Finset.induction_on with
    | empty => simpa using hB.zero_mem 0 le_rfl
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact hadd _ _ _ _ (hterm _ a) ih
  have hmem : ∀ c, f c ∈ B (r * Q * R) := by
    intro c
    refine hmono _ _ ?_ (hsum c Finset.univ)
    rw [← Finset.sum_mul]
    apply mul_le_mul_of_nonneg_right _ hR
    calc (∑ j, ((c j : ℕ) : ℝ)) ≤ ∑ _j : Fin r, (Q : ℝ) :=
          Finset.sum_le_sum fun j _ => by exact_mod_cast (c j).isLt.le
      _ = r * Q := by simp
  have hinj : Function.Injective f := by
    intro c c' h
    have h0 : ∑ j, (((c j : ℕ) : ℤ) - ((c' j : ℕ) : ℤ)) • v j = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, natCast_zsmul]
      exact sub_eq_zero.mpr h
    have := Fintype.linearIndependent_iff.1 hv _ h0
    funext j
    have hj := this j
    exact Fin.ext (by omega)
  have hsub : ((Finset.univ.image f : Finset G) : Set G) ⊆ B (r * Q * R) := by
    intro x hx
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx
    obtain ⟨c, rfl⟩ := hx
    exact hmem c
  calc ((Q ^ r : ℕ) : ℕ∞) = ((Finset.univ.image f).card : ℕ∞) := by
        rw [Finset.card_image_of_injective _ hinj]; simp
    _ = ((Finset.univ.image f : Finset G) : Set G).encard := (Set.encard_coe_eq_coe_finsetCard _).symm
    _ ≤ (B (r * Q * R)).encard := Set.encard_le_encard hsub

end GlobalTheory.VolBr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemipositiveOfIsometric
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts

namespace GlobalTheory

namespace HermLB

theorem Isometric.semiPos : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}
    (L M : GlobalTheory.HermLB p) (D : ℕ), L.Isometric M → L.SemiPos D → M.SemiPos D := by
  intro k _ X p L M D h hL σ a c y hy ξ
  have hb := mem_pick (L.φ σ).isLB y
  have hL' := hL σ _ c y ⟨hy.1, hb⟩ ξ
  have e := h.hess_eq c hy.1 hy.2 hb
  have hM : ReciprocityTheory.L2DbarEstimates.leviV D (fun v => ((M.φ σ).φ a (c.e.symm v) : ℂ)) (c.e y) ξ =
      ∑ j, ∑ l, c.hess (M.φ σ) a y j l * ξ j * (starRingEnd ℂ) (ξ l) := rfl
  have hL₂ : ReciprocityTheory.L2DbarEstimates.leviV D (fun v => ((L.φ σ).φ (pick (L.φ σ).isLB y) (c.e.symm v) : ℂ))
      (c.e y) ξ = ∑ j, ∑ l, c.hess (L.φ σ) (pick (L.φ σ).isLB y) y j l * ξ j * (starRingEnd ℂ) (ξ l) := rfl
  rw [hM, e, ← hL₂]
  exact hL'

end HermLB

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeparableFormGroupElementFixesUniquePositiveLineStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.separable_formGroup_element_fixes_unique_positive_line : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F), sigPosH (G.gram_herm v) = 1 → ∀ (β : G.Cˣ), sh G β = β → (∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) → ∀ y₀ : grp G β, (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n → (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable → ∀ z z' : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re → 0 < (star z' ⬝ᵥ (herm G v β *ᵥ z')).re → FixL G v β y₀ z → FixL G v β y₀ z' → ∃ c : ℂ, z' = c • z := by
  first | (exact @GlobalTheory.LKCx.fixL_pos_unique_of_sep) | (exact GlobalTheory.LKCx.fixL_pos_unique_of_sep) | (intros; apply GlobalTheory.LKCx.fixL_pos_unique_of_sep  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactVectorBundlesRankAdd
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (toMod)
open GlobalTheory.VB
open GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps
open GlobalTheory
open GlobalTheory.Twist (resM resM_resM app_resM)
open GlobalTheory.QCoh (appLinear appLinear_apply)

namespace GlobalTheory.VBExt

theorem bijective_add_section {X : Scheme.{0}} (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (V : X.Opens) (σ : Γ(S.X₃, V) →ₗ[Γ(X, V)] Γ(S.X₂, V)) (hσ : ∀ t, S.g.app V (σ t) = t) :
    Function.Bijective ((appLinear S.f V).coprod σ) := by
  have := hS.mono_f
  have hex (t : Γ(S.X₂, V)) (ht : S.g.app V t = 0) : ∃ u, S.f.app V u = t :=
    (QCoh.exact_app_of_exact_of_mono hS.exact V t).1 ht
  have hz (u : Γ(S.X₁, V)) : S.g.app V (S.f.app V u) = 0 :=
    (QCoh.exact_app_of_exact_of_mono hS.exact V _).2 ⟨u, rfl⟩
  have hinj : Function.Injective (appLinear S.f V) := QCoh.injective_app_of_mono S.f V
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨u, t⟩ h
    rw [LinearMap.coprod_apply, appLinear_apply] at h
    have h3 : t = 0 := by
      have := congrArg (S.g.app V) h
      rwa [map_add, hz, hσ, zero_add, map_zero] at this
    subst h3
    rw [map_zero, add_zero] at h
    have hu : u = 0 := hinj (by rw [map_zero, appLinear_apply]; exact h)
    rw [hu]; rfl
  · intro t
    obtain ⟨u, hu⟩ := hex (t - σ (S.g.app V t)) (by rw [map_sub, hσ, sub_self])
    exact ⟨(u, S.g.app V t), by rw [LinearMap.coprod_apply, appLinear_apply, hu, sub_add_cancel]⟩

theorem isVB_X₂_of_shortExact : ∀ (X : Scheme.{0}) (S : ShortComplex X.Modules) (r s : ℕ),
    S.ShortExact → IsVB S.X₁ r → IsVB S.X₃ s → IsVB S.X₂ (r + s) := by
  intro X S r s hS h₁ h₃
  have := hS.epi_g
  refine isVB_of_frames (ι := Fin r ⊕ Fin s) (by simp) fun x => ?_
  obtain ⟨U₁, e₁, hxU₁, he₁⟩ := h₁ x
  obtain ⟨U, hU, hxU, σ, hσc, hσ⟩ := DualExact.exists_local_section S.g h₃ hxU₁
  obtain ⟨U₃, e₃, -, hxU₃, hU₃, he₃⟩ := h₃.exists_affine hxU
  let e : Fin r ⊕ Fin s → Γ(S.X₂, U₃) :=
    Sum.elim (fun i => S.f.app U₃ (resM S.X₁ (hU₃.trans hU) (e₁ i))) fun j => σ U₃ hU₃ (e₃ j)
  refine ⟨U₃, e, hxU₃, isFrame_of_basis (fun V h =>
    ((he₁.basis (h.trans (hU₃.trans hU))).prod (he₃.basis h)).map
      (LinearEquiv.ofBijective _
        (bijective_add_section S hS V (σ V (h.trans hU₃)) (hσ V _)))) fun V h i => ?_⟩
  rcases i with i | j
  · simp only [Module.Basis.map_apply, Module.Basis.prod_apply, Sum.elim_inl, Function.comp_apply,
      LinearMap.inl_apply, LinearEquiv.ofBijective_apply, LinearMap.coprod_apply, map_zero,
      add_zero, appLinear_apply, IsFrame.basis_apply, e]
    rw [app_resM, app_resM, resM_resM]
  · simp only [Module.Basis.map_apply, Module.Basis.prod_apply, Sum.elim_inr, Function.comp_apply,
      LinearMap.inr_apply, LinearEquiv.ofBijective_apply, LinearMap.coprod_apply, map_zero,
      zero_add, appLinear_apply, IsFrame.basis_apply, e]
    exact hσc U₃ V hU₃ h (e₃ j)

end GlobalTheory.VBExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothVectorAutomorphicDerivativesStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_vector_automorphic_derivatives : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (ρ : GA D V →* (Lp ℂ 2 (nuQ V μ 𝓕) →L[ℂ] Lp ℂ 2 (nuQ V μ 𝓕))), FinPair V μ 𝓕 → IsReg V μ 𝓕 ρ → ∀ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) → ∀ F, IsSmoothVector' θ V ρ F → (∀ k ∈ U, k ∈ GfC V → ρ k F = F) → ∃ ψ, Repr V μ 𝓕 F ψ ∧ IsAutFun V ψ ∧ (∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Mt V.rank), (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g, ContDiff ℝ ∞ fun t : Fin k → ℝ => ψ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)) ∧ ∀ l : List (D.what₂.Tau × Mt V.rank), (∀ p ∈ l, p.2 ∈ lieAt V p.1) → Continuous (l.foldr (fun p f => Rder θ V p.1 p.2 f) ψ) ∧ Repr V μ 𝓕 (l.foldr (dL2 θ V ρ) F) (l.foldr (fun p f => Rder θ V p.1 p.2 f) ψ) := by
  first | exact @GlobalTheory.SmoothRep.exists_smooth_repr | exact GlobalTheory.SmoothRep.exists_smooth_repr | (intros; apply GlobalTheory.SmoothRep.exists_smooth_repr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongApproximationQuaternionNormOneSplitStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strongApproximation_quaternion_normOne_split : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → (∃ p q : AF F, ε * (algebraMap F (AF F) b - (p ^ 2 - algebraMap F (AF F) a * q ^ 2)) = 0) → ∀ g : DA F a b, nrm g = 1 → g ∈ closure (H0 (a := a) (b := b) ε) := by
  first | exact @GlobalTheory.QSA.strongApprox_nrm_one | exact GlobalTheory.QSA.strongApprox_nrm_one | (intros; apply GlobalTheory.QSA.strongApprox_nrm_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubbundleFrameExistsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
open GlobalTheory.QCoh (freeModule)
open GlobalTheory.Twist (resM)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subbundle_frame_exists : ∀ {X : Scheme.{0}} {F : X.Modules} {U : X.Opens} {N : ℕ} (P : VB.Sub F) (c : Fin N → Γ(F, U)), VB.IsFrame c → ∀ (l : ℕ), l ≤ N → (∀ (V : X.Opens) (h : V ≤ U) (a : Fin N → Γ(X, V)), (∑ j, a j • resM F h (c j)) ∈ P.sec V ↔ ∀ j : Fin N, l ≤ (j : ℕ) → a j = 0) → ∃ e : Fin l → Γ(P.toMod, U), VB.IsFrame e := by
  first | exact @GlobalTheory.VB.exists_isFrame_sub_of_vanishing | exact GlobalTheory.VB.exists_isFrame_sub_of_vanishing | (intros; apply GlobalTheory.VB.exists_isFrame_sub_of_vanishing <;> assumption)
end

