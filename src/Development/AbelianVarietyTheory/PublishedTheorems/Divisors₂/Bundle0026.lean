import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsInhabitant
import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1579
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0001
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverOfIsPullback

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DetALeviTorus
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Published.LeviCentreModel

namespace GlobalTheory.Published.LeviInducedModel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem piInf_conj (hσ : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) (a : AE F E) :
    piInf τ (cA σ a) = starRingEnd ℂ (piInf τ a) := by
  change _ = starRingEnd ℂ (infEmb τ _)
  rw [infEmb_sigR hσ]
  change infEmb τ _ = _
  congr 1
  induction a using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a e => rfl

theorem cont_piInf {w : InfinitePlace F} (τ : EmbOver E w) : Continuous (piInf τ : AE F E → ℂ) := by
  let L : AE F E →+ ℂ := (piInf τ).toAddMonoidHom
  refine IsModuleTopology.continuous_of_distribMulActionHomₑ (R := AF F) (σ := (piInf τ).toMonoidHom.comp (algebraMap (AF F) (AE F E)).toMonoidHom) ?_
    { L with map_smul' := fun r x => by simp [L, Algebra.smul_def] }
  exact (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp ((continuous_apply w).comp continuous_fst) |>.congr fun a => by
    change _ = infEmb τ (_ ⊗ₜ[F] (1 : E))
    rw [infEmb_tmul, map_one, mul_one]; rfl

def chi (hσ : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) : Chr F E where
  toFun t := ⟨piInf τ (t.1 * cA σ (t⁻¹).1), by
    have : piInf τ t.1 * piInf τ (t⁻¹).1 = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    have h2 := congrArg norm this
    simpa [Submonoid.unitSphere, piInf_conj hσ] using h2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by
    change piInf τ ((a * b).1 * cA σ ((a * b)⁻¹).1) = piInf τ (a.1 * cA σ (a⁻¹).1) * piInf τ (b.1 * cA σ (b⁻¹).1)
    simp only [mul_inv_rev, Units.val_mul, map_mul]; ring)

theorem detA_levi_torus (δ : E) (t : (AE F E)ˣ) (m : UA σ (big F δ).J)
    (hm : IsLevi (W₁ := small F δ) (pl E) t 1 m) : detA (big F δ).J m = t.1 * cA σ (t⁻¹).1 := by
  obtain ⟨h1, h2, h3⟩ := hm
  have a0 := congrFun h1 0
  have a1 := congrFun h1 1
  have a2 := congrFun h1 2
  have b0 := congrFun h2 0
  have b1 := congrFun h2 1
  have b2 := congrFun h2 2
  have c1 := congrFun (congrFun h3 1) 0
  have c2 := congrFun (congrFun h3 2) 0
  have e : mat (1 : UA σ (small F δ).J) = 1 := rfl
  rw [e] at c1 c2
  generalize cA σ (t⁻¹).1 = s at *
  simp [pl, incV, incM, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.mul_apply] at a0 a1 a2 b0 b1 b2 c1 c2
  rw [detA_apply, Matrix.det_fin_three]
  simp [a0, a1, a2, b0, b1, b2, c1, c2]

theorem exists_inhabitant (hσ : IsCMExt F E σ) :
    ∃ (Y : Spc F E 3) (Y₁ : Spc F E 1) (H : Plane E 3 1) (ψ : UA σ Y.J → ℂ) (χ : Chr F E) (c : E)
      (φ : GAd σ (c • Y.J.map σ) → ℂ) (V : Submodule ℂ (GAd σ (c • Y₁.J.map σ) → ℂ)) (Kc : Set (UA σ Y.J)),
      (∀ i j, σ (Y.J j i) = -Y.J i j) ∧ form σ Y.J H.x H.x = 0 ∧ form σ Y.J H.y H.y = 0 ∧ form σ Y.J H.x H.y = 1 ∧
      (∀ u, form σ Y.J (H.ι *ᵥ u) H.x = 0 ∧ form σ Y.J (H.ι *ᵥ u) H.y = 0) ∧ H.ιᵀ * Y.J * H.ι.map σ = Y₁.J ∧
      (∀ u ∈ unip σ Y H, ∀ x, ψ (u * x) = ψ x) ∧ Continuous (fun t : (AE F E)ˣ => (χ t : ℂ)) ∧
      (∀ t m, IsLevi (W₁ := Y₁) H t 1 m → ∀ x, ψ (m * x) = (χ t : ℂ) * ψ x) ∧
      c ≠ 0 ∧ IsHermND σ (c • Y.J.map σ) ∧ IsHermND σ (c • Y₁.J.map σ) ∧
      (∀ (g : UA σ Y.J) (g' : GAd σ (c • Y.J.map σ)), g.1 = g'.1 → φ g' = ψ g) ∧ GlobalTheory.UAut.IsSm σ (c • Y.J.map σ) φ ∧
      FiniteDimensional ℂ V ∧ (∀ v ∈ V, GlobalTheory.UAut.IsSm σ (c • Y₁.J.map σ) v) ∧
      (∀ v ∈ V, ∀ z, GlobalTheory.UAut.IsCentral σ (c • Y₁.J.map σ) z → GlobalTheory.UAut.dop z v ∈ V) ∧
      (∀ x : UA σ Y.J, ∃ u ∈ unip σ Y H, ∃ t h₁ m, IsLevi (W₁ := Y₁) H t h₁ m ∧ ∃ k ∈ Kc, x = u * m * k) ∧
      (∀ k ∈ Kc, ∃ v ∈ V, ∀ (h₁ : UA σ Y₁.J) (m : UA σ Y.J) (g' : GAd σ (c • Y₁.J.map σ)),
        IsLevi (W₁ := Y₁) H 1 h₁ m → h₁.1 = g'.1 → v g' = ψ (m * k)) ∧
      ψ 1 = 1 ∧ (∃ t, χ t ≠ 1) ∧ (∃ v ∈ V, ∃ a, v a ≠ v 1) ∧
      FiniteDimensional ℂ (Submodule.span ℂ {u | ∃ z, GlobalTheory.UAut.IsCentral σ (c • Y.J.map σ) z ∧ u = GlobalTheory.UAut.dop z φ}) := by
  obtain ⟨δ, h0, hδ⟩ := exists_anti hσ
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
  refine ⟨big F δ, small F δ, pl E, fun g => piInf τ (detA _ g), chi hσ τ, δ, fun g' => piInf τ (g'.1.1.det),
    Submodule.span ℂ {fun g => piInf τ (g.1.1 0 0)}, Set.univ,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h0, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, inferInstance, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j; fin_cases i <;> fin_cases j <;> simp [big, hδ]
  · simp [form, big, pl, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · simp [form, big, pl, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · simp [form, big, pl, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · intro u; simp [form, big, pl, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · ext i j; fin_cases i; fin_cases j; simp [big, small, pl, Matrix.mul_apply, Fin.sum_univ_three]
  · intro u hu x; simp only [map_mul, detA_unip δ u hu, one_mul]
  · change Continuous fun t : (AE F E)ˣ => piInf τ (t.1 * cA σ (t⁻¹).1)
    simp only [map_mul, piInf_conj hσ]
    exact ((cont_piInf τ).comp Units.continuous_val).mul
      (Complex.continuous_conj.comp ((cont_piInf τ).comp Units.continuous_coe_inv))
  · intro t m hm x
    change piInf τ (detA _ (m * x)) = piInf τ (t.1 * cA σ (t⁻¹).1) * piInf τ (detA _ x)
    rw [map_mul, detA_levi_torus δ t m hm, map_mul]
  · intro i j; fin_cases i <;> fin_cases j <;> simp [big, hδ]
  · simp [big, Matrix.det_fin_three, h0, hδ]
  · intro i j; fin_cases i; fin_cases j; simp [small, hδ]
  · simp [small, h0, hδ]
  · intro g g' hg
    exact congrArg (fun x : GL (Fin 3) (AE F E) => piInf τ x.1.det) hg.symm
  · intro k γ hγ g
    have e := fun i j => GlobalTheory.UAut.Model.isSm_entry (J := δ • (big F δ).J.map σ) hσ τ i j k γ hγ g
    simp only [arch_entry] at e
    simp only [Matrix.det_fin_three, map_add, map_sub, map_mul]
    fun_prop
  · intro v hv k γ hγ g
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hv
    have e := GlobalTheory.UAut.Model.isSm_entry (J := δ • (small F δ).J.map σ) hσ τ 0 0 k γ hγ g
    simp only [arch_entry] at e
    exact e.const_smul a
  · intro v hv z _
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hv
    choose c hc using GlobalTheory.UAut.foldr_lineDer_char (φ := fun g' : GAd σ (δ • (small F δ).J.map σ) => piInf τ (g'.1.1 0 0))
      (fun g h => by
        rw [← map_mul]
        change piInf τ ((g.1.1 * h.1.1) 0 0) = _
        simp [Matrix.mul_apply]) a
    exact Submodule.mem_span_singleton.2 ⟨z.sum fun l a => a * c l, funext fun g => by
      simp only [GlobalTheory.UAut.dop, hc]; simp [Finsupp.sum, Finset.sum_mul, mul_assoc]⟩
  · intro x
    refine ⟨1, one_mem _, 1, 1, 1, ⟨?_, ?_, ?_⟩, x, trivial, by simp⟩
    · change (1 : Matrix _ _ _) *ᵥ _ = _; simp
    · change (1 : Matrix _ _ _) *ᵥ _ = _; simp
    · change (1 : Matrix _ _ _) * _ = _ * (1 : Matrix _ _ _); simp
  · intro k _
    refine ⟨piInf τ (detA _ k) • fun g => piInf τ (g.1.1 0 0), Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), ?_⟩
    intro h₁ m g' hm e
    simp only [map_mul, detA_levi δ h₁ m hm, mat, e, Pi.smul_apply, smul_eq_mul, mul_comm]
  · simp
  · refine ⟨Units.map (inclR (F := F) (E := E) (AF F)).toMonoidHom (Units.mk0 δ h0), fun e => ?_⟩
    have e1 : piInf τ (inclR (F := F) (AF F) δ * inclR (F := F) (AF F) (σ δ⁻¹)) = 1 := congrArg Subtype.val e
    rw [← map_mul, map_inv₀, hδ, inv_neg, mul_neg, mul_inv_cancel₀ h0, map_neg, map_one, map_neg, map_one] at e1
    norm_num at e1
  · refine ⟨_, Submodule.mem_span_singleton_self _, ⟨-1, show _ * _ * _ = _ by
      ext i j; fin_cases i; fin_cases j; simp [Formalism.UG.cT, Matrix.mul_apply]⟩, ?_⟩
    change piInf τ ((-1 : Matrix (Fin 1) (Fin 1) _) 0 0) ≠ piInf τ ((1 : Matrix (Fin 1) (Fin 1) _) 0 0)
    simp only [Matrix.neg_apply, Matrix.one_apply_eq, map_neg, map_one]
    norm_num
  · refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ
      {fun g' : GAd σ (δ • (big F δ).J.map σ) => piInf τ (g'.1.1.det)}) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, -, rfl⟩
    choose c hc using GlobalTheory.UAut.Model.foldr_char (φ := fun g' : GAd σ (δ • (big F δ).J.map σ) => piInf τ (g'.1.1.det))
      fun g h => by rw [← map_mul, ← Matrix.det_mul]; rfl
    exact Submodule.mem_span_singleton.2 ⟨z.sum fun l a => a * c l, funext fun g => by
      simp [GlobalTheory.UAut.dop, hc, Finsupp.sum, Finset.sum_mul, mul_assoc]⟩

example (hσ : IsCMExt F E σ) {δ : E} (hJ : IsHermND σ (δ • (big F δ).J.map σ)) :
    ∃ φ : GAd σ (δ • (big F δ).J.map σ) → ℂ, GlobalTheory.UAut.IsSm σ _ φ ∧ ¬ FiniteDimensional ℂ (Submodule.span ℂ
      {u | ∃ z, GlobalTheory.UAut.IsCentral σ (δ • (big F δ).J.map σ) z ∧ u = GlobalTheory.UAut.dop z φ}) := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
  exact ⟨_, GlobalTheory.UAut.Model.not_zfin_exp hσ hJ τ 0⟩

end GlobalTheory.Published.LeviInducedModel

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InterNumDetNonposSplitTorus
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic
open GlobalTheory.LB (toMod)
open GlobalTheory.Twist (resM resM_resM resM_self)

namespace GlobalTheory.Published

def SemiAbelianLieSeminegative : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)],
    SmoothOfRelativeDimension 1 (strHom k C) → IsProjOver (strHom k C) → GeometricallyConnected (strHom k C) →
    ∀ (G : Over C) [GrpObj G] [IsSemiAbelian G] (W : C.Modules) (r : ℕ), IsVB W r →
      ∀ i : W ⟶ Lie G, Mono i → interNum k (structureModule C) ![det W r] ≤ 0

end GlobalTheory.Published

namespace GlobalTheory.LieSemineg

section Curve

variable {k : Type} [Field k] {C : Scheme.{0}} [Algebra k Γ(C, ⊤)]

theorem isIntegral_curve (hs : SmoothOfRelativeDimension 1 (strHom k C))
    (hc : GeometricallyConnected (strHom k C)) : IsIntegral C :=
  have : Smooth (strHom k C) := SmoothOfRelativeDimension.smooth 1 _
  isIntegral_of_smooth_of_geometricallyConnected (strHom k C)

theorem dim_curve [Nonempty C] (hs : SmoothOfRelativeDimension 1 (strHom k C)) : topologicalKrullDim C = 1 := by
  have key : topologicalKrullDim (Set.univ : Set C) = (1 : ℕ) := by
    refine topologicalKrullDim_eq_of_forall_exists_isOpen Set.univ_nonempty fun x _ => ?_
    obtain ⟨U, hU, hx, -⟩ := Opens.isBasis_iff_nbhd.1 C.isBasis_affineOpens (Opens.mem_top x)
    replace hU : IsAffineOpen (X := C) U := hU
    refine ⟨U, U.isOpen, hx, ?_⟩
    rw [Set.inter_univ, topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding hU.range_fromSpec]
    exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := Γ(C, U))).trans
      (SmoothDim.ringKrullDim_affineOpen k _ _ _ hs U hU ⟨x, hx⟩)
  exact (topologicalKrullDim_eq_of_isEmbedding (e := (id : C → C)) Topology.IsEmbedding.id Set.range_id).symm.trans key

theorem interNum_det_dual (hp : IsProjOver (strHom k C)) (hd : topologicalKrullDim C = 1) {W : C.Modules} {r : ℕ}
    (hW : IsVB W r) : interNum k (structureModule C) ![det (VB.dual W) r] =
      -interNum k (structureModule C) ![det W r] := by
  obtain ⟨_, H, hH⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hp
  have e := interNum_one_of_cls_eq_add (k := k) hH hd (LB.isLB_triv C) hW.dual.isLB_det hW.isLB_det
    (by rw [← (cls_eq_iff (isLB_dual hW.isLB_det) hW.dual.isLB_det).2 hW.lbIso_det_dual, cls_dual_add, cls_triv])
  rw [interNum_eq_zero_of_cls_eq_zero k _ (isLB_vecOne (LB.isLB_triv C)) 0 rfl] at e
  omega

end Curve

theorem mono_of_ne_zero {X : Scheme.{0}} [IsIntegral X] {L F : X.Modules} {g : ℕ} (hL : IsVB L 1) (hF : IsVB F g)
    (φ : L ⟶ F) (hφ : φ ≠ 0) : Mono φ := by
  refine IsTorsionFree.mono_of_injective_generic hL.isTorsionFree φ ?_
  obtain ⟨b⟩ := hL.nonempty_basis_stalk (genericPoint X)
  obtain ⟨c⟩ := hF.nonempty_basis_stalk (genericPoint X)
  have h0 : stalkLinear φ (genericPoint X) (b 0) ≠ 0 := fun h0 => hφ <| by
    have h1 : stalkLinear φ (genericPoint X) = 0 := b.ext fun j => by rwa [Subsingleton.elim j 0]
    ext V s
    by_cases hV : genericPoint X ∈ V
    · refine hF.isTorsionFree V hV _ ?_
      rw [← stalkLinear_germ, h1]
      rfl
    · exact Twist.sec_ext_of_cover (ι := Empty) (fun _ => V) (fun _ => le_rfl)
        (fun x hx => (hV (genericPoint_mem hx)).elim) fun x => x.elim
  rw [injective_iff_map_eq_zero]
  intro t ht
  rw [← b.sum_repr t, Fin.sum_univ_one] at ht ⊢
  rw [map_smul] at ht
  have := hF.free_stalk (genericPoint X)
  rw [(smul_eq_zero.1 ht).resolve_right h0, zero_smul]

theorem exists_det_ne_zero_field {K ι : Type} [Field K] [Fintype ι] {r : ℕ} (N : Matrix (Fin r) ι K)
    (hN : LinearIndependent K N.row) : ∃ σ : Fin r → ι, (N.submatrix id σ).det ≠ 0 := by
  by_contra! H
  have hs : Submodule.span K (Set.range N.col) = ⊤ := Submodule.eq_top_of_finrank_eq (by
    rw [← Matrix.rank_eq_finrank_span_cols, hN.rank_matrix, Module.finrank_fintype_fun_eq_card])
  have e : (Pi.basisFun K (Fin r)).det.toMultilinearMap = 0 := by
    refine MultilinearMap.ext_of_span_eq_top (γ := fun _ => ι) (g := fun _ j => N.col j) (fun _ => hs) fun σ => ?_
    rw [_root_.zero_apply, AlternatingMap.coe_multilinearMap, Module.Basis.det_apply, ← H σ]
    rfl
  have h₂ := DFunLike.congr_fun e ⇑(Pi.basisFun K (Fin r))
  rw [_root_.zero_apply, AlternatingMap.coe_multilinearMap, Module.Basis.det_self] at h₂
  exact one_ne_zero h₂

theorem exists_det_ne_zero {A ι : Type} [CommRing A] [IsDomain A] [Fintype ι] {r : ℕ} (M : Matrix (Fin r) ι A)
    (h : LinearIndependent A M.row) : ∃ σ : Fin r → ι, (M.submatrix id σ).det ≠ 0 := by
  obtain ⟨σ, hσ⟩ := exists_det_ne_zero_field (M.map (algebraMap A (FractionRing A)))
    ((linearIndependent_algebraMap_comp_iff (S := FractionRing A) (v := M.row)).2 h)
  refine ⟨σ, fun h₀ => hσ ?_⟩
  rw [Matrix.submatrix_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h₀, map_zero]

theorem hasNonzeroSec_det_dual {X : Scheme.{0}} [IsIntegral X] {W F : X.Modules} {r : ℕ} (hW : IsVB W r)
    {ι : Type} [Fintype ι] {f : ι → Γ(F, ⊤)} (hf : IsFrame f) (i : W ⟶ F) [Mono i] :
    HasNonzeroSec (det (VB.dual W) r) := by
  obtain ⟨U, e, hU, he⟩ := hW (genericPoint X)
  have hV : (⊤ ⊓ U : X.Opens) ≤ U := inf_le_right
  have : Nonempty (⊤ ⊓ U : X.Opens) := ⟨⟨_, trivial, hU⟩⟩
  let M : Matrix (Fin r) ι Γ(X, ⊤ ⊓ U) := fun b j =>
    (hf.basis le_top).repr (i.app _ (resM W hV (e b))) j
  have hM : LinearIndependent Γ(X, ⊤ ⊓ U) M.row := by
    have h₁ := ((he.basis hV).linearIndependent.map' ((hf.basis le_top).equivFun.toLinearMap ∘ₗ appLinear i _)
      (LinearMap.ker_eq_bot.2 ((hf.basis le_top).equivFun.injective.comp (injective_app_of_mono i _))))
    rw [he.coe_basis] at h₁
    exact h₁
  obtain ⟨σ, hσ⟩ := exists_det_ne_zero M hM
  refine ⟨LB.globalEquiv _ (wedge (VB.dual W) ⊤ r fun a => (dualMap i).app ⊤ (hf.coord (σ a))), fun h => hσ ?_⟩
  have h₀ := congrArg (detCoord · ⟨U, he.coord, he.dual⟩) ((LinearEquiv.map_eq_zero_iff _).1 h)
  simp only [detCoord_wedge, detCoord_zero, Module.Basis.det_apply] at h₀
  refine Eq.trans (congrArg Matrix.det ?_) h₀
  ext b a
  rw [Module.Basis.toMatrix_apply, he.dual_basis_repr]
  simp
  rfl

theorem interNum_det_nonpos_of_frame {k : Type} [Field k] {C : Scheme.{0}} [Algebra k Γ(C, ⊤)] [IsIntegral C]
    (hp : IsProjOver (strHom k C)) (hd : topologicalKrullDim C = 1) {W F : C.Modules} {r : ℕ} (hW : IsVB W r)
    {ι : Type} [Fintype ι] {f : ι → Γ(F, ⊤)} (hf : IsFrame f) (i : W ⟶ F) [Mono i] :
    interNum k (structureModule C) ![det W r] ≤ 0 := by
  obtain ⟨_, H, hH⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hp
  obtain ⟨s, hs⟩ := hasNonzeroSec_iff.1 (hasNonzeroSec_det_dual hW hf i)
  have := (interNum_one_nonneg_of_sec (k := k) hH hd hW.dual.isLB_det s hs).1
  rw [interNum_det_dual hp hd hW] at this
  omega

theorem interNum_det_nonpos_splitTorus {k : Type} [Field k] {C : Scheme.{0}} [Algebra k Γ(C, ⊤)]
    (hs : SmoothOfRelativeDimension 1 (strHom k C)) (hp : IsProjOver (strHom k C))
    (hc : GeometricallyConnected (strHom k C)) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (W : C.Modules) (r : ℕ) (hW : IsVB W r) (i : W ⟶ Lie (splitTorus C X)) [Mono i] :
    IsSemiAbelian (splitTorus C X) ∧ interNum k (structureModule C) ![det W r] ≤ 0 :=
  have := isIntegral_curve hs hc
  ⟨inferInstance, interNum_det_nonpos_of_frame hp (dim_curve hs) hW
    (isFrame_dlogChar C (Module.Free.chooseBasis ℤ X)).dual i⟩

theorem projectiveLine_hyps (k : Type) [Field k] :
    letI := algebraΓOfHom (PSpace.str k 1)
    SmoothOfRelativeDimension 1 (strHom k (PSpace k 1)) ∧ IsProjOver (strHom k (PSpace k 1)) ∧
      GeometricallyConnected (strHom k (PSpace k 1)) := by
  letI := algebraΓOfHom (PSpace.str k 1)
  rw [strHom_eq (f := PSpace.str k 1) fun _ => rfl]
  exact ⟨Adelic.smoothOfRelativeDimension_pspace k 1, ProjSpace.isProjOver_pspace_str k 1,
    Adelic.geometricallyConnected_pspace k 1⟩

end GlobalTheory.LieSemineg

namespace GlobalTheory.Published.SemiAbelianLieSeminegative

open GlobalTheory.LieSemineg

variable (h : SemiAbelianLieSeminegative) {k : Type} [Field k] [CharZero k] {C : Scheme.{0}} [Algebra k Γ(C, ⊤)]
  (hs : SmoothOfRelativeDimension 1 (strHom k C)) (hp : IsProjOver (strHom k C))
  (hc : GeometricallyConnected (strHom k C)) (G : Over C) [GrpObj G] [IsSemiAbelian G]

include h hs hp hc

theorem line {S : LB C} (hS : S.IsLB) (φ : toMod S ⟶ Lie G) (hφ : φ ≠ 0) :
    interNum k (structureModule C) ![S] ≤ 0 := by
  have := isIntegral_curve hs hc
  obtain ⟨g, -, hg⟩ := exists_isVB_of_isSemiAbelian G
  have e := h k C hs hp hc G _ 1 (isVB_toMod hS) φ (mono_of_ne_zero (isVB_toMod hS) hg φ hφ)
  refine (interNum_congr_lbIso k _ (isLB_vecOne hS) (isLB_vecOne (isVB_toMod hS).isLB_det) fun j => ?_).trans_le e
  fin_cases j
  exact lbIso_det_toMod hS

theorem quotient_omega {Q : C.Modules} {r : ℕ} (hQ : IsVB Q r) (π : omega G ⟶ Q) [Epi π] :
    0 ≤ interNum k (structureModule C) ![det Q r] := by
  have := isIntegral_curve hs hc
  have e := h k C hs hp hc G _ r hQ.dual (dualMap π) inferInstance
  rw [interNum_det_dual hp (dim_curve hs) hQ] at e
  omega

theorem dual_det_nonneg {W : C.Modules} {r : ℕ} (hW : IsVB W r) (i : W ⟶ Lie G) [Mono i] :
    0 ≤ interNum k (structureModule C) ![CechPic.dual (det W r)] := by
  have := isIntegral_curve hs hc
  have e := h k C hs hp hc G W r hW i inferInstance
  have e' := interNum_congr_lbIso k (structureModule C) (isLB_vecOne (isLB_dual hW.isLB_det))
    (isLB_vecOne hW.dual.isLB_det) fun j => by fin_cases j; exact hW.lbIso_det_dual
  rw [e', interNum_det_dual hp (dim_curve hs) hW]
  omega

end GlobalTheory.Published.SemiAbelianLieSeminegative
end
end

