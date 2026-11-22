import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0597
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0462
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0260
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0011
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0016
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0006
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0018
import Mathlib.RingTheory.Nilpotent.Exp
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0067

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmHom
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

noncomputable section

namespace UpperTheory.V.Loc

section Generic

variable {G : Type} [Group G] {Q V V' W : Type} [Field Q] [AddCommGroup V] [Module Q V] [AddCommGroup V']
  [Module Q V'] [AddCommGroup W] [Module Q W] [FiniteDimensional Q V]

private theorem exists_inj_dual_tprod (ρ : Representation Q G V) (ρ' : Representation Q G V')
    (π : Representation Q G W) (b : W →ₗ[Q] V →ₗ[Q] V') (hb : ∀ g w x, b (π g w) (ρ g x) = ρ' g (b w x))
    (hi : Function.Injective b) :
    ∃ f : W →ₗ[Q] Module.Dual Q V ⊗[Q] V', (∀ g w, f (π g w) = (ρ.dual.tprod ρ') g (f w)) ∧
      Function.Injective f := by
  let e := dualTensorHomEquiv Q V V'
  refine ⟨e.symm.toLinearMap ∘ₗ b, fun g w => ?_, e.symm.injective.comp hi⟩
  have key : ∀ (t : Module.Dual Q V ⊗[Q] V') (x : V),
      e ((ρ.dual.tprod ρ') g t) (ρ g x) = ρ' g (e t x) := by
    intro t x
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add s t hs ht => simp only [map_add, LinearMap.add_apply, hs, ht]
    | tmul f y => simp [e, Module.Dual.transpose_apply]
  apply e.injective
  ext x
  obtain ⟨x, rfl⟩ : ∃ y, ρ g y = x := ⟨ρ g⁻¹ x, by simp⟩
  rw [key]
  simp [hb]

end Generic

section Transport

variable {l : ℕ} [Fact l.Prime] {G H A V : Type} [Group G] [Group H] [CommRing A] [Algebra ℚ_[l] A]
  [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V]

private theorem admissible_transport_equiv (ψ : H →* GQ l) (e : G ≃* H) (ρ : Representation A G V) :
    (IsCr (ψ.comp e.toMonoidHom) ρ ↔ IsCr ψ (ρ.comp e.symm.toMonoidHom : Representation A H V)) ∧
    (IsDr (ψ.comp e.toMonoidHom) ρ ↔ IsDr ψ (ρ.comp e.symm.toMonoidHom : Representation A H V)) := by
  have hr : (ψ.comp e.toMonoidHom).range = ψ.range := by
    ext x
    exact ⟨fun ⟨g, hg⟩ => ⟨e g, hg⟩, fun ⟨h, hh⟩ => ⟨e.symm h, by simpa using hh⟩⟩
  have h1 : Dcr (ψ.comp e.toMonoidHom) (resCoef ℚ_[l] ρ) =
      Dcr ψ (resCoef ℚ_[l] (ρ.comp e.symm.toMonoidHom : Representation A H V)) := by
    unfold Dcr
    refine e.toEquiv.iInf_congr fun g => ?_
    simp [actC, resCoef]
  have h2 : Ddr (ψ.comp e.toMonoidHom) (resCoef ℚ_[l] ρ) =
      Ddr ψ (resCoef ℚ_[l] (ρ.comp e.symm.toMonoidHom : Representation A H V)) := by
    unfold Ddr
    refine e.toEquiv.iInf_congr fun g => ?_
    simp [actD, resCoef]
  unfold IsCr IsDr
  rw [hr, h1, h2]
  exact ⟨Iff.rfl, Iff.rfl⟩

end Transport

section Field

variable {l : ℕ} [Fact l.Prime] (K : FinExt l) {V V' W : Type} [AddCommGroup V] [Module ℚ_[l] V]
  [AddCommGroup V'] [Module ℚ_[l] V'] [AddCommGroup W] [Module ℚ_[l] W] [FiniteDimensional ℚ_[l] V]
  [FiniteDimensional ℚ_[l] V'] [FiniteDimensional ℚ_[l] W]
  (ρ : Representation ℚ_[l] ↥(GK K) V) (ρ' : Representation ℚ_[l] ↥(GK K) V')
  (π : Representation ℚ_[l] ↥(GK K) W) (f : W →ₗ[ℚ_[l]] Module.Dual ℚ_[l] V ⊗[ℚ_[l]] V')
  (hf : ∀ g w, f (π g w) = (ρ.dual.tprod ρ') g (f w)) (hi : Function.Injective f)
include hf hi

private theorem crys_hom (h : IsCrys ((PP l).PD K) ρ) (h' : IsCrys ((PP l).PD K) ρ') :
    IsCrys ((PP l).PD K) π := by
  obtain ⟨T⟩ := tiedP l
  obtain ⟨C, hfit⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l _ _ T
  haveI := GlobalTheory.RegularRing.isDomain_of_tied T K
  have h1 := GlobalTheory.RegularRing.fracInv hfit (GlobalTheory.T.algClosure_tensor_bcris_to_bdR_injective l C) K
  have h2 := GlobalTheory.RegularRing.lineUnit hfit (GlobalTheory.T.bcris_regular_of_tensorInj l C (GlobalTheory.T.algClosure_tensor_bcris_to_bdR_injective l C)) K
  exact GlobalTheory.RegularRing.subCrys _ ℚ_[l] h1 _ _ _ π f hf hi
    (GlobalTheory.RegularRing.tensorCrys _ ℚ_[l] h1 h2 _ _ _ _
      (GlobalTheory.RegularRing.dualCrys _ ℚ_[l] h1 h2 _ ρ h) h')

private theorem dR_hom (h : IsDR ((PP l).PD K) ρ) (h' : IsDR ((PP l).PD K) ρ') :
    IsDR ((PP l).PD K) π := by
  obtain ⟨T⟩ := tiedP l
  have := K.2
  have hF := GlobalTheory.DRFil.isField_dR T
  have s : GlobalTheory.DRFil.Spans ((PP l).PD K) ρ := GlobalTheory.Per.DeRhamSpan.span_of_isField _ ρ hF h
  have s' : GlobalTheory.DRFil.Spans ((PP l).PD K) ρ' := GlobalTheory.Per.DeRhamSpan.span_of_isField _ ρ' hF h'
  have sd : GlobalTheory.DRFil.Spans ((PP l).PD K) ρ.dual :=
    GlobalTheory.DRFil.spans_dual_of_spans _ ρ ρ.dual (Module.Dual.eval ℚ_[l] V) hF
      (fun g x y => by simp [Module.Dual.transpose_apply]) Function.bijective_id s
  have st : GlobalTheory.DRFil.Spans ((PP l).PD K) (ρ.dual.tprod ρ') :=
    GlobalTheory.DRFil.Spans.tensor _ (LinearEquiv.refl _ _) (fun g x y => by simp) sd s'
  have sw := GlobalTheory.DRSubQuot.spans_of_injective _ π _ f hf hF hi st
  obtain ⟨h1, h2⟩ := GlobalTheory.Per.FontaineBound.ddR_finite_le ((PP l).PD K) hF π
  exact le_antisymm h2 (GlobalTheory.DRFil.finrank_mul_le_finrank_DdR_of_spans _ π h1 sw)

end Field

end UpperTheory.V.Loc

theorem UpperTheory.V.Loc.isCrys_isDR_internalHom :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {A : Type} [CommRing A] [Algebra ℚ_[l] A] {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] {V' : Type} [AddCommGroup V'] [Module A V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] A V'] [FiniteDimensional ℚ_[l] V'] [TopologicalSpace V'] [IsModuleTopology ℚ_[l] V'] [IsTopologicalAddGroup V'] [ContinuousConstSMul A V'] {W : Type} [AddCommGroup W] [Module A W] [Module ℚ_[l] W] [IsScalarTower ℚ_[l] A W] [FiniteDimensional ℚ_[l] W] [TopologicalSpace W] [IsModuleTopology ℚ_[l] W] [IsTopologicalAddGroup W] [ContinuousConstSMul A W] (ρ : Representation A G V) (ρ' : Representation A G V') (π : Representation A G W), ContAction ρ → ContAction ρ' → ContAction π → ∀ b : W →ₗ[ℚ_[l]] V →ₗ[ℚ_[l]] V', (∀ g w x, b (π g w) (ρ g x) = ρ' g (b w x)) → Function.Injective b → (IsCr φ ρ → IsCr φ ρ' → IsCr φ π) ∧ (IsDr φ ρ → IsDr φ ρ' → IsDr φ π) := by
  intro l _ G _ _ _ φ hφ A _ _ V _ _ _ _ _ _ _ _ _ V' _ _ _ _ _ _ _ _ _ W _ _ _ _ _ _ _ _ _ ρ ρ' π _ _ _ b hb hi
  obtain ⟨K, e, -, -, rfl, -⟩ := openField φ hφ
  obtain ⟨f, hf, hfi⟩ := exists_inj_dual_tprod
    (resCoef ℚ_[l] (ρ.comp e.symm.toMonoidHom : Representation A ↥(GK K) V))
    (resCoef ℚ_[l] (ρ'.comp e.symm.toMonoidHom : Representation A ↥(GK K) V'))
    (resCoef ℚ_[l] (π.comp e.symm.toMonoidHom : Representation A ↥(GK K) W)) b
    (fun g w x => hb (e.symm g) w x) hi
  rw [(admissible_transport_equiv _ e ρ).1, (admissible_transport_equiv _ e ρ').1, (admissible_transport_equiv _ e π).1, (admissible_transport_equiv _ e ρ).2,
    (admissible_transport_equiv _ e ρ').2, (admissible_transport_equiv _ e π).2, (isCrIff K _).1, (isCrIff K _).1, (isCrIff K _).1,
    (isCrIff K _).2, (isCrIff K _).2, (isCrIff K _).2]
  exact ⟨crys_hom K _ _ _ f hf hfi, dR_hom K _ _ _ f hf hfi⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsNeOne
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private theorem sandwich {E M : Type} [Field E] [AddCommGroup M] [Module E M] (B S Z : Submodule E M)
    (hBS : B ≤ S) (hSZ : S ≤ Z) [Module.Finite E B]
    [hQ : Module.Finite E ↥((S.comap Z.subtype).map (B.comap Z.subtype).mkQ)] :
    Module.Finite E S ∧
      finrank E S = finrank E ↥((S.comap Z.subtype).map (B.comap Z.subtype).mkQ) + finrank E B := by
  let f : S →ₗ[E] (Z ⧸ B.comap Z.subtype) := (B.comap Z.subtype).mkQ ∘ₗ Submodule.inclusion hSZ
  have hr : LinearMap.range f = (S.comap Z.subtype).map (B.comap Z.subtype).mkQ := by
    rw [LinearMap.range_comp, Submodule.range_inclusion]
  have hk : LinearMap.ker f = B.comap S.subtype := by
    ext x
    simp [f]
  have eB := Submodule.comapSubtypeEquivOfLe hBS
  have hkf : Module.Finite E ↥(LinearMap.ker f) := by
    rw [hk]; exact Module.Finite.equiv eB.symm
  have hrf : Module.Finite E ↥(LinearMap.range f) := by rw [hr]; exact hQ
  have hS : Module.Finite E S := by
    rw [Module.finite_def]
    refine Submodule.fg_of_fg_map_of_fg_inf_ker f ?_ ?_
    · rw [Submodule.map_top]; exact Module.Finite.iff_fg.1 hrf
    · rw [top_inf_eq]; exact Module.Finite.iff_fg.1 hkf
  refine ⟨hS, ?_⟩
  rw [← LinearMap.finrank_range_add_finrank_ker f, hr, hk, eB.finrank_eq]

private theorem exists_ne_one {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G]
    (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [Algebra ℤ_[l] E]
    [IsScalarTower ℤ_[l] ℚ_[l] E] (κ : G →* Eˣ) (w : ℤ) (hw : w ≠ 0) (h : HasWeight φ κ w) :
    ∃ g, κ g ≠ 1 := by
  obtain ⟨U, hU, h⟩ := h
  obtain ⟨-, s, ⟨⟨g, hg, rfl⟩, hs⟩, hfin⟩ := (cycInertia l).2 (U.map φ) (hφ.isOpenMap _ hU)
  refine ⟨g, fun h1 => hfin ?_⟩
  have hinj : Function.Injective (algebraMap ℤ_[l] E) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] E]
    exact (algebraMap ℚ_[l] E).injective.comp Subtype.val_injective
  have h2 := h g hg hs
  rw [h1] at h2
  have h3 : cyc l l (φ g) ^ w = 1 := by
    apply Units.map_injective (f := (algebraMap ℤ_[l] E : ℤ_[l] →* E)) hinj
    rw [map_zpow, map_one]
    exact h2.symm
  exact isOfFinOrder_iff_zpow_eq_one.2 ⟨w, hw, h3⟩

private theorem finrank_ddr {l : ℕ} [Fact l.Prime] {G : Type} [Group G]
    (φ : G →* GQ l) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (ρ : Representation E G E) (h : IsDr φ ρ) : finrank E ↥(Ddr φ ρ) = φ.range.index := by
  have he : Ddr φ (resCoef ℚ_[l] ρ) = (Ddr φ ρ).restrictScalars ℚ_[l] := by
    ext x
    simp only [Ddr, Submodule.restrictScalars_mem, Submodule.mem_iInf, LinearMap.mem_ker]
    rfl
  have h1 : finrank ℚ_[l] ↥(Ddr φ ρ) = φ.range.index * finrank ℚ_[l] E := by
    unfold IsDr at h
    rw [he] at h
    exact h
  rw [← Module.finrank_mul_finrank ℚ_[l] E, mul_comm] at h1
  exact Nat.eq_of_mul_eq_mul_right Module.finrank_pos h1

theorem UpperTheory.V.Loc.z1fChar :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] [TopologicalSpace E] [IsModuleTopology ℚ_[l] E] [IsTopologicalRing E] (κ : G →* Eˣ), Continuous (fun g => (κ g : E)) → ∀ w : ℤ, HasWeight φ κ w → (w < 0 → UpperTheory.V.Loc.finiteCocycles φ (chRep κ) = ReciprocityTheory.Gal.B1 (chRep κ) ∧ finrank E ↥(ReciprocityTheory.Gal.B1 (chRep κ)) = 1) ∧ (0 < w → Module.Finite E ↥(UpperTheory.V.Loc.finiteCocycles φ (chRep κ)) ∧ finrank E ↥(UpperTheory.V.Loc.finiteCocycles φ (chRep κ)) = φ.range.index + 1) := by
  intro hP l _ G _ _ _ φ hφ E _ _ _ _ _ _ _ _ κ hκ w hw
  have hc : ReciprocityTheory.Gal.ContAction (chRep κ) := by
    have : (fun p : G × E => chRep κ p.1 p.2) = fun p => (κ p.1 : E) * p.2 := by
      funext p; simp [chRep]
    unfold ReciprocityTheory.Gal.ContAction
    rw [this]
    exact (hκ.comp continuous_fst).mul continuous_snd
  obtain ⟨hdr, hfil⟩ := charFil φ hφ κ hκ w hw
  obtain ⟨hfin, hdim⟩ := bkDim hP φ hφ (chRep κ) hc hdr
  have hBS := (z1fMap φ (chRep κ) (chRep κ)).1 hc
  have hSZ : UpperTheory.V.Loc.finiteCocycles φ (chRep κ) ≤ ReciprocityTheory.Gal.Z1 (chRep κ) := fun c h => h.1
  have hBf : Module.Finite E ↥(ReciprocityTheory.Gal.B1 (chRep κ)) := by
    unfold ReciprocityTheory.Gal.B1; infer_instance
  obtain ⟨hS, hSd⟩ := sandwich _ _ _ hBS hSZ (hQ := hfin)
  replace hSd : finrank E ↥(UpperTheory.V.Loc.finiteCocycles φ (chRep κ)) =
    finrank E ↥(finiteCohomology φ (chRep κ)) + finrank E ↥(ReciprocityTheory.Gal.B1 (chRep κ)) := hSd
  have key : w ≠ 0 → ReciprocityTheory.Gal.H0 (chRep κ) = ⊥ ∧ finrank E ↥(ReciprocityTheory.Gal.B1 (chRep κ)) = 1 := by
    intro h0
    obtain ⟨g, hg⟩ := exists_ne_one φ hφ κ w h0 hw
    have hz : ∀ m : E, chRep κ g m - m = 0 → m = 0 := by
      intro m hm
      have h1 : ((κ g : E) - 1) * m = 0 := by
        rw [sub_mul, one_mul]; simpa [chRep] using hm
      rcases mul_eq_zero.1 h1 with h | h
      · exact absurd (Units.val_eq_one.1 (sub_eq_zero.1 h)) hg
      · exact h
    refine ⟨?_, ?_⟩
    · rw [eq_bot_iff]
      intro m hm
      exact hz m (sub_eq_zero.2 ((mem_riemannRochSpace_iff_regularAt_everywhere _ _).1 hm g))
    · unfold ReciprocityTheory.Gal.B1
      rw [LinearMap.finrank_range_of_inj, finrank_self]
      rw [injective_iff_map_eq_zero]
      intro m hm
      exact hz m (congrFun hm g)
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨h0, hB⟩ := key h.ne
    rw [h0, (hfil 0).1 (by omega), finrank_ddr φ _ hdr, finrank_bot, finrank_self] at hdim
    refine ⟨(Submodule.eq_of_le_of_finrank_eq hBS (by omega)).symm, hB⟩
  · obtain ⟨h0, hB⟩ := key h.ne'
    rw [h0, (hfil 0).2 (by omega), finrank_bot, finrank_bot, finrank_self] at hdim
    exact ⟨hS, by omega⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.InertiaFixesOfFrobeniusAnnihilatedMemFilZero
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology Polynomial

private theorem companion {R : Type} [CommRing R] (P : R[X]) (hP : P.Monic) (h0 : IsUnit (P.coeff 0)) :
    ∃ M : Matrix (Fin P.natDegree) (Fin P.natDegree) R, IsUnit M.det ∧
      ∀ i : Fin P.natDegree, P ∣ X ^ ((i : ℕ) + 1) - ∑ j : Fin P.natDegree, C (M i j) * X ^ (j : ℕ) := by
  classical
  let b : Basis (Fin P.natDegree) R (AdjoinRoot P) := (AdjoinRoot.powerBasis' hP).basis
  have hb : ∀ i : Fin P.natDegree, b i = AdjoinRoot.root P ^ (i : ℕ) := fun i =>
    (AdjoinRoot.powerBasis' hP).basis_eq_pow i
  have hr : IsUnit (AdjoinRoot.root P) := by
    have h1 : AdjoinRoot.mk P (X * divX P + C (P.coeff 0)) = 0 := by
      rw [X_mul_divX_add]; exact AdjoinRoot.mk_self
    rw [map_add, map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at h1
    have h2 : IsUnit (AdjoinRoot.root P * AdjoinRoot.mk P (divX P)) := by
      rw [eq_neg_of_add_eq_zero_left h1]
      exact (h0.map (AdjoinRoot.of P)).neg
    exact isUnit_of_mul_isUnit_left h2
  refine ⟨(Algebra.leftMulMatrix b (AdjoinRoot.root P)).transpose, ?_, fun i => ?_⟩
  · rw [Matrix.det_transpose, ← Matrix.isUnit_iff_isUnit_det]
    exact hr.map _
  · rw [← AdjoinRoot.mk_eq_mk]
    have h := b.sum_repr (AdjoinRoot.root P * b i)
    simp only [map_sum, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, Matrix.transpose_apply,
      Algebra.leftMulMatrix_eq_repr_mul]
    rw [pow_succ', ← hb, ← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [h, Algebra.smul_def, hb j]
    rfl

theorem UpperTheory.inertia_fixes_of_frobenius_annihilated_mem_fil_zero :
    ∀ {l : ℕ} [Fact l.Prime] (P : ℤ_[l][X]), P.Monic → IsUnit (P.coeff 0) → ∀ x : Bcr l, aeval ((PP l).φB.toLinearMap : Module.End ℚ_[l] (Bcr l)) (P.map (algebraMap ℤ_[l] ℚ_[l])) x = 0 → (∀ i : ℕ, (PP l).ιB (((PP l).φB)^[i] x) ∈ ((PP l).PD (botExt l)).Fil 0) → ∀ g ∈ Iq l, (PP l).actQ g x = x := by
  intro l _ P hP h0 x hx hF g hg
  classical
  rcases Nat.eq_zero_or_pos P.natDegree with hd | hd
  · rw [hP.natDegree_eq_zero.1 hd, Polynomial.map_one, map_one, Module.End.one_apply] at hx
    rw [hx, map_zero]
  obtain ⟨M, hM, hdiv⟩ := companion P hP h0
  obtain ⟨N, N', hNN, -, hN', hφ, hI⟩ := UpperTheory.exists_algebraic_element_of_algebraicVectorSubspace M hM
  let V : Fin P.natDegree → Bcr l := fun i => ((PP l).φB)^[i] x
  have hpow : ∀ k : ℕ, (((PP l).φB.toLinearMap : Module.End ℚ_[l] (Bcr l)) ^ k) x = ((PP l).φB)^[k] x :=
    fun k => by rw [Module.End.pow_apply]; rfl
  have hV : ∀ i, (PP l).φB (V i) =
      ((M.map (fun z => algebraMap ℚ_[l] (Bcr l) (z : ℚ_[l]))).mulVec V) i := fun i => by
    obtain ⟨Q, hQ⟩ := hdiv i
    have h1 := congrArg (fun p : ℤ_[l][X] => aeval ((PP l).φB.toLinearMap : Module.End ℚ_[l] (Bcr l))
      (p.map (algebraMap ℤ_[l] ℚ_[l])) x) hQ
    rw [mul_comm P Q, Polynomial.map_mul, map_mul, Module.End.mul_apply, hx, map_zero] at h1
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_sum, Polynomial.map_mul, map_X, map_C,
      map_sub, map_sum, map_mul, map_pow, aeval_X, aeval_C, LinearMap.sub_apply, LinearMap.sum_apply,
      Module.End.mul_apply, hpow, Module.algebraMap_end_apply] at h1
    rw [Function.iterate_succ_apply', sub_eq_zero] at h1
    refine h1.trans (Finset.sum_congr rfl fun j _ => ?_)
    rw [Algebra.smul_def]
    rfl
  have hN'N : N' * N = 1 := mul_eq_one_comm.1 hNN
  let Y : Fin P.natDegree → Bcr l := N'.mulVec V
  have hVY : N.mulVec Y = V := by
    simp only [Y, Matrix.mulVec_mulVec, hNN, Matrix.one_mulVec]
  have hφY : ∀ i, (PP l).φB (Y i) = Y i := fun i => by
    have h1 : (PP l).φB (Y i) = ((N'.map (PP l).φB).mulVec ((PP l).φB ∘ V)) i :=
      RingHom.map_mulVec ((PP l).φB : Bcr l →+* Bcr l) N' V i
    have h2 : (PP l).φB ∘ V = (M.map (fun z => algebraMap ℚ_[l] (Bcr l) (z : ℚ_[l]))).mulVec V :=
      funext hV
    have h3 : N'.map (PP l).φB * N.map (PP l).φB = 1 := by
      have := congrArg ((PP l).φB : Bcr l →+* Bcr l).mapMatrix hN'N
      rw [map_mul, map_one] at this
      exact this
    rw [h1, h2, ← hVY, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, ← hφ, h3,
      Matrix.one_mulVec]
  have hYF : ∀ i, (PP l).ιB (Y i) ∈ ((PP l).PD (botExt l)).Fil 0 := fun i => by
    have h1 : Y i = ∑ j, N' i j * V j := rfl
    rw [h1, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [map_mul]
    simpa using ((PP l).PD (botExt l)).Fil_mul 0 0 _ _ (hN' i j) (hF j)
  have hgY : (PP l).actQ g ∘ Y = Y := funext fun i => by
    obtain ⟨c, hc⟩ := ((PP l).PD (botExt l)).fund (Y i) (by rw [(PP l).PD_φ]; exact hφY i)
      (by rw [(PP l).PD_ι]; exact hYF i)
    change (PP l).actQ g (Y i) = Y i
    rw [← hc, AlgEquiv.commutes]
  have h1 : (PP l).actQ g (N.mulVec Y ⟨0, hd⟩) =
      ((N.map ((PP l).actQ g)).mulVec ((PP l).actQ g ∘ Y)) ⟨0, hd⟩ :=
    RingHom.map_mulVec (((PP l).actQ g : Bcr l ≃ₐ[ℚ_[l]] Bcr l) : Bcr l →+* Bcr l) N Y _
  rw [hI g hg, hgY, hVY] at h1
  exact h1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LiftUnramifiedUnipotentCharacter
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc UpperTheory.V.Loc

private theorem ul_exp_two {A : Type} [CommRing A] [Algebra ℚ A] {a : A} (ha : IsNilpotent a) :
    ∃ s, IsNilpotent.exp a = 1 + a + a ^ 2 * s := by
  obtain ⟨k, hk⟩ := ha
  have h2 : a ^ (k + 1 + 1) = 0 := pow_eq_zero_of_le (by omega) hk
  refine ⟨∑ i ∈ Finset.range k, (((i + 1 + 1).factorial : ℚ))⁻¹ • a ^ i, ?_⟩
  rw [IsNilpotent.exp_eq_sum h2, Finset.sum_range_succ', Finset.sum_range_succ', Finset.mul_sum]
  have : ∀ i ∈ Finset.range k, (((i + 1 + 1).factorial : ℚ))⁻¹ • a ^ (i + 1 + 1)
      = a ^ 2 * ((((i + 1 + 1).factorial : ℚ))⁻¹ • a ^ i) := fun i _ => by
    rw [mul_smul_comm]; congr 1; ring
  rw [Finset.sum_congr rfl this]
  simp only [zero_add, Nat.factorial_one, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, pow_one,
    pow_zero]
  ring

private theorem ul_exp_onto {A : Type} [CommRing A] [Algebra ℚ A] {n : A} (hn : IsNilpotent n) :
    ∃ x, IsNilpotent x ∧ IsNilpotent.exp x = 1 + n :=
  _root_.UpperTheory.Reformulated.B.UnipotentExponentialSurjective.ul_exp_onto hn

private theorem t2Space_finite_padic_module {l : ℕ} [Fact l.Prime] {V : Type} [AddCommGroup V] [Module ℚ_[l] V]
    [Module.Finite ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] : T2Space V := by
  haveI : IsTopologicalAddGroup V := IsModuleTopology.topologicalAddGroup ℚ_[l] V
  let e0 := (Module.finBasis ℚ_[l] V).equivFun
  exact T2Space.of_injective_continuous e0.injective
    (IsModuleTopology.continuous_of_linearMap e0.toLinearMap)

theorem UpperTheory.lift_unramified_unipotent_character :
    ∀ {v l : ℕ} [Fact v.Prime] [Fact l.Prime] {B B' : Type} [CommRing B] [CommRing B'] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra ℚ_[l] B'] [Module.Finite ℚ_[l] B'] (p : B →ₐ[ℚ_[l]] B'), Function.Surjective p → (∀ a, p a = 0 → IsNilpotent a) → ∀ u' : GQ v →* B'ˣ, QCont l (fun g => (u' g : B')) → (∀ g ∈ Iq v, u' g = 1) → (∀ g, IsNilpotent ((u' g : B') - 1)) → ∃ u : GQ v →* Bˣ, QCont l (fun g => (u g : B)) ∧ (∀ g ∈ Iq v, u g = 1) ∧ ∀ g, p (u g : B) = (u' g : B') := by
  intro v l _ _ B B' _ _ _ _ _ _ p hp hker u' hc' hI' hn'
  letI : Algebra ℚ B := ((algebraMap ℚ_[l] B).comp (algebraMap ℚ ℚ_[l])).toAlgebra
  letI : Algebra ℚ B' := ((algebraMap ℚ_[l] B').comp (algebraMap ℚ ℚ_[l])).toAlgebra
  letI : TopologicalSpace B := moduleTopology ℚ_[l] B
  letI : TopologicalSpace B' := moduleTopology ℚ_[l] B'
  haveI : IsModuleTopology ℚ_[l] B := ⟨rfl⟩
  haveI : IsModuleTopology ℚ_[l] B' := ⟨rfl⟩
  haveI : IsTopologicalAddGroup B := IsModuleTopology.topologicalAddGroup ℚ_[l] B
  haveI : IsTopologicalAddGroup B' := IsModuleTopology.topologicalAddGroup ℚ_[l] B'
  haveI : ContinuousSMul ℚ_[l] B := IsModuleTopology.toContinuousSMul ℚ_[l] B
  haveI : ContinuousSMul ℚ_[l] B' := IsModuleTopology.toContinuousSMul ℚ_[l] B'
  haveI : T2Space B' := t2Space_finite_padic_module (l := l)
  obtain ⟨σ, hσ⟩ := (iqBasic v).2.2.2.1
  obtain ⟨x', hx', he'⟩ := ul_exp_onto (hn' σ)
  obtain ⟨x, rfl⟩ := hp x'
  have hx : IsNilpotent x := by
    obtain ⟨k, hk⟩ := hx'
    exact (hker (x ^ k) (by rw [map_pow, hk])).of_pow
  obtain ⟨c, ⟨hc, hcI, hcσ⟩, -⟩ := existsUnique_unramified_cocycle_frobenius_value (l := l) (A := ℚ_[l]) (V := ℚ_[l])
    (1 : Representation ℚ_[l] (GQ v) ℚ_[l]) continuous_snd (fun _ _ => rfl) σ hσ 1
  have hadd : ∀ g h, c (g * h) = c g + c h := fun g h => hc.2 g h
  have hcc : Continuous c := hc.1
  have hc1 : c 1 = 0 := hcI 1 (one_mem _)
  let f : GQ v →* B :=
    { toFun := fun g => IsNilpotent.exp (c g • x)
      map_one' := by rw [hc1, zero_smul, IsNilpotent.exp_zero]
      map_mul' := fun g h => by
        rw [hadd, add_smul, IsNilpotent.exp_add_of_commute (Commute.all _ _) (hx.smul _) (hx.smul _)] }
  have hf : Continuous f := by
    obtain ⟨k, hk⟩ := hx
    have : (f : GQ v → B) = fun g => ∑ i ∈ Finset.range k,
        ((((i.factorial : ℚ)⁻¹ : ℚ) : ℚ_[l]) * c g ^ i) • x ^ i := by
      funext g
      change IsNilpotent.exp (c g • x) = _
      rw [IsNilpotent.exp_eq_sum (k := k) (by rw [smul_pow, hk, smul_zero])]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_smul, Rat.cast_smul_eq_qsmul, smul_pow]
    rw [this]
    fun_prop
  have hfI : ∀ g ∈ Iq v, f g = 1 := fun g hg => by
    change IsNilpotent.exp (c g • x) = 1
    rw [hcI g hg, zero_smul, IsNilpotent.exp_zero]
  refine ⟨f.toHomUnits, hf, fun g hg => Units.ext (hfI g hg), fun g => ?_⟩
  let f1 : GQ v →* B' := (p : B →* B').comp f
  let f2 : GQ v →* B' := (Units.coeHom B').comp u'
  have hcl : IsClosed ((f1.eqLocus f2 : Subgroup (GQ v)) : Set (GQ v)) :=
    isClosed_eq ((IsModuleTopology.continuous_of_linearMap p.toLinearMap).comp hf) hc'
  have hle : Iq v ⊔ Subgroup.zpowers σ ≤ f1.eqLocus f2 := by
    refine sup_le (fun k hk => ?_) ((Subgroup.zpowers_le).2 ?_)
    · change p (f k) = (u' k : B')
      rw [hfI k hk, hI' k hk, map_one, Units.val_one]
    · change p (IsNilpotent.exp (c σ • x)) = (u' σ : B')
      rw [hcσ, one_smul, IsNilpotent.map_exp hx, he', add_sub_cancel]
  have := Subgroup.topologicalClosure_minimal _ hle hcl
  rw [frobDense σ hσ] at this
  exact this (Subgroup.mem_top g)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.NormLeOneOfFrobeniusEigenvectorMemFilZero
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology Polynomial

theorem UpperTheory.norm_le_one_of_frobenius_eigenvector_mem_fil_zero :
    ∀ {l : ℕ} [Fact l.Prime] (c : Bcr l) (δ : ℚ_[l]), c ≠ 0 → (PP l).φB c = algebraMap ℚ_[l] (Bcr l) δ * c → (PP l).ιB c ∈ ((PP l).PD (botExt l)).Fil 0 → ‖δ‖ ≤ 1 := by
  intro l _ c δ hc hφ hF
  by_contra hδ
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    simp at hδ
  have hv : δ.valuation < 0 := by
    by_contra h
    exact hδ ((Padic.norm_le_one_iff_val_nonneg δ).2 (not_lt.1 h))
  obtain ⟨a, ha⟩ : ∃ a : ℕ, ((a + 1 : ℕ) : ℤ) = -δ.valuation := ⟨(-δ.valuation - 1).toNat, by push_cast; omega⟩
  have hl : (l : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hu : ‖δ * (l : ℚ_[l]) ^ (a + 1)‖ = 1 := by
    rw [norm_mul, Padic.norm_p_pow, Padic.norm_eq_zpow_neg_valuation hδ0, ← zpow_add₀ hl, ha]
    simp
  let u : ℤ_[l] := ⟨δ * (l : ℚ_[l]) ^ (a + 1), hu.le⟩
  have huu : IsUnit u := PadicInt.isUnit_iff.2 hu
  obtain ⟨N, N', hNN, hN, hN', hφN, -⟩ := UpperTheory.exists_algebraic_element_of_algebraicVectorSubspace (l := l) (n := 1) (Matrix.of fun _ _ => u)
    (by rw [Matrix.det_fin_one]; exact huu)
  set P := PP l with hP
  set D := P.PD (botExt l) with hD
  have h1 : N 0 0 * N' 0 0 = 1 := by
    have := congrFun (congrFun hNN 0) 0
    simpa [Matrix.mul_apply] using this
  have h2 : P.φB (N 0 0) = algebraMap ℚ_[l] (Bcr l) (δ * (l : ℚ_[l]) ^ (a + 1)) * N 0 0 := by
    have := congrFun (congrFun hφN 0) 0
    rw [Matrix.mul_apply, Fin.sum_univ_one] at this
    exact this
  set w := N 0 0
  set w' := N' 0 0 with hw'
  have h3 : algebraMap ℚ_[l] (Bcr l) (δ * (l : ℚ_[l]) ^ (a + 1)) * P.φB w' = w' := by
    have h := congrArg P.φB h1
    rw [map_mul, map_one, h2] at h
    linear_combination w' * h - (algebraMap ℚ_[l] (Bcr l) (δ * (l : ℚ_[l]) ^ (a + 1)) * P.φB w') * h1
  have ht : P.φB D.t = algebraMap ℚ_[l] (Bcr l) (l : ℚ_[l]) * D.t := by
    have := D.t_φ
    rw [P.PD_φ, P.PD_p, Algebra.smul_def] at this
    exact this
  have hb : D.φ (c * D.t ^ (a + 1) * w') = c * D.t ^ (a + 1) * w' := by
    rw [P.PD_φ, map_mul, map_mul, map_pow, hφ, ht, mul_pow]
    rw [map_mul, map_pow] at h3
    linear_combination (c * D.t ^ (a + 1)) * h3
  have ht0 : D.ι D.t ∈ D.Fil 0 := D.Fil_anti 0 D.mem_filtration_one
  have htp : ∀ n : ℕ, D.ι (D.t ^ n) ∈ D.Fil 0 := by
    intro n
    induction n with
    | zero => rw [pow_zero, map_one]; exact D.one_mem
    | succ n ih => rw [pow_succ, map_mul]; exact D.Fil_mul 0 0 _ _ ih ht0
  have hF1 : D.ι (c * D.t ^ (a + 1) * w') ∈ D.Fil 1 := by
    rw [map_mul, map_mul, pow_succ, map_mul]
    have e1 : D.ι c ∈ D.Fil 0 := by rw [P.PD_ι]; exact hF
    have e2 : D.ι w' ∈ D.Fil 0 := by rw [P.PD_ι]; exact hN' 0 0
    exact D.Fil_mul 1 0 _ _ (D.Fil_mul 0 1 _ _ e1 (D.Fil_mul 0 1 _ _ (htp a) D.mem_filtration_one)) e2
  obtain ⟨r, hr⟩ := D.fund _ hb (D.Fil_anti 0 hF1)
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [map_zero] at hr
    have hw : IsUnit w' := IsUnit.of_mul_eq_one w (by rw [mul_comm]; exact h1)
    rw [eq_comm, hw.mul_left_eq_zero, (D.t_unit.pow _).mul_left_eq_zero] at hr
    exact hc hr
  have hone : (1 : P.R.BdR) ∈ D.Fil 1 := by
    rw [← hr, P.PD_ι, AlgHom.commutes] at hF1
    have := (D.Fil 1).smul_mem (algebraMap ℚ_[l] ↥(botExt l).1 r⁻¹) hF1
    rwa [algebraMap_smul, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hr0, map_one] at this
  have := D.Fil_mul 1 1 _ _ D.mem_filtration_one hone
  rw [mul_one] at this
  exact D.not_mem_filtration_two this
end

