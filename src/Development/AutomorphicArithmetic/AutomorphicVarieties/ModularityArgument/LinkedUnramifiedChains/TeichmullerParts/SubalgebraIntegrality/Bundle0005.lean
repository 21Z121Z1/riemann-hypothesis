import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.UnramifiedTrivialInertialType
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0038
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0009
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0004
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0007
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0056
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0059
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0055
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0057
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0054
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0060
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0053
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0732
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0678
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1357
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1399
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0724
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0311
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0012
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.UpOperatorEigenvalues.EigChar

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.PiRepTprod
section
open UpperTheory.V.Z.J.D
open scoped TensorProduct

section Transfer

variable {G G' W W' : Type} [Group G] [Group G'] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

private lemma irr_iff (ρ : Representation ℂ G W) :
    ρ.IsIrreducible ↔ Nontrivial W ∧
      ∀ N : Submodule ℂ W, (∀ g, ∀ v ∈ N, ρ g v ∈ N) → N = ⊥ ∨ N = ⊤ :=
  _root_.UpperTheory.Reformulated.B.Ra6.irr_iff ρ

private lemma transfer (ρ : Representation ℂ G W) (ρ' : Representation ℂ G' W') (φ : G' → G)
    (hφ : Function.Surjective φ) (e : W' ≃ₗ[ℂ] W)
    (h : ∀ g x, e (ρ' g x) = ρ (φ g) (e x)) (hρ : AbsIrr ρ) : AbsIrr ρ' := by
  obtain ⟨h1, h2⟩ := hρ
  obtain ⟨hW, hN⟩ := (irr_iff ρ).1 h1
  refine ⟨(irr_iff ρ').2 ⟨e.toEquiv.nontrivial, fun N hN' => ?_⟩, fun f hf => ?_⟩
  · have hinv : ∀ g, ∀ v ∈ N.map e.toLinearMap, ρ g v ∈ N.map e.toLinearMap := by
      rintro g _ ⟨x, hx, rfl⟩
      obtain ⟨g', rfl⟩ := hφ g
      exact ⟨ρ' g' x, hN' g' x hx, h g' x⟩
    rcases hN _ hinv with h3 | h3
    · left
      rw [Submodule.eq_bot_iff]
      intro x hx
      have hm : e.toLinearMap x ∈ N.map e.toLinearMap := Submodule.mem_map_of_mem hx
      rw [h3, Submodule.mem_bot] at hm
      exact e.map_eq_zero_iff.1 hm
    · right
      rw [Submodule.eq_top_iff']
      intro x
      have hm : e.toLinearMap x ∈ N.map e.toLinearMap := by rw [h3]; exact Submodule.mem_top
      obtain ⟨y, hy, hyx⟩ := hm
      rwa [← e.injective hyx]
  · have hs : ∀ g' v, e.symm (ρ (φ g') v) = ρ' g' (e.symm v) := fun g' v => by
      rw [LinearEquiv.symm_apply_eq, h g' (e.symm v), LinearEquiv.apply_symm_apply]
    have hF : Intw ρ ρ (e.toLinearMap ∘ₗ f ∘ₗ e.symm.toLinearMap) := by
      intro g v
      obtain ⟨g', rfl⟩ := hφ g
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [hs, hf, h]
    obtain ⟨a, ha⟩ := h2 _ hF
    refine ⟨a, LinearMap.ext fun x => e.injective ?_⟩
    have := LinearMap.congr_fun ha (e x)
    simpa using this

private lemma pt_eq {ι Z : Type} {s : ι → Type} [∀ i, AddCommGroup (s i)] [∀ i, Module ℂ (s i)]
    [AddCommGroup Z] [Module ℂ Z] (A B : (⨂[ℂ] i, s i) →ₗ[ℂ] Z)
    (h : ∀ m, A (PiTensorProduct.tprod ℂ m) = B (PiTensorProduct.tprod ℂ m)) (x : ⨂[ℂ] i, s i) :
    A x = B x :=
  LinearMap.congr_fun (PiTensorProduct.ext (MultilinearMap.ext h)) x

end Transfer

private lemma piRep_tprod {I : Type} {Gi Wi : I → Type} [∀ i, Group (Gi i)]
    [∀ i, AddCommGroup (Wi i)] [∀ i, Module ℂ (Wi i)]
    (τ : ∀ i, Representation ℂ (Gi i) (Wi i)) (g : ∀ i, Gi i) (m : ∀ i, Wi i) :
    piRep τ g (PiTensorProduct.tprod ℂ m) = PiTensorProduct.tprod ℂ fun i => τ i (g i) (m i) :=
  PiTensorProduct.map_tprod _ _

private def Pp (I : Type) : Prop :=
  ∀ (Gi Wi : I → Type) [∀ i, Group (Gi i)] [∀ i, AddCommGroup (Wi i)] [∀ i, Module ℂ (Wi i)]
    (τ : ∀ i, Representation ℂ (Gi i) (Wi i)), (∀ i, AbsIrr (τ i)) → AbsIrr (piRep τ)

private lemma Pp_equiv {α β : Type} (f : β ≃ α) (h : Pp α) : Pp β := by
  intro Gi Wi _ _ _ τ hτ
  refine transfer (piRep fun a => τ (f.symm a)) (piRep τ) (Equiv.piCongrLeft' Gi f)
    (Equiv.surjective _) (PiTensorProduct.reindex ℂ Wi f) (fun g x => ?_)
    (h (fun a => Gi (f.symm a)) (fun a => Wi (f.symm a)) (fun a => τ (f.symm a)) fun a => hτ _)
  refine pt_eq ((PiTensorProduct.reindex ℂ Wi f).toLinearMap ∘ₗ piRep τ g)
    ((piRep (fun a => τ (f.symm a)) (Equiv.piCongrLeft' Gi f g)) ∘ₗ
      (PiTensorProduct.reindex ℂ Wi f).toLinearMap) (fun m => ?_) x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, piRep_tprod, PiTensorProduct.reindex_tprod]
  rfl

private lemma absIrr_triv : AbsIrr (Representation.trivial ℂ Unit ℂ) := by
  refine ⟨(irr_iff _).2 ⟨inferInstance, fun N _ => eq_bot_or_eq_top N⟩, fun f _ => ⟨f 1, ?_⟩⟩
  refine LinearMap.ext_ring ?_
  simp

private lemma Pp_empty : Pp PEmpty := by
  intro Gi Wi _ _ _ τ _
  refine transfer (Representation.trivial ℂ Unit ℂ) (piRep τ) (fun _ => ()) (fun _ => ⟨1, rfl⟩)
    (PiTensorProduct.isEmptyEquiv PEmpty) (fun g x => ?_) absIrr_triv
  refine pt_eq ((PiTensorProduct.isEmptyEquiv PEmpty).toLinearMap ∘ₗ piRep τ g)
    (Representation.trivial ℂ Unit ℂ () ∘ₗ (PiTensorProduct.isEmptyEquiv PEmpty).toLinearMap)
    (fun m => ?_) x
  simp [piRep_tprod, PiTensorProduct.isEmptyEquiv_apply_tprod]

private lemma Pp_unit : Pp PUnit := by
  intro Gi Wi _ _ _ τ hτ
  refine transfer (τ PUnit.unit) (piRep τ) (fun g => g PUnit.unit) (fun h => ⟨fun _ => h, rfl⟩)
    (PiTensorProduct.subsingletonEquiv PUnit.unit) (fun g x => ?_) (hτ _)
  refine pt_eq ((PiTensorProduct.subsingletonEquiv PUnit.unit).toLinearMap ∘ₗ piRep τ g)
    (τ PUnit.unit (g PUnit.unit) ∘ₗ (PiTensorProduct.subsingletonEquiv PUnit.unit).toLinearMap)
    (fun m => ?_) x
  simp [piRep_tprod, PiTensorProduct.subsingletonEquiv_apply_tprod]

private lemma Pp_sum (hB : BoxIrr) {α β : Type} (ha : Pp α) (hb : Pp β) : Pp (α ⊕ β) := by
  intro Gi Wi _ _ _ τ hτ
  refine transfer (box (piRep fun a => τ (.inl a)) (piRep fun b => τ (.inr b))) (piRep τ)
    (fun g => (fun a => g (.inl a), fun b => g (.inr b)))
    (fun p => ⟨fun s => Sum.rec (motive := Gi) p.1 p.2 s, rfl⟩)
    (PiTensorProduct.tmulEquivDep ℂ Wi).symm (fun g x => ?_)
    (hB _ _ _ _ _ _ (ha _ _ _ fun a => hτ _) (hb _ _ _ fun b => hτ _))
  refine pt_eq ((PiTensorProduct.tmulEquivDep ℂ Wi).symm.toLinearMap ∘ₗ piRep τ g)
    ((box (piRep fun a => τ (.inl a)) (piRep fun b => τ (.inr b))
        (fun a => g (.inl a), fun b => g (.inr b))) ∘ₗ
      (PiTensorProduct.tmulEquivDep ℂ Wi).symm.toLinearMap) (fun m => ?_) x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, piRep_tprod,
    PiTensorProduct.tmulEquivDep_symm_apply]
  simp only [box, Representation.tprod_apply, MonoidHom.comp_apply, TensorProduct.map_tmul]
  simp [piRep_tprod]

theorem UpperTheory.V.Z.J.D.piIrr :
    BoxIrr → PiIrr := by
  intro hB I _ _ Gi Wi _ _ _ τ hτ
  have key : ∀ (α : Type) [Fintype α], Pp α := by
    refine Fintype.induction_empty_option (P := fun α _ => Pp α) ?_ Pp_empty ?_
    · intro α β _ e h
      exact Pp_equiv e.symm h
    · intro α _ h
      exact Pp_equiv (Equiv.optionEquivSumPUnit α) (Pp_sum hB h Pp_unit)
  exact key I Gi Wi τ hτ
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.SpehInfRankOneEq
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
open UpperTheory.V.Af.Gu UpperTheory.V.Z.J.D GlobalTheory.DefiniteBC GlobalTheory.SmGL
open UpperTheory.V.Z.Mult (Cp At)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem ss_irr {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r : Γ →* GL (Fin n) k} (h : IsIrr r) : IsSSRep r := fun M hM => by
  rcases h.2.2 M le_top hM with rfl | rfl
  · exact ⟨⊤, h.2.1, isCompl_bot_top⟩
  · refine ⟨⊥, fun g v hv => ?_, isCompl_top_bot⟩
    rw [(Submodule.mem_bot k).1 hv]
    simp

private theorem irr_conj {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r r' : Γ →* GL (Fin n) k} (e : RepIso r r') (h : IsIrr r) :
    IsIrr r' := by
  obtain ⟨P, hP⟩ := e
  refine ⟨h.1, fun _ _ _ => Submodule.mem_top, fun M _ hM => ?_⟩
  let T : (Fin n → k) ≃ₗ[k] (Fin n → k) := (Matrix.GeneralLinearGroup.toLin P).toLinearEquiv
  have hT : ∀ v, T v = (P : Matrix (Fin n) (Fin n) k).mulVec v := fun v => rfl
  have hi : Formalism.MainNotions.N.IsInv r (M.comap (T : (Fin n → k) →ₗ[k] (Fin n → k))) := fun g v hv => by
    have h1 := hM g _ hv
    have h2 : T ((r g : Matrix (Fin n) (Fin n) k).mulVec v) = (r' g : Matrix (Fin n) (Fin n) k).mulVec (T v) := by
      rw [hT, hT, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hP g]
      simp [Matrix.mul_assoc]
    show T _ ∈ M
    rw [h2]
    exact h1
  rcases h.2.2 _ le_top hi with h0 | h0
  · left
    refine (Submodule.eq_bot_iff _).2 fun v hv => ?_
    have h1 : T.symm v ∈ M.comap (T : (Fin n → k) →ₗ[k] (Fin n → k)) := by simpa using hv
    rw [h0] at h1
    simpa using (Submodule.mem_bot k).1 h1
  · right
    refine (Submodule.eq_top_iff').2 fun v => ?_
    have h1 : T.symm v ∈ M.comap (T : (Fin n → k) →ₗ[k] (Fin n → k)) := by rw [h0]; trivial
    simpa using h1

private theorem iso_split {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (hE : ∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal)
    {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {n : ℕ} (r r' : G E Ω →* GL (Fin n) (Qbar l)) (hr : Continuous r) (hr' : Continuous r')
    (hs : IsSSRep r) (hs' : IsSSRep r')
    (hw : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, IsSplitAt w → ∃ B, FrobEig ι r w B ∧ FrobEig ι r' w B) : RepIso r r' := by
  have hc : ∀ g : G E Ω, (r g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly =
      (r' g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly := by
    intro g
    ext i
    have h1 : Continuous fun g : G E Ω => (r g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i :=
      (GlobalTheory.LocBound.continuous_coeff_charpoly n i).comp (Units.continuous_val.comp (hr.comp continuous_inv))
    have h2 : Continuous fun g : G E Ω => (r' g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i :=
      (GlobalTheory.LocBound.continuous_coeff_charpoly n i).comp (Units.continuous_val.comp (hr'.comp continuous_inv))
    refine congrFun (GlobalTheory.Published.chebotarevDegreeOne'.eq_of_frob (Filter.eventually_cofinite.1 hw) h1 h2 ?_) g
    intro v hv hd A hA σ hσ
    obtain ⟨B, hB, hB'⟩ := (not_not.1 hv) (UpperTheory.isSplitAt_of_unramified_of_inertiaDeg_eq_one E v (hE v) hd)
    have h := ((hB A hA).2 σ hσ).trans ((hB' A hA).2 σ hσ).symm
    have h' := Polynomial.map_injective ι.toRingHom ι.injective h
    simp only [h']
  obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix r r' hs hs' (fun g => by simpa using hc g⁻¹)
  exact ⟨P⁻¹, fun s => by rw [hP s, inv_inv]⟩

private theorem speh_inf_rank_one_eq (m : Multiset ℂ) : GlobalTheory.DefiniteBC.spehInf 1 m = m := by
  simp [GlobalTheory.DefiniteBC.spehInf]

private theorem ev_away {K : Type} [Field K] [NumberField K] (l : ℕ) [Fact l.Prime] :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ((l : ℕ) : 𝓞 K) ∉ v.asIdeal := by
  have h0 : Ideal.span {((l : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)

private theorem onePart (H : HypothesesH) (hLink : SatLink) {E : Type} [Field E] [NumberField E] [IsCMField E]
    (hE : ∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal)
    {n : ℕ} (hn : 1 ≤ n) (σ : Submodule ℂ (UA E n → ℂ)) (hσ : IsAutRepU σ) (hsum : ∑ _i : Fin 1, 1 * n = n)
    (P : Fin 1 → CuspSub E n) (ρ : Fin 1 → ∀ w : HeightOneSpectrum (𝓞 E), LocIrr w n)
    (m : Fin 1 → (E →+* ℂ) → Multiset ℂ) (τs : Fin 1 → ∀ w : HeightOneSpectrum (𝓞 E), LocIrr w (1 * n))
    (hP : GlobalTheory.BcSpeh.Parts σ (fun _ => n) (fun _ => 1) hsum P ρ m)
    (hS : ∀ i w, GlobalTheory.SmGL.IsUnitarisable (ρ i w).ρ ∧ GlobalTheory.SmGL.IsUnitarisable (τs i w).ρ ∧
      GlobalTheory.LocGL.IsSpeh (GlobalTheory.LocGL.IrrGL.of (ρ i w).ρ (ρ i w).smooth (ρ i w).irred) 1 (τs i w).ρ)
    (hsplit : ∀ w, IsSplitAt w → IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) (locProd hsum w (τs · w))) :
    ∃ π : CuspSub E n, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧ At π σ ∧
      (∀ φ lam, HasWeightAt σ φ lam → π.HasInfChar φ (infOfWeight lam)) ∧ ∀ w, IsUnramU σ w → ∃ B, (CG.mk π).HasSat w B := by
  have hw : ∀ φ lam, HasWeightAt σ φ lam → (P 0).HasInfChar φ (infOfWeight lam) := fun φ lam h => by
    have e := hP.weight φ lam h
    rw [Fin.sum_univ_one, speh_inf_rank_one_eq] at e
    exact e ▸ hP.inf 0 φ
  refine ⟨P 0, (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => ?_, GlobalTheory.LocGlobDual.Model.dualIsConj_of_isCsd (H.toClassicalTheorems.litN.aut.gk E _ (P 0)) (hP.csd 0), ?_, hw, fun w hu => ?_⟩
  · obtain ⟨lam, hl⟩ := GlobalTheory.T.exists_algebraicWeight_of_automorphic_definiteUnitary E _ hn σ hσ τ
    rw [CG.HasInfChar.infChar_eq (π := CG.mk (P 0)) (hw τ lam hl)]
    refine ⟨nodup_infOfWeight lam, fun z hz => ?_⟩
    rw [infOfWeight, Multiset.mem_map] at hz
    obtain ⟨j, -, rfl⟩ := hz
    exact ⟨lam.w j - (j : ℕ), by push_cast; ring⟩
  · filter_upwards [(hLink E _ (P 0)).2] with w ⟨B, hB⟩ hs
    have e : (fun i => τs i w) = fun _ => τs 0 w := funext fun i => by rw [Subsingleton.elim i 0]
    have key : ∀ f : Fin 1 → LocIrr w (1 * n), f = (fun _ => τs 0 w) →
        IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) (locProd hsum w f) →
        IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) (locProd hsum w fun _ => τs 0 w) := by
      rintro f rfl h
      exact h
    have hc := key _ e (hsplit w hs)
    exact ⟨ρ 0 w, B, UpperTheory.V.Z.Desc.irrComp E n σ hsum (P 0) w (ρ 0 w) (τs 0 w) (hP.loc 0 w) (hS 0 w).2.2 hc (ρ 0 w) (hP.loc 0 w),
      ((hLink E _ (P 0)).1 w _ (hP.loc 0 w) _).1 hB, hB⟩
  · obtain ⟨x, hx, h0⟩ := (Submodule.ne_bot_iff _).1
      (GlobalTheory.SphBC.isSpherical_of_isUnramU E hE n σ hσ 1 _ _ hsum P ρ m τs hP hS hsplit w hu 0 (ρ 0 w) (hP.loc 0 w))
    obtain ⟨B, hB⟩ := (satLoc H.toClassicalTheorems E n w (ρ 0 w)).1 ⟨x, h0, GlobalTheory.LGrp.mem_fixed.1 hx⟩
    exact ⟨B, ((hLink E _ (P 0)).1 w _ (hP.loc 0 w) _).2 hB⟩

private theorem assemble (H : HypothesesH) (hB : GlobalTheory.BcSpeh.BcSpeh) (hFam : SumFam) (hHalf : Half) (hStr : Strings) (hUni : CompUnique)
    (hRec : RecTot) (hFrob : FrobTot) (hLink : SatLink) : BcOf := by
  intro _ E Ω _ _ _ _ _ _ hE l _ _ ι n hn π hπ R hRc hRi hR
  obtain ⟨c, a, d, hsum, P, ρ, m, σ, hP, hS, hsplit⟩ := hB E hE n hn π hπ
  have hc : 1 ≤ c := by
    rcases c with _ | c
    · simp at hsum; omega
    · omega
  have hint : ∀ i (k : Fin (d i)) τ, (m i τ).Nodup ∧ ∀ z ∈ m i τ, ∃ j : ℤ, z + (ex n (d i) k : ℂ) / 2 = j := fun i k τ => by
    obtain ⟨lam, hl⟩ := GlobalTheory.T.exists_algebraicWeight_of_automorphic_definiteUnitary E n hn π hπ τ
    exact (hStr n c d (m · τ) lam (hP.weight τ lam hl)).1 i k
  choose r₀ HT₀ h₀ hw₀ using fun i (k : Fin (d i)) =>
    hHalf E Ω l ι (a i) (hP.pos i).1 (P i) (hP.csd i) (ρ i) (hP.loc i) (m i) (hP.inf i) (ex n (d i) k) (hint i k)
  choose r₁ h₁ hi₁ using fun i => hFam E Ω l ι (d i) (hP.pos i).2 (fun _ => a i) (fun _ => (hP.pos i).1) (d i * a i) (by simp)
    (r₀ i) _ (HT₀ i) (h₀ i)
  obtain ⟨r, hr, hi⟩ := hFam E Ω l ι c hc (fun i => d i * a i) (fun i => Nat.mul_pos (hP.pos i).2 (hP.pos i).1) n hsum r₁ _ _ h₁
  have hpar : ∀ w, ParAt ι r w (totPar n d (ρ · w)) := hr.par
  have hev : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ((l : ℕ) : 𝓞 E) ∉ w.asIdeal ∧
      ∃ S : Fin c → Multiset ℂˣ, ∀ i, (CG.mk (P i)).HasSat w (S i) := by
    filter_upwards [ev_away (K := E) l, Filter.eventually_all.2 fun i => (hLink E _ (P i)).2] with w h1 h2
    exact ⟨h1, Classical.skolem.1 h2⟩
  have hRp : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, IsSplitAt w → ParAt ι R w (totPar n d (ρ · w)) := by
    filter_upwards [hR] with w hw hs
    let T : SmIrr (GL (Fin n) (w.adicCompletion E)) :=
      { V := _, ρ := locProd hsum w (σ · w), smooth := GlobalTheory.SmGL.isSmooth_parInd _ _, irred := (hsplit w hs).1 }
    exact ((locGlob_iff ι R w T).1 (hw hs T (hsplit w hs))).congr fun A h rc hrc =>
      (hRec E Ω n c a d hsum P w (ρ · w) (σ · w) hP.pos (hP.loc · w) (hS · w) T
        (hUni E n π hπ w hs _ _ _ _ (hsplit w hs) (hsplit w hs)) A h rc hrc).symm
  have hiso : RepIso R r := iso_split hE ι R r hRc hr.cont (ss_irr hRi) hr.ss (by
    filter_upwards [hev, hRp] with w ⟨hw, S, hS'⟩ hp hs
    have hSat : ∀ i, GlobalTheory.LFun.HasSatGL w (ρ i w).ρ (S i) := fun i => ((hLink E _ (P i)).1 w _ (hP.loc i w) _).1 (hS' i)
    exact ⟨_, hFrob E Ω l ι n c a d R hRc w hw (ρ · w) S hSat (hp hs), hFrob E Ω l ι n c a d r hr.cont w hw (ρ · w) S hSat (hpar w)⟩)
  have hirr : IsIrr r := irr_conj hiso hRi
  obtain ⟨hc1, hr1⟩ := hi hirr
  have hd1 : ∀ i, d i = 1 := fun i => (hi₁ i (hr1 i)).1
  clear hi hi₁ h₁ hr hpar hint hev hRp hiso hirr hr1 h₀ hw₀
  subst hc1
  obtain rfl : d = fun _ => 1 := funext hd1
  have ha : a = fun _ => n := funext fun i => by
    rw [Subsingleton.elim i 0]
    simpa using hsum
  subst ha
  exact onePart H hLink hE hn π hπ hsum P ρ m σ hP hS hsplit

theorem UpperTheory.V.Z.J.D.bcOf :
    BcOf := fun H =>
  assemble H (GlobalTheory.BcSpeh.bcSpeh_of_baseChange (GlobalTheory.BaseChangeBridge.main H.litN.aut.bc H.litN.loc.bern)
      (GlobalTheory.SpehInfChar.discreteSpectrumGL_of_residual H.litN.aut.mw))
    (UpperTheory.sum_family_of_reductions (UpperTheory.sum_two_of_hodge_tate H UpperTheory.galoisRep_direct_sum_away_from_places UpperTheory.sum_hodge_tate) UpperTheory.finiteSum_reduction)
    (UpperTheory.half_of_compatible_polarization H UpperTheory.eta_condition UpperTheory.twist_local_components_compatible (UpperTheory.compatible_polarization_of_link H (compatCsd H) (UpperTheory.satake_galois_compatibility_of_hecke_eigensystem H)))
    UpperTheory.speh_parameter_strings UpperTheory.building_component_uniqueness (UpperTheory.total_reciprocity H) (UpperTheory.total_frobenius_compatibility H) (UpperTheory.satake_galois_compatibility_of_hecke_eigensystem H) H
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.UnitEv
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Z.J.D
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option synthInstance.maxHeartbeats 200000

private theorem norm_le_of_isIntegral {l : ℕ} [Fact l.Prime] {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
    (x : B →+* PadicAlgCl l) (h : ∀ a, ‖x (algebraMap A B a)‖ ≤ 1) {t : B} (ht : IsIntegral A t) : ‖x t‖ ≤ 1 := by
  obtain ⟨p, hm, hp⟩ := ht
  let S := integralClosure ℤ_[l] (PadicAlgCl l)
  let g : A →+* S := (x.comp (algebraMap A B)).codRestrict S.toSubring (fun a => by
    show IsIntegral ℤ_[l] (x (algebraMap A B a))
    exact (UpperTheory.V.Hi.Up.intIff _).2 (h a))
  have hint : IsIntegral S (x t) := by
    refine ⟨p.map g, hm.map g, ?_⟩
    rw [Polynomial.eval₂_map]
    have hc : (algebraMap S (PadicAlgCl l)).comp g = x.comp (algebraMap A B) := by
      ext a
      rfl
    rw [hc, ← Polynomial.hom_eval₂, hp, map_zero]
  exact (UpperTheory.V.Hi.Up.intIff _).1 (isIntegral_trans (R := ℤ_[l]) _ hint)

private theorem isIntegral_of_subalgebra {A Y : Type} [CommRing A] [AddCommGroup Y] [Module A Y] [Module.Finite A Y]
    (T : Subalgebra A (Module.End A Y)) (t : T) : IsIntegral A t := by
  have h : IsIntegral A (t : Module.End A Y) := by
    obtain ⟨p, hp, he⟩ := LinearMap.exists_monic_and_aeval_eq_zero A (t : Module.End A Y)
    exact ⟨p, hp, by rwa [← Polynomial.aeval_def]⟩
  exact (isIntegral_algHom_iff T.val Subtype.val_injective).1 h

private theorem norm_unit {l : ℕ} [Fact l.Prime] {B : Type} [CommRing B] (x : B →+* PadicAlgCl l) (u : Bˣ)
    (h : ∀ t, ‖x t‖ ≤ 1) : ‖x u‖ = 1 := by
  have e : ‖x u‖ * ‖x (u⁻¹ : Bˣ)‖ = 1 := by
    rw [← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]
  refine le_antisymm (h _) ?_
  calc (1 : ℝ) = ‖x u‖ * ‖x (u⁻¹ : Bˣ)‖ := e.symm
    _ ≤ ‖x u‖ * 1 := mul_le_mul_of_nonneg_left (h _) (norm_nonneg _)
    _ = ‖x u‖ := mul_one _

theorem UpperTheory.V.Z.J.D.unitEv :
    UnitEv := by
  intro L Ω _ _ _ _ _ l _ n c H hAx A _ _ _ θ _ ι K a _ _ I D ψ hU z v j
  obtain ⟨s, hs⟩ := GlobalTheory.LocLanglands.IsLocalArtin.surj (hAx.art_spec v)
    (UpperTheory.V.Hi.unif (IsDedekindDomain.HeightOneSpectrum.adicCompletion L (H.Sl v)))
  let g : Dec (H.pl v) := ⟨s, GlobalTheory.WeilDeligne.Weil_le_Dec (H.ovr v) s.2⟩
  rw [← hU.ψ_unif v j s g rfl hs]
  apply norm_unit z.toRingHom
  intro t
  refine norm_le_of_isIntegral (A := A) z.toRingHom ?_ (isIntegral_of_subalgebra _ t)
  intro a0
  let y : A →ₐ[c.O] PadicAlgCl l := z.comp (IsScalarTower.toAlgHom c.O A (H.TK θ a K))
  show ‖y a0‖ ≤ 1
  obtain ⟨b, hb⟩ := UpperTheory.V.Alg.IsCO.res_surj (O := c.O) a0
  have hm := UpperTheory.V.Hi.Up.normLt (l := l) (O := c.O) y _ hb
  have hi1 : IsIntegral ℤ_[l] (y (a0 - algebraMap c.O A b)) :=
    (UpperTheory.V.Hi.Up.intIff _).2 hm.le
  have hbi : IsIntegral ℤ_[l] b := by
    haveI := c.fin
    exact IsIntegral.of_finite ℤ_[l] b
  have hi2 : IsIntegral ℤ_[l] (y (algebraMap c.O A b)) := by
    rw [AlgHom.commutes]
    exact (isIntegral_algHom_iff c.O.val Subtype.val_injective).2 hbi
  have := hi1.add hi2
  rw [← map_add, sub_add_cancel] at this
  exact (UpperTheory.V.Hi.Up.intIff _).1 this
end

