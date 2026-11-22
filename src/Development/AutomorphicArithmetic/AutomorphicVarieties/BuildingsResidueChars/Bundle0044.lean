import Mathlib
import Development.AutomorphicArithmetic.DivisorFrames.Bundle0004
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0359
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0039
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AutTranslate
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CuspidalFiniteness.TypePoly
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0071
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0223
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0226
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0041
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0043
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0038
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedIsCrysAndJumpEqZero

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AdmissibleEquivariantFormsRepresentation
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.DefU

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {S : Type} [AddCommGroup S] [Module ℂ S]

private def eqForms (ρ : Representation ℂ (infU E n) S) : Submodule ℂ (S →ₗ[ℂ] (UA E n → ℂ)) where
  carrier := {f | (∀ v, f v ∈ autU E n) ∧ ∀ (x : infU E n) v, f (ρ x v) = RU E n x (f v)}
  add_mem' ha hb := ⟨fun v => add_mem (ha.1 v) (hb.1 v), fun x v => by
    rw [LinearMap.add_apply, LinearMap.add_apply, ha.2, hb.2, map_add]⟩
  zero_mem' := ⟨fun _ => zero_mem _, fun _ _ => rfl⟩
  smul_mem' c _ ha := ⟨fun v => Submodule.smul_mem _ c (ha.1 v), fun x v => by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, ha.2, map_smul]⟩

private noncomputable def eqRep (ρ : Representation ℂ (infU E n) S) : Representation ℂ (finU E n) (eqForms ρ) where
  toFun k := (LinearMap.llcomp ℂ _ _ _ (RU E n k)).restrict (p := eqForms ρ) (q := eqForms ρ) fun f h =>
    ⟨fun v => RU_mem_autU _ _ (h.1 v), fun x v => by
      change RU E n k (f (ρ x v)) = RU E n x (RU E n k (f v))
      rw [h.2, RU_RU, RU_RU, fin_mul_inf k.2 x.2]⟩
  map_one' := LinearMap.ext fun f => Subtype.ext (LinearMap.ext fun v => funext fun g => congrArg (f.1 v) (mul_one g))
  map_mul' a b := LinearMap.ext fun f => Subtype.ext (LinearMap.ext fun v => funext fun g =>
    congrArg (f.1 v) (mul_assoc g a b).symm)

private theorem eqRep_adm [FiniteDimensional ℂ S] (ρ : Representation ℂ (infU E n) S) (f : eqForms ρ) :
    ∃ K : Subgroup (finU E n), (∀ k ∈ K, eqRep ρ k f = f) ∧ FiniteDimensional ℂ (GlobalTheory.PRep.fixed (eqRep ρ) K) ∧
      ∀ w, (Set.range fun k : K => eqRep ρ k w).Finite :=
  _root_.UpperTheory.Reformulated.B.Gr38.eqRep_adm ρ f

end

theorem UpperTheory.admissible_equivariantForms_representation :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (B : (UA E n → ℂ) →ₗ⋆[ℂ] (UA E n → ℂ) →ₗ[ℂ] ℂ), (∀ φ, IsAutFormU φ → B φ φ = 0 → φ = 0) → (∀ x φ ψ, IsAutFormU φ → IsAutFormU ψ → B (RU E n x φ) (RU E n x ψ) = B φ ψ) → ∀ (S : Type) [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S] (ρ : Representation ℂ (infU E n) S), Submodule.span ℂ (Set.range ρ) = ⊤ → ∀ f : S →ₗ[ℂ] (UA E n → ℂ), (∀ v, IsAutFormU (f v)) → (∀ (x : infU E n) v, f (ρ x v) = RU E n x (f v)) → ∀ v, f v ∈ ⨆ σ : {σ : Submodule ℂ (UA E n → ℂ) // IsAutRepU σ}, σ.1 := by
  intro E _ _ _ n B hdefB hinv S _ _ _ ρ hsp f hfa hfe v
  classical
  by_cases hv : v = 0
  · rw [hv, map_zero]
    exact zero_mem _
  let ev : eqForms ρ →ₗ[ℂ] (UA E n → ℂ) := LinearMap.applyₗ v ∘ₗ (eqForms ρ).subtype
  let B' : eqForms ρ →ₗ⋆[ℂ] eqForms ρ →ₗ[ℂ] ℂ := (B.compl₂ ev).comp ev
  have hB' : ∀ u w, B' u w = B (u.1 v) (w.1 v) := fun _ _ => rfl
  have hev : ∀ u : eqForms ρ, u.1 v = 0 → u = 0 := fun u hu => by
    have h1 : ∀ T ∈ Submodule.span ℂ (Set.range ρ), u.1 (T v) = 0 := by
      intro T hT
      induction hT using Submodule.span_induction with
      | mem T hT =>
        obtain ⟨x, rfl⟩ := hT
        rw [u.2.2, hu, map_zero]
      | zero => simp
      | add a b _ _ ha hb => rw [LinearMap.add_apply, map_add, ha, hb, add_zero]
      | smul c a _ ha => rw [LinearMap.smul_apply, map_smul, ha, smul_zero]
    obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one ℂ hv
    refine Subtype.ext (LinearMap.ext fun w => ?_)
    have h2 := h1 (LinearMap.smulRight l w) (hsp ▸ Submodule.mem_top)
    rw [LinearMap.smulRight_apply, hl, one_smul] at h2
    exact h2
  have hdef : ∀ u, B' u u = 0 → u = 0 := fun u hu => hev u (hdefB _ (u.2.1 v) hu)
  have hinv' : ∀ g u w, B' (eqRep ρ g u) (eqRep ρ g w) = B' u w := fun g u w =>
    hinv g _ _ (u.2.1 _) (w.2.1 _)
  have hmem := UpperTheory.mem_iSup_irreducible_of_admissible_unitary (finU E n) (eqForms ρ) (eqRep ρ) B' hdef hinv' (eqRep_adm ρ) ⟨f, hfa, hfe⟩
  refine (iSup_le ?_ : _ ≤ (⨆ σ : {σ : Submodule ℂ (UA E n → ℂ) // IsAutRepU σ}, σ.1).comap ev) hmem
  rintro ⟨U, hU0, hU, hirr⟩
  let j : U →ₗ[ℂ] S →ₗ[ℂ] (UA E n → ℂ) := (eqForms ρ).subtype ∘ₗ U.subtype
  have hj : ∀ (p : U) (x : infU E n) v, j p (ρ x v) = RU E n x.1 (j p v) := fun p x v => p.1.2.2 x v
  have hrep : IsAutRepU (Pairs.img j) := by
    refine ⟨fun φ hφ => ?_, fun x φ hφ => ?_, fun h => hU0 ?_, fun N hle hN => ?_⟩
    · have h1 : Pairs.img j ≤ autU E n := Submodule.span_le.2 (by
        rintro _ ⟨p, v, rfl⟩
        exact p.1.2.1 v)
      exact h1 hφ
    · refine Pairs.stable_of (fun a => ?_) (fun k => ?_) x φ hφ
      · have h1 : Pairs.img j ≤ (Pairs.img j).comap (RU E n a.1) := Submodule.span_le.2 (by
          rintro _ ⟨p, v, rfl⟩
          change RU E n a.1 _ ∈ Pairs.img j
          rw [← hj]
          exact Pairs.apply_mem_img _ _ _)
        exact fun φ hφ => h1 hφ
      · have h1 : Pairs.img j ≤ (Pairs.img j).comap (RU E n k.1) := Submodule.span_le.2 (by
          rintro _ ⟨p, v, rfl⟩
          exact Pairs.apply_mem_img j ⟨eqRep ρ k p.1, hU k _ p.2⟩ v)
        exact fun φ hφ => h1 hφ
    · rw [Submodule.eq_bot_iff]
      intro u hu
      have := Pairs.apply_mem_img j ⟨u, hu⟩ v
      rw [h, Submodule.mem_bot] at this
      exact hev u this
    · refine Pairs.eq_bot_or_eq_img hsp (R := fun x => RU E n x.1) hj
        (Q := fun k : finU E n => (eqRep ρ k).restrict (hU k)) (T := fun k => RU E n k.1) (fun _ _ _ => rfl)
        (fun P hP => ?_) hle (fun x => hN x.1) (fun k => hN k.1)
      rcases hirr (P.map U.subtype) (Submodule.map_subtype_le U P) (by
        rintro g _ ⟨p, hp, rfl⟩
        exact ⟨_, hP g p hp, rfl⟩) with h | h
      · left
        exact Submodule.map_injective_of_injective U.injective_subtype (h.trans (Submodule.map_bot _).symm)
      · right
        exact Submodule.map_injective_of_injective U.injective_subtype (h.trans (Submodule.map_subtype_top _).symm)
  intro u hu
  exact le_iSup (fun σ : {σ : Submodule ℂ (UA E n → ℂ) // IsAutRepU σ} => σ.1) ⟨_, hrep⟩
    (Pairs.apply_mem_img j ⟨u, hu⟩ v)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AlgModBotCompactCasimirOfTypes
section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private noncomputable def slc {K : Type} [Field K] [NumberField K] {n : ℕ} (g : AdelicGLn.AdelicGL K n) :
    archSmooth K n →ₗ[ℂ] (archCompact K n → ℂ) where
  toFun φ k := φ.1 (g * infEmb K n k.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem slc_op {K : Type} [Field K] [NumberField K] {n : ℕ} (X : (isExpLieAlgebra K n).lieSubalgebra)
    (hX : ∀ t : ℝ, (isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie X) ∈ archCompact K n) :
    (∃ D : Module.End ℂ (archCompact K n → ℂ), ∀ g φ,
      D (slc g φ) = slc g (uAction (UniversalEnvelopingAlgebra.ι ℝ X) φ)) ∧
    ∀ (V : Submodule ℂ (archCompact K n → ℂ)), FiniteDimensional ℂ V → (∀ f ∈ V, ∀ k', (fun k => f (k * k')) ∈ V) →
      ∀ g φ, slc g φ ∈ V → slc g (uAction (UniversalEnvelopingAlgebra.ι ℝ X) φ) ∈ V := by
  let γ : ℝ → archCompact K n := fun t =>
    ⟨(isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie X), hX t⟩
  have F : ∀ (g : AdelicGLn.AdelicGL K n) (φ : archSmooth K n) (k : archCompact K n),
      HasDerivAt (fun t => slc g φ (k * γ t)) (slc g (uAction (UniversalEnvelopingAlgebra.ι ℝ X) φ) k) 0 := by
    intro g φ k
    have d := (isExpLieAlgebra K n).hasDerivAt_rightDeriv
      ((show IsArchSmooth φ.1 from φ.2) (g * infEmb K n k.1)) ((isExpLieAlgebra K n).ofLie X) 1
    show HasDerivAt _ ((uAction (UniversalEnvelopingAlgebra.ι ℝ X) φ).1 (g * infEmb K n k.1)) 0
    rw [uAction_ι_apply]
    have e : (fun t => slc g φ (k * γ t)) = fun t => archSlice φ.1 (g * infEmb K n k.1)
        (1 * (isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie X)) := by
      funext t
      simp only [slc, LinearMap.coe_mk, AddHom.coe_mk, archSlice_apply, one_mul, Subgroup.coe_mul, map_mul,
        mul_assoc]
      rfl
    rw [e]
    exact d
  let P : Submodule ℂ (archCompact K n → ℂ) :=
    { carrier := {f | ∀ k, DifferentiableAt ℝ (fun t => f (k * γ t)) 0}
      add_mem' := fun ha hb k => (ha k).add (hb k)
      zero_mem' := fun _ => differentiableAt_const _
      smul_mem' := fun c _ hf k => (hf k).const_smul c }
  let D₀ : P →ₗ[ℂ] (archCompact K n → ℂ) :=
    { toFun := fun f k => deriv (fun t => f.1 (k * γ t)) 0
      map_add' := fun f h => by
        funext k
        show deriv (fun t => f.1 (k * γ t) + h.1 (k * γ t)) 0 = _
        exact deriv_add (f.2 k) (h.2 k)
      map_smul' := fun c f => by
        funext k
        show deriv (fun t => c • f.1 (k * γ t)) 0 = _
        exact deriv_const_smul c (f.2 k) }
  obtain ⟨D, hD⟩ := LinearMap.exists_extend D₀
  refine ⟨⟨D, fun g φ => ?_⟩, fun V hV hVs g φ hφ => ?_⟩
  · have hm : slc g φ ∈ P := fun k => (F g φ k).differentiableAt
    have h1 := congrArg (fun L => L ⟨slc g φ, hm⟩) hD
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h1
    rw [h1]
    funext k
    exact (F g φ k).deriv
  · haveI := hV
    exact mem_of_hasDerivAt V (c := fun t k => slc g φ (k * γ t)) (fun t => hVs _ hφ (γ t)) (fun k => F g φ k)

theorem UpperTheory.algMod_bot_compact_casimir_of_types :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (S : Submodule ℂ (archSmooth K n)), Types S → ∀ (ι : Type) [Fintype ι] (X : ι → (isExpLieAlgebra K n).lieSubalgebra) (c : ι → ℝ), (∀ i, c i = 0 ∨ ∀ t : ℝ, (isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie (X i)) ∈ archCompact K n) → AlgMod S ⊥ (uAction (∑ i, c i • (UniversalEnvelopingAlgebra.ι ℝ (X i) * UniversalEnvelopingAlgebra.ι ℝ (X i)))) := by
  intro K _ _ n S hS ι _ X c hc
  obtain ⟨V, hV, hVs, hSV⟩ := hS
  have hi : ∀ i, ∃ Di : Module.End ℂ (archCompact K n → ℂ), ∀ g φ,
      c i • Di (Di (slc g φ)) = slc g (c i • uAction (UniversalEnvelopingAlgebra.ι ℝ (X i))
        (uAction (UniversalEnvelopingAlgebra.ι ℝ (X i)) φ)) := by
    intro i
    rcases hc i with h0 | hX
    · exact ⟨0, fun g φ => by simp [h0]⟩
    · obtain ⟨D, hD⟩ := (slc_op (X i) hX).1
      exact ⟨D, fun g φ => by rw [hD, hD, LinearMap.map_smul_of_tower]⟩
  choose Di hDi using hi
  have e1 : ∀ φ : archSmooth K n, uAction (∑ i, c i • (UniversalEnvelopingAlgebra.ι ℝ (X i) *
      UniversalEnvelopingAlgebra.ι ℝ (X i))) φ = ∑ i, c i • uAction (UniversalEnvelopingAlgebra.ι ℝ (X i))
        (uAction (UniversalEnvelopingAlgebra.ι ℝ (X i)) φ) := by
    intro φ
    simp only [map_sum, map_smul, map_mul, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply]
  have hinter : ∀ g φ, (∑ i, c i • (Di i * Di i)) (slc g φ) = slc g (uAction (∑ i, c i •
      (UniversalEnvelopingAlgebra.ι ℝ (X i) * UniversalEnvelopingAlgebra.ι ℝ (X i))) φ) := by
    intro g φ
    rw [e1, map_sum]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply]
    exact Finset.sum_congr rfl fun i _ => hDi i g φ
  have hstab : ∀ φ ∈ (⨅ g, V.comap (slc g)), uAction (∑ i, c i •
      (UniversalEnvelopingAlgebra.ι ℝ (X i) * UniversalEnvelopingAlgebra.ι ℝ (X i))) φ ∈ (⨅ g, V.comap (slc g)) := by
    intro φ hφ
    simp only [Submodule.mem_iInf, Submodule.mem_comap] at hφ ⊢
    intro g
    rw [e1, map_sum]
    refine V.sum_mem fun i _ => ?_
    rw [LinearMap.map_smul_of_tower]
    rcases hc i with h0 | hX
    · rw [h0, zero_smul]
      exact V.zero_mem
    · exact V.smul_of_tower_mem _ ((slc_op (X i) hX).2 V hV hVs g _ ((slc_op (X i) hX).2 V hV hVs g φ (hφ g)))
  have hinV : ∀ g, ∀ φ ∈ (⨅ g, V.comap (slc g)), slc g φ ∈ V := by
    intro g φ hφ
    simp only [Submodule.mem_iInf, Submodule.mem_comap] at hφ
    exact hφ g
  obtain ⟨q, hq, -, hq0⟩ := UpperTheory.V.Af.CuspFin.polySlices (archSmooth K n) (archCompact K n → ℂ)
    (AdelicGLn.AdelicGL K n) _ _ (fun g => slc g) hinter V hV _ hstab hinV
  refine ⟨q, hq, fun φ hφ => ?_⟩
  rw [Submodule.mem_bot]
  have hN : φ ∈ (⨅ g, V.comap (slc g)) := by
    simp only [Submodule.mem_iInf, Submodule.mem_comap]
    exact fun g => hSV φ hφ g
  apply Subtype.ext
  funext g
  have h1 := congrFun (hq0 g φ hN) 1
  simpa [slc] using h1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisRepresentationModelOverFiniteExtension
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Module
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Wd

private theorem exists_lift {Γ k K : Type} [Group Γ] [Field k] [Field K] [Algebra k K] (L : IntermediateField k K)
    (ψ : Γ →* Kˣ) (hψ : ∀ g, (ψ g : K) ∈ L) : ∃ ψL : Γ →* (↥L)ˣ, ∀ g, ((ψL g : ↥L) : K) = ψ g :=
  ⟨MonoidHom.toHomUnits (((Units.coeHom K).comp ψ).codRestrict L hψ), fun _ => rfl⟩

private theorem toMatrix_repE {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω Gw O) {m : ℕ} (L : FinExt l) (r : ↥Gw →* GL (Fin m) ↥L.1) (g : ↥(GK Bw.Kw)) :
    LinearMap.toMatrix (Pi.basisFun ↥L.1 (Fin m)) (Pi.basisFun ↥L.1 (Fin m)) (Bw.repE L r g) =
      (r (Bw.e.symm g) : Matrix (Fin m) (Fin m) ↥L.1) := by
  have e : Bw.repE L r g = Matrix.toLin' (r (Bw.e.symm g) : Matrix (Fin m) (Fin m) ↥L.1) :=
    LinearMap.ext fun _ => rfl
  rw [e, LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']

theorem UpperTheory.galois_representation_model_over_finite_extension :
    UpperTheory.V.Af.Wd.Model := by
  intro F Ω _ _ _ _ _ l _ ι n r w A h O _ _ _ Bw hj κ χ hχ hfl hr
  obtain ⟨p, hp⟩ := hfl
  let r' : ↥(Dec (F := F) A) →* GL (Fin n) (Qbar l) :=
    (MulAut.conj p).toMonoidHom.comp (r.comp (Dec (F := F) A).subtype)
  have hr' : ∀ s, r' s = p * r s * p⁻¹ := fun _ => rfl
  have hc := GlobalTheory.T.fontaineParameter_invariant_under_conjugation F Ω l ι n (Loc.PP l) (Loc.AIP l) (Loc.tiedP l) w A h O Bw hj
    (r.comp (Dec (F := F) A).subtype) r' p hr' hr
  obtain ⟨hpst, hwd⟩ := hc
  have hm := wdAt_of_isPstAt ι Bw h hj hpst
  obtain ⟨L₁, r₁, hm₁, hp₁, e₁⟩ := hm
  have hL : ∃ L : FinExt l, L₁.1 ≤ L.1 ∧ ∀ i s, (χ i s : Om l) ∈ L.1 := by
    have hfin : (⋃ i, Units.val '' Set.range (χ i)).Finite := Set.finite_iUnion fun i => (hχ i).image _
    haveI : Finite ↥(⋃ i, Units.val '' Set.range (χ i)) := hfin
    refine ⟨supExt L₁ ⟨IntermediateField.adjoin ℚ_[l] (⋃ i, Units.val '' Set.range (χ i)),
      IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x⟩,
      le_sup_left, fun i s => ?_⟩
    exact (le_sup_right : IntermediateField.adjoin ℚ_[l] (⋃ i, Units.val '' Set.range (χ i)) ≤ _)
      (IntermediateField.subset_adjoin _ _ (Set.mem_iUnion.2 ⟨i, _, ⟨s, rfl⟩, rfl⟩))
  obtain ⟨L, h₁, hχL⟩ := hL
  have hm₂ := hm₁.enlarge h₁
  have hp₂ := GlobalTheory.T.isPotentiallySemistable_coefficientField_enlarge (Loc.PP l) Bw h₁ r₁ hp₁
  have e₂ := GlobalTheory.T.potSemistableParameter_coefficientField_enlarge (Loc.PP l) ι Bw h hj h₁ r₁ hp₁
  generalize mapRep (IntermediateField.inclusion h₁).toRingHom r₁ = r₂ at hm₂ hp₂ e₂
  have er : ∀ s i j, (p * r (s : ↥(Dec (F := F) A)) * p⁻¹ : GL (Fin n) (Qbar l)) i j =
      (((r₂ s : Matrix (Fin n) (Fin n) ↥L.1) i j : ↥L.1) : Om l) :=
    fun s i j => by rw [← hr', ← hm₂.2]; rfl
  have hκL : ∀ i s, (κ i s : Om l) ∈ L.1 := fun i s => by
    rw [← (hp s).2 i, er]; exact SetLike.coe_mem _
  choose κL hκ using fun i => exists_lift L.1 ((κ i).comp Bw.e.symm.toMonoidHom) fun g => hκL i _
  choose χL hχ' using fun i => exists_lift L.1
    (((χ i).comp (Dec (F := F) A).subtype).comp Bw.e.symm.toMonoidHom) fun g => hχL i _
  refine ⟨L, Bw.repE L r₂, κL, χL, hp₂, hwd.symm.trans (e₁.trans e₂.symm),
    ⟨Pi.basisFun _ _, fun g => ⟨fun i j hij => ?_, fun i => ?_⟩⟩, fun i s => ?_, fun i s => ?_⟩
  · rw [toMatrix_repE]
    exact Subtype.ext ((er _ i j).symm.trans ((hp _).1 i j hij))
  · rw [toMatrix_repE]
    exact Subtype.ext (((er _ i i).symm.trans ((hp _).2 i)).trans (hκ i g).symm)
  · rw [hκ]
    exact congrArg (fun t => (κ i t : Qbar l)) (Bw.e.symm_apply_apply s)
  · rw [hχ']
    exact congrArg (fun t : ↥(Dec (F := F) A) => (χ i t : Qbar l)) (Bw.e.symm_apply_apply s)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.WeilDeligneFunctorExactness
section
open Module

private theorem finrank_add_of_exact {k A B C : Type} [Field k] [AddCommGroup A] [Module k A] [AddCommGroup B]
    [Module k B] [AddCommGroup C] [Module k C] [FiniteDimensional k A] [FiniteDimensional k B] (f : A →ₗ[k] B)
    (p : B →ₗ[k] C) (hp : Function.Surjective p) (hex : Function.Exact f p) :
    finrank k (LinearMap.ker f) + finrank k B = finrank k A + finrank k C := by
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  have h2 := LinearMap.finrank_range_add_finrank_ker p
  rw [LinearMap.range_eq_top.mpr hp, finrank_top, LinearMap.exact_iff.mp hex] at h2
  omega

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.Pst.DpstMap in
theorem UpperTheory.weil_deligne_functor_exactness :
    UpperTheory.V.Af.Wd.WdExact := by
  intro l _ ι K L V' V V'' _ _ _ _ _ _ _ _ _ _ _ _ _ ρ' ρ ρ'' f p hf hp hfi hps hex hV
  obtain ⟨hV', hV'', hds⟩ := UpperTheory.dpst_right_exact l K L V' V V'' ρ' ρ ρ'' f p hf hp hfi hps hex hV
  obtain ⟨-, hde⟩ := UpperTheory.weilDeligne_dpst_leftExact l (UpperTheory.V.Loc.PP l) K L V' V V'' ρ' ρ ρ'' f p hf hp hfi hex
  haveI : FiniteDimensional ↥L.1 V' := FiniteDimensional.of_injective f hfi
  haveI : FiniteDimensional ↥L.1 V'' := Module.Finite.of_surjective p hps
  have key : Function.Exact (wdLin (UpperTheory.V.Loc.PP l) ι hf) (wdLin (UpperTheory.V.Loc.PP l) ι hp) ∧
      Function.Surjective (wdLin (UpperTheory.V.Loc.PP l) ι hp) :=
    letI := algC ι L
    UpperTheory.weilDeligne_functor_exact _ _ _ _ _ ℂ (mulD (UpperTheory.V.Loc.PP l) ρ') (mulD (UpperTheory.V.Loc.PP l) ρ) (mulD (UpperTheory.V.Loc.PP l) ρ'') (urC ι)
      (dmap (UpperTheory.V.Loc.PP l) hf) (dmap (UpperTheory.V.Loc.PP l) hp) _ _ hde hds
  refine ⟨hV', hV'', ?_, key.2, key.1⟩
  haveI := hV.finite
  haveI := hV'.finite
  have h1 := finrank_add_of_exact _ _ key.2 key.1
  have h2 := finrank_add_of_exact f p hps hex
  rw [LetterDim.finrank_wdSpace l _ ι K L V ρ hV, LetterDim.finrank_wdSpace l _ ι K L V' ρ' hV',
    LetterDim.finrank_wdSpace l _ ι K L V'' ρ'' hV''] at h1
  rw [LinearMap.ker_eq_bot.mpr hfi, finrank_bot] at h2
  rw [← LinearMap.ker_eq_bot, ← Submodule.finrank_eq_zero]
  omega
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.WeilDeligneUnramifiedPeriod
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Module TensorProduct GlobalTheory.Pst Polynomial

private theorem key {Q V B B' : Type} [Field Q] [AddCommGroup V] [Module Q V] [CommRing B] [Algebra Q B]
    [AddCommGroup B'] [Module Q B'] {n : ℕ} (e : Basis (Fin n) Q V) (T : V →ₗ[Q] V) (c : B →ₗ[Q] B')
    (w w' : Fin n → B) (h : ∀ i, ∑ j, algebraMap Q B (e.repr (T (e j)) i) * w' j = w i) :
    ∑ j, T (e j) ⊗ₜ[Q] c (w' j) = ∑ i, e i ⊗ₜ[Q] c (w i) := by
  have h1 : ∀ j, T (e j) ⊗ₜ[Q] c (w' j) = ∑ i, e i ⊗ₜ[Q] c (algebraMap Q B (e.repr (T (e j)) i) * w' j) := by
    intro j
    conv_lhs => rw [← e.sum_repr (T (e j))]
    rw [sum_tmul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_tmul, ← Algebra.smul_def, map_smul]
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← tmul_sum, ← map_sum, h]

private theorem eq_zero {Q V B' : Type} [Field Q] [AddCommGroup V] [Module Q V]
    [AddCommGroup B'] [Module Q B'] {n : ℕ} (e : Basis (Fin n) Q V) (w : Fin n → B')
    (h : ∑ i, e i ⊗ₜ[Q] w i = 0) (k : Fin n) : w k = 0 := by
  have := congrArg (fun x => TensorProduct.lid Q B' (LinearMap.rTensor B' (e.coord k) x)) h
  simpa [map_sum, Finsupp.single_apply, ite_smul] using this

private theorem phiV_pow {l : ℕ} [Fact l.Prime] (P : LocPrime l)
    (LL : Type) [Field LL] [Algebra ℚ_[l] LL] (k : ℕ) (v : LL) (b : P.R.B) :
    (phiV P LL LL ^ k) (v ⊗ₜ C b) = v ⊗ₜ C ((P.φB ^ k) b) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', pow_succ', Module.End.mul_apply, ih, phiV_tmul, phiSt_C, AlgHom.mul_apply]

theorem UpperTheory.weilDeligne_unramified_period :
    UpperTheory.V.Af.Wd.UnrPer := by
  intro l _ K L η hη hI
  haveI := GlobalTheory.UnramifiedCrys.compactSpace_GK K
  haveI : FiniteDimensional ℚ_[l] ↥L.1 := L.2
  haveI : IsModuleTopology ℚ_[l] ↥L.1 := isModuleTopologyOfFiniteDimensional
  have hη' : Continuous fun g => (η g : ↥L.1) := continuous_induced_rng.2 hη
  obtain ⟨n, e, M, hMc, hM⟩ := UpperTheory.galois_representation_integral_lattice l ↥(GK K) ↥L.1 (V.Loc.resCoef ℚ_[l] (V.Loc.chRep η))
    (fun x => hη'.mul continuous_const)
  obtain ⟨W, hW, hWg, hWφ⟩ := UpperTheory.crystalline_frobenius_algebraic_elements l K n M hMc (fun g hg => by
    rw [← map_one M]
    ext i j
    apply PadicInt.ext
    rw [hM, hM, map_one]
    congr 2
    change (η g : ↥L.1) * e j = e j
    rw [hI g hg, Units.val_one, one_mul])
  haveI := nontrivial_B (V.Loc.PP l)
  haveI : Nonempty (Fin n) := e.index_nonempty
  let j₀ : Fin n := Classical.arbitrary _
  let c : V.Loc.Bcr l →ₗ[ℚ_[l]] Bst (V.Loc.PP l) := (CAlgHom : V.Loc.Bcr l →ₐ[ℚ_[l]] Bst (V.Loc.PP l)).toLinearMap
  have hk : ∀ (g : ↥(GK K)) (f : V.Loc.Bcr l → V.Loc.Bcr l),
      (M g).map (fun z => algebraMap ℚ_[l] (V.Loc.Bcr l) (z : ℚ_[l])) * W.map f = W →
      ∑ j, ((η g : ↥L.1) * e j) ⊗ₜ[ℚ_[l]] (C (f (W j j₀)) : Bst (V.Loc.PP l)) = ∑ i, e i ⊗ₜ[ℚ_[l]] C (W i j₀) := by
    intro g f h
    refine key e (V.Loc.resCoef ℚ_[l] (V.Loc.chRep η) g) c (fun i => W i j₀) (fun i => f (W i j₀)) fun i => ?_
    have := congrFun (congrFun h i) j₀
    simpa only [Matrix.mul_apply, Matrix.map_apply, hM] using this
  refine ⟨∑ i, e i ⊗ₜ[ℚ_[l]] C (W i j₀), fun h0 => ?_, fun g => ?_, fun g k hg => ?_⟩
  · refine hW.ne_zero (Matrix.det_eq_zero_of_column_eq_zero j₀ fun i => ?_)
    exact C_eq_zero.1 (eq_zero e (fun i => (C (W i j₀) : Bst (V.Loc.PP l))) h0 i)
  · rw [map_sum]
    simp only [stRep_tmul, actSt_C]
    exact hk g _ (hWg g)
  · rw [map_sum, Finset.smul_sum]
    simp only [phiV_pow, smul_tmul']
    exact hk g _ (hWφ g k hg)
end

