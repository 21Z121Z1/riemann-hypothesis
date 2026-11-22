import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0096
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0176
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0154
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0186
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0187
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0188
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0077

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarRepCommuteAndAnnihilate
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem action_commute_and_killed_by_polynomials
    (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C] (Λ : Type) [CommRing Λ] (h : ℕ)
    (R : Type) [CommRing R] [Algebra R Λ] (φ : R →+* O)
    (ρ : Λ →+* Matrix (Fin h) (Fin h) O)
    (hρ : ∀ c : R, ρ (algebraMap R Λ c) = φ c • (1 : Matrix (Fin h) (Fin h) O)) :
    (∀ a b : Λ, Commute (Matrix.toLin' ((ρ a).map (algebraMap O C)))
      (Matrix.toLin' ((ρ b).map (algebraMap O C)))) ∧
    ∀ (a : Λ) (f : Polynomial R), Polynomial.aeval a f = 0 →
      Polynomial.aeval (Matrix.toLin' ((ρ a).map (algebraMap O C)))
        (f.map ((algebraMap O C).comp φ)) = 0 := by
  let Φ : Λ →+* Module.End C (Fin h → C) :=
    ((Matrix.toLinAlgEquiv' (R := C) (n := Fin h)).toRingEquiv.toRingHom).comp
      (((algebraMap O C).mapMatrix).comp ρ)
  have hΦ : ∀ a, Matrix.toLin' ((ρ a).map (algebraMap O C)) = Φ a := fun a => by
    ext i j
    simp [Φ, Matrix.toLinAlgEquiv'_apply, Matrix.toLin'_apply]
  have hscal : (algebraMap C (Module.End C (Fin h → C))).comp ((algebraMap O C).comp φ)
      = Φ.comp (algebraMap R Λ) := by
    ext c : 1
    show _ = Φ (algebraMap R Λ c)
    rw [RingHom.comp_apply, ← hΦ, hρ]
    ext i j
    simp [Matrix.toLin'_apply, Matrix.one_apply, Pi.single_apply, Module.algebraMap_end_apply,
      Matrix.map_apply, Matrix.mulVec]
    split_ifs <;> simp
  refine ⟨fun a b => ?_, fun a f hf => ?_⟩
  · rw [hΦ, hΦ]
    exact (Commute.all a b).map Φ
  · rw [hΦ, Polynomial.aeval_def, Polynomial.eval₂_map, hscal, ← Polynomial.hom_eval₂,
      ← Polynomial.aeval_def, hf, map_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalingOpenSubgroupsFinite
section
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.BoxCosetSum

variable {F : Type} [Field F] [NumberField F]

theorem continuous_evalV' (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) :=
  RestrictedProduct.continuous_eval (R := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
    (A := fun w : HeightOneSpectrum (𝓞 F) => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) v

theorem eventually_evalV_mem_integers (x : FiniteAdeleRing (𝓞 F) F) :
    ∀ᶠ v in Filter.cofinite, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v x ∈ v.adicCompletionIntegers F := x.2

theorem isOpen_box (B : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F))
    (hBo : ∀ v, IsOpen (B v : Set (v.adicCompletion F)))
    (hBO : ∀ v, (B v : Set (v.adicCompletion F)) ⊆ v.adicCompletionIntegers F)
    (hBf : ∀ᶠ v in Filter.cofinite, (B v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F) :
    IsOpen {x : FiniteAdeleRing (𝓞 F) F | ∀ v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v x ∈ B v} := by
  have hT : {v | ¬ (B v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F}.Finite :=
    Filter.eventually_cofinite.1 hBf
  have hO : IsOpen {x : FiniteAdeleRing (𝓞 F) F |
      ∀ v, x v ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))} :=
    RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      (fun v => Valued.isOpen_valuationSubring _)
  have e : {x : FiniteAdeleRing (𝓞 F) F | ∀ v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v x ∈ B v} =
      {x : FiniteAdeleRing (𝓞 F) F | ∀ v, x v ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))} ∩
        ⋂ v ∈ hT.toFinset, (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) ⁻¹' (B v : Set (v.adicCompletion F)) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage,
      Set.Finite.mem_toFinset, SetLike.mem_coe]
    constructor
    · intro h
      exact ⟨fun v => hBO v (h v), fun v _ => h v⟩
    · rintro ⟨h1, h2⟩ v
      by_cases hv : (B v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F
      · have : x v ∈ (B v : Set (v.adicCompletion F)) := by rw [hv]; exact h1 v
        exact this
      · exact h2 v hv
  rw [e]
  exact hO.inter (isOpen_biInter_finset fun v _ => (hBo v).preimage (continuous_evalV' v))

def boxSub (κ : Type) (B : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F)) :
    AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F) where
  carrier := {u | ∀ i v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (u i) ∈ B v}
  add_mem' := by
    intro a b ha hb i v
    simp only [Pi.add_apply, map_add]
    exact (B v).add_mem (ha i v) (hb i v)
  zero_mem' := by
    intro i v
    simp only [Pi.zero_apply, map_zero]
    exact (B v).zero_mem
  neg_mem' := by
    intro a ha i v
    simp only [Pi.neg_apply, map_neg]
    exact (B v).neg_mem (ha i v)

theorem mem_boxSub {κ : Type} {B : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F)}
    {u : κ → FiniteAdeleRing (𝓞 F) F} :
    u ∈ boxSub κ B ↔ ∀ i v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (u i) ∈ B v := Iff.rfl

theorem isOpen_boxSub (κ : Type) [Finite κ] (B : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F))
    (hBo : ∀ v, IsOpen (B v : Set (v.adicCompletion F)))
    (hBO : ∀ v, (B v : Set (v.adicCompletion F)) ⊆ v.adicCompletionIntegers F)
    (hBf : ∀ᶠ v in Filter.cofinite, (B v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F) :
    IsOpen (boxSub κ B : Set (κ → FiniteAdeleRing (𝓞 F) F)) := by
  have e : (boxSub κ B : Set (κ → FiniteAdeleRing (𝓞 F) F)) =
      ⋂ i, (fun u : κ → FiniteAdeleRing (𝓞 F) F => u i) ⁻¹'
        {x : FiniteAdeleRing (𝓞 F) F | ∀ v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v x ∈ B v} := by
    ext u
    simp only [SetLike.mem_coe, mem_boxSub, Set.mem_iInter, Set.mem_preimage, Set.mem_setOf_eq]
  rw [e]
  exact isOpen_iInter_of_finite fun i => (isOpen_box B hBo hBO hBf).preimage (continuous_apply i)

theorem finprod_indicator_eq (κ : Type) [Finite κ]
    (B : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F))
    (hBO : ∀ v, (B v : Set (v.adicCompletion F)) ⊆ v.adicCompletionIntegers F)
    (hBf : ∀ᶠ v in Filter.cofinite, (B v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F)
    (r y : κ → FiniteAdeleRing (𝓞 F) F) :
    (∏ᶠ v, Set.indicator {x : κ → v.adicCompletion F | ∀ i, x i - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (r i) ∈ B v}
          (1 : (κ → v.adicCompletion F) → ℂ) (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i))) =
      Set.indicator {z | z - r ∈ boxSub κ B} (fun _ => (1 : ℂ)) y := by
  have key : ∀ v, ((fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) ∈
      {x : κ → v.adicCompletion F | ∀ i, x i - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (r i) ∈ B v}) ↔
      ∀ i, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v ((y - r) i) ∈ B v := by
    intro v
    simp only [Set.mem_setOf_eq, Pi.sub_apply, map_sub]
  by_cases h : y - r ∈ boxSub κ B
  · rw [Set.indicator_of_mem (show y ∈ {z | z - r ∈ boxSub κ B} from h)]
    apply finprod_eq_one_of_forall_eq_one
    intro v
    rw [Set.indicator_of_mem ((key v).2 fun i => h i v), Pi.one_apply]
  · rw [Set.indicator_of_notMem (show y ∉ {z | z - r ∈ boxSub κ B} from h)]
    rw [mem_boxSub] at h
    push_neg at h
    obtain ⟨i0, v0, hv0⟩ := h
    apply finprod_eq_zero _ v0
    · rw [Set.indicator_of_notMem]
      rw [key v0]
      exact fun H => hv0 (H i0)
    · have hT : {v | ¬ (B v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F}.Finite :=
        Filter.eventually_cofinite.1 hBf
      have hI : (⋃ i, {v | ¬ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v ((y - r) i) ∈ v.adicCompletionIntegers F}).Finite :=
        Set.finite_iUnion fun i => Filter.eventually_cofinite.1 (eventually_evalV_mem_integers ((y - r) i))
      refine (hT.union hI).subset ?_
      intro v hv
      by_contra hc
      simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion, not_or, not_not, not_exists] at hc
      apply hv
      dsimp only
      rw [Set.indicator_of_mem, Pi.one_apply]
      rw [key v]
      intro i
      have h2 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v ((y - r) i) ∈
          ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) := hc.2 i
      rw [← hc.1] at h2
      exact h2

theorem eq_sum_finprod_box_indicator : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (B : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F)),
    (∀ v, IsOpen (B v : Set (v.adicCompletion F))) →
    (∀ v, (B v : Set (v.adicCompletion F)) ⊆ v.adicCompletionIntegers F) →
    (∀ᶠ v in Filter.cofinite, (B v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F) →
    ∀ g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ, HasCompactSupport g →
      (∀ y u : κ → FiniteAdeleRing (𝓞 F) F, (∀ i v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (u i) ∈ B v) → g (y + u) = g y) →
      ∃ R : Finset (κ → FiniteAdeleRing (𝓞 F) F), g = ∑ r ∈ R, g r • fun y : κ → FiniteAdeleRing (𝓞 F) F =>
        ∏ᶠ v, Set.indicator {x : κ → v.adicCompletion F | ∀ i, x i - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (r i) ∈ B v}
          (1 : (κ → v.adicCompletion F) → ℂ) (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) := by
  intro F _ _ κ _ B hBo hBO hBf g hg hinv
  classical
  set U := boxSub κ B with hU
  have hUo : IsOpen (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) := isOpen_boxSub κ B hBo hBO hBf
  have hK : IsCompact (tsupport g) := hg
  have hcov : tsupport g ⊆ ⋃ y : (κ → FiniteAdeleRing (𝓞 F) F), {x | x - y ∈ U} := by
    intro x _
    exact Set.mem_iUnion.2 ⟨x, by simp [U.zero_mem]⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun y => {x | x - y ∈ U})
    (fun y => hUo.preimage (continuous_id.sub continuous_const)) hcov
  let R : Finset (κ → FiniteAdeleRing (𝓞 F) F) :=
    (t.image (QuotientAddGroup.mk : (κ → FiniteAdeleRing (𝓞 F) F) → _ ⧸ U)).image Quotient.out
  have hdist : ∀ r ∈ R, ∀ r' ∈ R, ∀ x, x - r ∈ U → x - r' ∈ U → r = r' := by
    intro r hr r' hr' x h h'
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hr
    obtain ⟨q', -, rfl⟩ := Finset.mem_image.1 hr'
    have e1 : (QuotientAddGroup.mk q.out : _ ⧸ U) = QuotientAddGroup.mk x :=
      QuotientAddGroup.eq.2 (by rwa [neg_add_eq_sub])
    have e2 : (QuotientAddGroup.mk q'.out : _ ⧸ U) = QuotientAddGroup.mk x :=
      QuotientAddGroup.eq.2 (by rwa [neg_add_eq_sub])
    rw [QuotientAddGroup.out_eq'] at e1 e2
    rw [e1, e2]
  have hcover : ∀ x ∈ tsupport g, ∃ r ∈ R, x - r ∈ U := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht hx)
    refine ⟨(QuotientAddGroup.mk y : _ ⧸ U).out, Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hy), ?_⟩
    have e : -(QuotientAddGroup.mk y : _ ⧸ U).out + y ∈ U :=
      QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' _)
    have := U.add_mem hxy e
    convert this using 1
    abel
  refine ⟨R, ?_⟩
  funext x
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, finprod_indicator_eq κ B hBO hBf]
  by_cases hx : ∃ r ∈ R, x - r ∈ U
  · obtain ⟨r0, hr0, hxr0⟩ := hx
    rw [Finset.sum_eq_single_of_mem r0 hr0]
    · rw [Set.indicator_of_mem (show x ∈ {z | z - r0 ∈ boxSub κ B} from hxr0), mul_one]
      have := hinv r0 (x - r0) hxr0
      rwa [add_sub_cancel] at this
    · intro r hr hne
      have hm : x ∉ {z | z - r ∈ boxSub κ B} := fun h => hne (hdist r hr r0 hr0 _ h hxr0)
      rw [Set.indicator_of_notMem hm, mul_zero]
  · push_neg at hx
    have hK' : x ∉ tsupport g := fun h => by
      obtain ⟨r, hr, h'⟩ := hcover _ h
      exact hx r hr h'
    rw [image_eq_zero_of_notMem_tsupport hK']
    symm
    apply Finset.sum_eq_zero
    intro r hr
    have hm : x ∉ {z | z - r ∈ boxSub κ B} := hx r hr
    rw [Set.indicator_of_notMem hm, mul_zero]

end GlobalTheory.BoxCosetSum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchlessingerFlatFibreProduct
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace GlobalTheory.SchlessingerFlat

theorem exists_unique_of_isPullback : ∀ {P R₁ R₂ R₀ : CommRingCat.{0}} (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → ∀ (x : R₁) (y : R₂), g₁.hom x = g₂.hom y → ∃! p : P, f₁.hom p = x ∧ f₂.hom p = y := by
  intro P R₁ R₂ R₀ f₁ f₂ g₁ g₂ h x y hxy
  have H := (Types.isPullback_iff _ _ _ _).1 (h.map (forget CommRingCat))
  obtain ⟨p, hp₁, hp₂⟩ := H.2.2 x y hxy
  exact ⟨p, ⟨hp₁, hp₂⟩, fun q hq => H.2.1 q p ⟨hq.1.trans hp₁.symm, hq.2.trans hp₂.symm⟩⟩

theorem isPushout_of_surjective_of_ker : ∀ {P R B C : CommRingCat.{0}} (a : P ⟶ B) (f : P ⟶ R) (c : B ⟶ C) (a' : R ⟶ C), a ≫ c = f ≫ a' → Function.Surjective f → Function.Surjective c → RingHom.ker c.hom = (RingHom.ker f.hom).map a.hom → IsPushout a f c a' := by
  intro P R B C a f c a' w hf hc hk
  have hw : ∀ p, c.hom (a.hom p) = a'.hom (f.hom p) := fun p => congr($(w) p)
  have key : ∀ (s : PushoutCocone a f), RingHom.ker c.hom ≤ RingHom.ker s.inl.hom := by
    intro s
    rw [hk, Ideal.map_le_iff_le_comap]
    intro p hp
    have e : s.inl.hom (a.hom p) = s.inr.hom (f.hom p) := congr($(s.condition) p)
    rw [Ideal.mem_comap, RingHom.mem_ker, e, (RingHom.mem_ker).mp hp, map_zero]
  let d : ∀ (s : PushoutCocone a f), C ⟶ s.pt := fun s =>
    CommRingCat.ofHom ((Ideal.Quotient.lift (RingHom.ker c.hom) s.inl.hom (fun x hx => key s hx)).comp
      (RingHom.quotientKerEquivOfSurjective hc).symm.toRingHom)
  have hd : ∀ (s : PushoutCocone a f) (b : B), (d s).hom (c.hom b) = s.inl.hom b := by
    intro s b
    have : (RingHom.quotientKerEquivOfSurjective hc).symm (c.hom b) = Ideal.Quotient.mk _ b := by
      apply (RingHom.quotientKerEquivOfSurjective hc).injective
      simp
    simp [d, this]
    rfl
  refine ⟨⟨w⟩, ⟨PushoutCocone.IsColimit.mk _ d ?_ ?_ ?_⟩⟩
  · intro s; ext b; exact hd s b
  · intro s; ext r
    obtain ⟨p, rfl⟩ := hf r
    change (d s).hom (a'.hom (f.hom p)) = s.inr.hom (f.hom p)
    rw [← hw, hd]
    exact congr($(s.condition) p)
  · intro s m h1 _
    ext x
    obtain ⟨b, rfl⟩ := hc x
    rw [hd]
    exact congr($(h1) b)

theorem surjective_ker_of_isPushout : ∀ {R₁ R₀ B₁ B₀ : CommRingCat.{0}} (a₁ : R₁ ⟶ B₁) (g₁ : R₁ ⟶ R₀) (b₁ : B₁ ⟶ B₀) (a₀ : R₀ ⟶ B₀), IsPushout a₁ g₁ b₁ a₀ → Function.Surjective g₁ → Function.Surjective b₁ ∧ RingHom.ker b₁.hom = (RingHom.ker g₁.hom).map a₁.hom := by
  intro R₁ R₀ B₁ B₀ a₁ g₁ b₁ a₀ h hg
  let J : Ideal B₁ := (RingHom.ker g₁.hom).map a₁.hom
  let q : B₁ ⟶ CommRingCat.of (B₁ ⧸ J) := CommRingCat.ofHom (Ideal.Quotient.mk J)
  let a' : R₀ ⟶ CommRingCat.of (B₁ ⧸ J) := CommRingCat.ofHom
    ((Ideal.quotientMap J a₁.hom Ideal.le_comap_map).comp (RingHom.quotientKerEquivOfSurjective hg).symm.toRingHom)
  have w : a₁ ≫ q = g₁ ≫ a' := by
    ext r
    have e0 : (RingHom.quotientKerEquivOfSurjective hg).symm (g₁.hom r) = Ideal.Quotient.mk _ r := by
      apply (RingHom.quotientKerEquivOfSurjective hg).injective
      simp
    change Ideal.Quotient.mk J (a₁.hom r) = Ideal.quotientMap J a₁.hom Ideal.le_comap_map ((RingHom.quotientKerEquivOfSurjective hg).symm (g₁.hom r))
    rw [e0]
    rfl
  have h' := isPushout_of_surjective_of_ker a₁ g₁ q a' w hg Ideal.Quotient.mk_surjective Ideal.mk_ker
  have e := IsPushout.inl_isoIsPushout_hom _ _ h h'
  let φ := h.isoIsPushout _ _ h'
  have hb : ∀ x, φ.hom.hom (b₁.hom x) = Ideal.Quotient.mk J x := fun x => congr($(e) x)
  have hinj : Function.Injective φ.hom.hom := fun x y hxy => by
    simpa using congrArg φ.inv.hom hxy
  refine ⟨fun y => ?_, ?_⟩
  · obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (φ.hom.hom y)
    exact ⟨x, hinj (by rw [hb, hx])⟩
  · ext x
    rw [RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem, ← hb]
    constructor
    · intro h0; rw [h0, map_zero]
    · intro h0; exact hinj (h0.trans (map_zero _).symm)

theorem ker_eq_map_of_fibre : ∀ (P R₁ R₂ B B₁ B₂ : Type) [CommRing P] [CommRing R₁] [CommRing R₂] [CommRing B] [CommRing B₁] [CommRing B₂] (f₁ : P →+* R₁) (f₂ : P →+* R₂) (a : P →+* B) (a₁ : R₁ →+* B₁) (a₂ : R₂ →+* B₂) (c₁ : B →+* B₁) (c₂ : B →+* B₂) (I₂ : Ideal R₂), c₁.comp a = a₁.comp f₁ → c₂.comp a = a₂.comp f₂ → Function.Surjective c₂ → (∀ k ∈ I₂, ∃ p : P, f₁ p = 0 ∧ f₂ p = k) → (∀ x : B, c₁ x = 0 → c₂ x = 0 → x = 0) → (∀ x : B, c₁ x = 0 → c₂ x ∈ I₂.map a₂) → RingHom.ker c₁ = (RingHom.ker f₁).map a := by
  intro P R₁ R₂ B B₁ B₂ _ _ _ _ _ _ f₁ f₂ a a₁ a₂ c₁ c₂ I₂ w₁ w₂ hc₂ hlift hj hker
  have w₁' : ∀ p, c₁ (a p) = a₁ (f₁ p) := fun p => by simpa using RingHom.congr_fun w₁ p
  have w₂' : ∀ p, c₂ (a p) = a₂ (f₂ p) := fun p => by simpa using RingHom.congr_fun w₂ p
  have claim : ∀ y ∈ I₂.map a₂, ∃ z ∈ (RingHom.ker f₁).map a, c₁ z = 0 ∧ c₂ z = y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      obtain ⟨p, hp1, hp2⟩ := hlift k hk
      exact ⟨a p, Ideal.mem_map_of_mem _ hp1, by rw [w₁', hp1, map_zero], by rw [w₂', hp2]⟩
    | zero => exact ⟨0, Ideal.zero_mem _, map_zero _, map_zero _⟩
    | add u v _ _ hu hv =>
      obtain ⟨z1, h1, e1, e1'⟩ := hu
      obtain ⟨z2, h2, e2, e2'⟩ := hv
      exact ⟨z1 + z2, Ideal.add_mem _ h1 h2, by rw [map_add, e1, e2, add_zero], by rw [map_add, e1', e2']⟩
    | smul s u _ hu =>
      obtain ⟨z, hz, e, e'⟩ := hu
      obtain ⟨t, rfl⟩ := hc₂ s
      exact ⟨t * z, Ideal.mul_mem_left _ _ hz, by rw [map_mul, e, mul_zero], by rw [map_mul, e', smul_eq_mul]⟩
  apply le_antisymm
  · intro x hx
    rw [RingHom.mem_ker] at hx
    obtain ⟨z, hz, e, e'⟩ := claim _ (hker x hx)
    have h0 : x - z = 0 := hj _ (by rw [map_sub, hx, e, sub_zero]) (by rw [map_sub, e', sub_self])
    rw [sub_eq_zero.mp h0]
    exact hz
  · rw [Ideal.map_le_iff_le_comap]
    intro p hp
    rw [Ideal.mem_comap, RingHom.mem_ker, w₁', (RingHom.mem_ker).mp hp, map_zero]

theorem isNilpotent_ker_of_fibre : ∀ (P R₁ R₂ R₀ : Type) [CommRing P] [CommRing R₁] [CommRing R₂] [CommRing R₀] (f₁ : P →+* R₁) (f₂ : P →+* R₂) (g₁ : R₁ →+* R₀) (g₂ : R₂ →+* R₀), g₁.comp f₁ = g₂.comp f₂ → RingHom.ker f₁ ⊓ RingHom.ker f₂ = ⊥ → IsNilpotent (RingHom.ker g₂) → IsNilpotent (RingHom.ker f₁) := by
  intro P R₁ R₂ R₀ _ _ _ _ f₁ f₂ g₁ g₂ w hj hn
  obtain ⟨n, hn⟩ := hn
  refine ⟨n + 1, ?_⟩
  rw [Submodule.zero_eq_bot, eq_bot_iff]
  intro x hx
  have h1 : x ∈ RingHom.ker f₁ := Ideal.pow_le_self (Nat.succ_ne_zero n) hx
  have hle : (RingHom.ker f₁).map f₂ ≤ RingHom.ker g₂ := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    rw [Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply, ← w, RingHom.comp_apply,
      (RingHom.mem_ker).mp hy, map_zero]
  have h2 : f₂ x ∈ (RingHom.ker g₂) ^ (n + 1) := by
    have := Ideal.mem_map_of_mem f₂ hx
    rw [Ideal.map_pow] at this
    exact Ideal.pow_right_mono hle _ this
  rw [pow_succ, hn, Submodule.zero_eq_bot, Submodule.bot_mul] at h2
  have h3 : x ∈ RingHom.ker f₁ ⊓ RingHom.ker f₂ := ⟨h1, by simpa using h2⟩
  rw [hj] at h3
  exact h3

theorem mul_injective_of_flat : ∀ (P R₂ B B₂ : Type) [CommRing P] [CommRing R₂] [CommRing B] [CommRing B₂] [Algebra P B] (K₁ : Ideal P) (f₂ : P →+* R₂) (a₂ : R₂ →+* B₂) (c₂ : B →+* B₂), Function.Surjective f₂ → Function.Surjective c₂ → c₂.comp (algebraMap P B) = a₂.comp f₂ → RingHom.ker c₂ = (RingHom.ker f₂).map (algebraMap P B) → K₁ ⊓ RingHom.ker f₂ = ⊥ → a₂.Flat → Function.Injective (TensorProduct.lift ((LinearMap.lsmul P B).comp K₁.subtype)) := GlobalTheory.T.mul_tensor_injective_of_flat_baseChange_ker_inf

theorem flat_quotient_of_flat : ∀ (P R₁ B B₁ : Type) [CommRing P] [CommRing R₁] [CommRing B] [CommRing B₁] [Algebra P B] (f₁ : P →+* R₁) (a₁ : R₁ →+* B₁) (c₁ : B →+* B₁), Function.Surjective f₁ → Function.Surjective c₁ → c₁.comp (algebraMap P B) = a₁.comp f₁ → RingHom.ker c₁ = (RingHom.ker f₁).map (algebraMap P B) → a₁.Flat → Module.Flat (P ⧸ RingHom.ker f₁) (B ⧸ (RingHom.ker f₁ • ⊤ : Submodule P B)) := GlobalTheory.T.flat_quotient_smul_top_of_surjective_flat

theorem schlessinger_flat : ∀ (P R₁ R₂ R₀ B₁ B₂ B₀ B : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀) (a₁ : R₁ ⟶ B₁) (a₂ : R₂ ⟶ B₂) (a₀ : R₀ ⟶ B₀) (b₁ : B₁ ⟶ B₀) (b₂ : B₂ ⟶ B₀) (c₁ : B ⟶ B₁) (c₂ : B ⟶ B₂) (a : P ⟶ B), IsPullback f₁ f₂ g₁ g₂ → Function.Surjective g₁ → Function.Surjective g₂ → IsNilpotent (RingHom.ker g₁.hom) → IsNilpotent (RingHom.ker g₂.hom) → IsPushout a₁ g₁ b₁ a₀ → IsPushout a₂ g₂ b₂ a₀ → a₁.hom.Flat → a₂.hom.Flat → IsPullback c₁ c₂ b₁ b₂ → a ≫ c₁ = f₁ ≫ a₁ → a ≫ c₂ = f₂ ≫ a₂ → a.hom.Flat ∧ IsPushout a f₁ c₁ a₁ ∧ IsPushout a f₂ c₂ a₂ := by
  intro P R₁ R₂ R₀ B₁ B₂ B₀ B f₁ f₂ g₁ g₂ a₁ a₂ a₀ b₁ b₂ c₁ c₂ a hP hg₁ hg₂ hn₁ hn₂ hA₁ hA₂ hfl₁ hfl₂ hB hac₁ hac₂
  have eP := exists_unique_of_isPullback f₁ f₂ g₁ g₂ hP
  have eB := exists_unique_of_isPullback c₁ c₂ b₁ b₂ hB
  obtain ⟨hb₁, hkb₁⟩ := surjective_ker_of_isPushout a₁ g₁ b₁ a₀ hA₁ hg₁
  obtain ⟨hb₂, hkb₂⟩ := surjective_ker_of_isPushout a₂ g₂ b₂ a₀ hA₂ hg₂
  have wP : g₁.hom.comp f₁.hom = g₂.hom.comp f₂.hom := by
    rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, hP.w]
  have wB : ∀ x, b₁.hom (c₁.hom x) = b₂.hom (c₂.hom x) := fun x => by
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, hB.w]
  have w₁ : c₁.hom.comp a.hom = a₁.hom.comp f₁.hom := by
    rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, hac₁]
  have w₂ : c₂.hom.comp a.hom = a₂.hom.comp f₂.hom := by
    rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, hac₂]
  have sf₁ : Function.Surjective f₁.hom := fun x => by
    obtain ⟨y, hy⟩ := hg₂ (g₁.hom x)
    obtain ⟨p, hp, -⟩ := eP x y hy.symm
    exact ⟨p, hp.1⟩
  have sf₂ : Function.Surjective f₂.hom := fun y => by
    obtain ⟨x, hx⟩ := hg₁ (g₂.hom y)
    obtain ⟨p, hp, -⟩ := eP x y hx
    exact ⟨p, hp.2⟩
  have sc₁ : Function.Surjective c₁.hom := fun x => by
    obtain ⟨y, hy⟩ := hb₂ (b₁.hom x)
    obtain ⟨p, hp, -⟩ := eB x y hy.symm
    exact ⟨p, hp.1⟩
  have sc₂ : Function.Surjective c₂.hom := fun y => by
    obtain ⟨x, hx⟩ := hb₁ (b₂.hom y)
    obtain ⟨p, hp, -⟩ := eB x y hx
    exact ⟨p, hp.2⟩
  have jB : ∀ x : B, c₁.hom x = 0 → c₂.hom x = 0 → x = 0 := fun x h1 h2 => by
    obtain ⟨p, -, hu⟩ := eB 0 0 (by simp)
    rw [hu x ⟨h1, h2⟩, hu 0 ⟨by simp, by simp⟩]
  have jP : RingHom.ker f₁.hom ⊓ RingHom.ker f₂.hom = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨p, -, hu⟩ := eP 0 0 (by simp)
    rw [Ideal.mem_bot, hu x ⟨hx.1, hx.2⟩, hu 0 ⟨by simp, by simp⟩]
  have kc₁ : RingHom.ker c₁.hom = (RingHom.ker f₁.hom).map a.hom :=
    ker_eq_map_of_fibre P R₁ R₂ B B₁ B₂ f₁.hom f₂.hom a.hom a₁.hom a₂.hom c₁.hom c₂.hom (RingHom.ker g₂.hom) w₁ w₂ sc₂
      (fun k hk => by
        obtain ⟨p, hp, -⟩ := eP 0 k (by rw [map_zero]; exact ((RingHom.mem_ker).mp hk).symm)
        exact ⟨p, hp.1, hp.2⟩) jB
      (fun x hx => by
        rw [← hkb₂, RingHom.mem_ker, ← wB, hx, map_zero])
  have kc₂ : RingHom.ker c₂.hom = (RingHom.ker f₂.hom).map a.hom :=
    ker_eq_map_of_fibre P R₂ R₁ B B₂ B₁ f₂.hom f₁.hom a.hom a₂.hom a₁.hom c₂.hom c₁.hom (RingHom.ker g₁.hom) w₂ w₁ sc₁
      (fun k hk => by
        obtain ⟨p, hp, -⟩ := eP k 0 (by rw [map_zero]; exact ((RingHom.mem_ker).mp hk))
        exact ⟨p, hp.2, hp.1⟩) (fun x h2 h1 => jB x h1 h2)
      (fun x hx => by
        rw [← hkb₁, RingHom.mem_ker, wB, hx, map_zero])
  have nil₁ : IsNilpotent (RingHom.ker f₁.hom) :=
    isNilpotent_ker_of_fibre P R₁ R₂ R₀ f₁.hom f₂.hom g₁.hom g₂.hom wP jP hn₂
  refine ⟨?_, isPushout_of_surjective_of_ker a f₁ c₁ a₁ hac₁ sf₁ sc₁ kc₁, isPushout_of_surjective_of_ker a f₂ c₂ a₂ hac₂ sf₂ sc₂ kc₂⟩
  letI : Algebra P B := a.hom.toAlgebra
  change Module.Flat P B
  exact GlobalTheory.NilpotentFlat.flat_of_isNilpotent P (RingHom.ker f₁.hom) nil₁ B
    (flat_quotient_of_flat P R₁ B B₁ f₁.hom a₁.hom c₁.hom sf₁ sc₁ w₁ kc₁ hfl₁)
    (mul_injective_of_flat P R₂ B B₂ (RingHom.ker f₁.hom) f₂.hom a₂.hom c₂.hom sf₂ sc₂ w₂ kc₂ jP hfl₂)

end GlobalTheory.SchlessingerFlat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzCompactSupportDense
section
open MeasureTheory Filter Topology
open scoped SchwartzMap

namespace GlobalTheory

theorem schwartz_mem_closure_hasCompactSupport :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (f : SchwartzMap V ℂ),
    f ∈ closure {g : SchwartzMap V ℂ | HasCompactSupport (g : V → ℂ)} := by
  intro V _ _ _ f
  exact schwartz_dense_hasCompactSupport f

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFamilyPhaseBoundStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_family_phase_bound : ∀ (E P : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup P] [NormedSpace ℝ P]
    (A : P →L[ℝ] E →L[ℝ] ℝ) (f : SchwartzMap E ℂ), ∃ Φ : P → SchwartzMap E ℂ,
    (∀ ξ x, Φ ξ x = Complex.exp (Complex.I * (A ξ x : ℂ)) * f x) ∧ Continuous Φ ∧
    ∀ k n : ℕ, ∃ C : ℝ, ∀ ξ, SchwartzMap.seminorm ℂ k n (Φ ξ) ≤ C * (1 + ‖ξ‖ ^ n) := by
  first | exact @GlobalTheory.CharFamily.charMul_family | exact GlobalTheory.CharFamily.charMul_family | (intros; apply GlobalTheory.CharFamily.charMul_family <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFunctionalIntegralCommStatement
section
open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_functional_integral_comm : ∀ (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W]
    [BorelSpace W] (ν : Measure W) [SigmaFinite ν] (n : ℕ) (L : Sch (Fin n) →L[ℂ] ℂ) (G : W → Sch (Fin n))
    (c : W → ℂ) (g : Sch (Fin n)), Continuous G → Continuous c →
    (∀ k m : ℕ, Integrable (fun w => ‖c w‖ * SchwartzMap.seminorm ℂ k m (G w)) ν) →
    (∀ x, g x = ∫ w, c w * G w x ∂ν) → L g = ∫ w, c w * L (G w) ∂ν := by
  first | exact @GlobalTheory.SchwartzIntegral.clm_integral_interchange | exact GlobalTheory.SchwartzIntegral.clm_integral_interchange | (intros; apply GlobalTheory.SchwartzIntegral.clm_integral_interchange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSliceSeminormLeStatement
section
open scoped SchwartzMap ContDiff
open GlobalTheory.SchwartzFstOp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_slice_seminorm_le : ∀ {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup V'] [NormedSpace ℝ V'] (f : 𝓢(V × V', ℂ)) (x' : V') (j k n : ℕ), ‖x'‖ ^ k * SchwartzMap.seminorm ℂ j n (sliceCLM x' f) ≤ SchwartzMap.seminorm ℂ (j + k) n f := by
  first | exact @GlobalTheory.SchwartzFstOp.norm_pow_mul_seminorm_sliceCLM_le | exact GlobalTheory.SchwartzFstOp.norm_pow_mul_seminorm_sliceCLM_le | (intros; apply GlobalTheory.SchwartzFstOp.norm_pow_mul_seminorm_sliceCLM_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzTranslateTaylorSecondOrderStatement
section
open scoped SchwartzMap ContDiff
open GlobalTheory.SchwartzFstOp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_translate_taylor_second_order : ∀ {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] (f : 𝓢(X, ℂ)) (k n : ℕ), ∃ C : ℝ, ∀ a : X, ‖a‖ ≤ 1 → SchwartzMap.seminorm ℂ k n (SchwartzMap.compSubConstCLM ℂ (-a) f - f - LineDeriv.lineDerivOpCLM ℂ 𝓢(X, ℂ) a f) ≤ C * ‖a‖ ^ 2 := by
  first | exact @GlobalTheory.SchwartzTranslateUnif.seminorm_translate_sub_lineDeriv_le | exact GlobalTheory.SchwartzTranslateUnif.seminorm_translate_sub_lineDeriv_le | (intros; apply GlobalTheory.SchwartzTranslateUnif.seminorm_translate_sub_lineDeriv_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAlongCurveProductsStableStatement
section
open MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_along_curve_products_stable_alt : ∀ (G : Type) [Group G] (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (ρ : G →* (K →L[ℂ] K)) (P : Type) (A : Set P) (e : P → ℝ → G) (v : K), (∀ (k : ℕ) (ps : Fin k → P), (∀ i, ps i ∈ A) → ContDiff ℝ ∞ fun t : Fin k → ℝ => ρ (List.ofFn fun i => e (ps i) (t i)).prod v) → (∀ p ∈ A, ∀ (k : ℕ) (ps : Fin k → P), (∀ i, ps i ∈ A) → ContDiff ℝ ∞ fun t : Fin k → ℝ => ρ (List.ofFn fun i => e (ps i) (t i)).prod (deriv (fun r : ℝ => ρ (e p r) v) 0)) ∧ (∀ (m : ℕ) (qs : Fin m → P) (r : Fin m → ℝ), (∀ i, qs i ∈ A) → ∀ (k : ℕ) (ps : Fin k → P), (∀ i, ps i ∈ A) → ContDiff ℝ ∞ fun t : Fin k → ℝ => ρ (List.ofFn fun i => e (ps i) (t i)).prod (ρ (List.ofFn fun i => e (qs i) (r i)).prod v)) ∧ ∀ l : List P, (∀ p ∈ l, p ∈ A) → ∀ (k : ℕ) (ps : Fin k → P), (∀ i, ps i ∈ A) → ContDiff ℝ ∞ fun t : Fin k → ℝ => l.foldr (fun p w => deriv (fun r : ℝ => ρ (e p r) w) 0) (ρ (List.ofFn fun i => e (ps i) (t i)).prod v) := by
  first | exact @GlobalTheory.smooth_along_curve_products_stable | exact GlobalTheory.smooth_along_curve_products_stable | (intros; apply GlobalTheory.smooth_along_curve_products_stable <;> assumption)
end

