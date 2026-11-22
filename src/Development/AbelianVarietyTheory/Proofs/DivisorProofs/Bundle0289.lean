import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0251
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0258
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0259
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0276
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0252
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0203
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0277
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0281
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0253
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0236
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0275

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantElementProduct
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem lead_mul {R C : Type} [CommRing R] [Field C] (f : R →+* C) (ξ r r' : R) (n n' : ℕ)
    (c c' : C) (h : Lead f ξ r n c) (h' : Lead f ξ r' n' c') :
    Lead f ξ (r * r') (n + n') (c * c') := by
  obtain ⟨s, t, hs, hr, ht⟩ := h
  obtain ⟨s', t', hs', hr', ht'⟩ := h'
  refine ⟨s * s', t * t', ?_, ?_, ?_⟩
  · rw [map_mul]; exact mul_ne_zero hs hs'
  · calc s * s' * (r * r') = (s * r) * (s' * r') := by ring
      _ = ξ ^ (n + n') * (t * t') := by rw [hr, hr', pow_add]; ring
  · rw [map_mul, map_mul, ht, ht']; ring

theorem detData_mul : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (C : Type) [Field C] [Algebra O C] (ε : PreTilt O p) (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (ψ : RL p O Λ →+* RL p O Λ) (N N' : ℕ) (Δ Δ' : RL p O Λ) (a a' : (Λ →+* O) → ℕ) (c c' : (Λ →+* O) → C), IsDetElt ε ψ N Δ → IsDetElt ε ψ N' Δ' → HasOrders C ε N Δ a c → HasOrders C ε N' Δ' a' c' → IsDetElt ε ψ (N + N') (Δ * Δ') ∧ HasOrders C ε (N + N') (Δ * Δ') (a + a') (c * c') := by
  intro p _ O _ _ _ C _ _ ε Λ _ _ ψ N N' Δ Δ' a a' c c' h1 h2 h3 h4
  obtain ⟨hd, g, hg, hgd⟩ := h1
  obtain ⟨hd', g', hg', hgd'⟩ := h2
  refine ⟨⟨?_, g * g', ?_, ?_⟩, ?_⟩
  · rw [pow_add]; exact mul_dvd_mul hd hd'
  · rw [map_mul]
    calc Δ * Δ' = (g * ψ Δ) * (g' * ψ Δ') := by rw [← hg, ← hg']
      _ = g * g' * (ψ Δ * ψ Δ') := by ring
  · rw [pow_add]; exact mul_dvd_mul hgd hgd'
  · intro σ f hf
    obtain ⟨ha, hc, hl⟩ := h3 σ f hf
    obtain ⟨ha', hc', hl'⟩ := h4 σ f hf
    refine ⟨?_, ?_, ?_⟩
    · simp only [Pi.add_apply]; omega
    · simp only [Pi.mul_apply]; exact mul_ne_zero hc hc'
    · simpa only [Pi.add_apply, Pi.mul_apply] using lead_mul _ _ _ _ _ _ _ _ hl hl'

end GlobalTheory.DetInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantLatticePrincipal
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem detLattice_eq_span_singleton : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (Λ : Type) [CommRing Λ] (h N : ℕ), v.Integers O → ∀ (ρ : Λ → Matrix (Fin h) (Fin h) O) (τ : Λ →+* O), iSupIndep (fun σ : Λ →+* O => eig C ρ σ) → (⨆ σ : Λ →+* O, eig C ρ σ) = ⊤ → Module.finrank C (eig C ρ τ) = N → Module.finrank C (detLine C ρ τ N) = 1 ∧ ∃ w : detLine C ρ τ N, w ≠ 0 ∧ detLattice C ρ τ N = Submodule.span O {w} := by
  intro C _ v O _ _ Λ _ h N hv ρ τ hind htop hN
  obtain ⟨π, hπ, -, hq⟩ := GlobalTheory.T.eigen_projection_quotient_lattice C O Λ h ρ τ hind htop
  have hsurj : Function.Surjective π := fun x => ⟨x, hπ x⟩
  obtain ⟨g, hgC, hgO⟩ := GlobalTheory.T.exists_spanning_image_lattice C O (eig C ρ τ) h π hsurj
  have hq' : quotLattice C ρ τ = (Submodule.span O (Set.range g) : Set (eig C ρ τ)) := by
    rw [hq, hgO]
  obtain ⟨hrank, s, hs⟩ := GlobalTheory.T.exteriorPower_top_finrank_one C (eig C ρ τ) h N g hgC hN
  have hspan : detLattice C ρ τ N =
      Submodule.span O (Set.range (fun s : Fin N → Fin h => exteriorPower.ιMulti C N (g ∘ s))) := by
    unfold detLattice
    rw [hq']
    exact GlobalTheory.T.exteriorPower_span_of_lattice C O (eig C ρ τ) h N g
  refine ⟨hrank, ?_⟩
  obtain ⟨w, hw, hwspan⟩ := GlobalTheory.T.rank_one_lattice_span_singleton C v O (⋀[C]^N (eig C ρ τ)) (Fin N → Fin h)
    (fun s : Fin N → Fin h => exteriorPower.ιMulti C N (g ∘ s)) hv hrank ⟨s, hs⟩
  exact ⟨w, hw, hspan.trans hwspan⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantOrdersIndependentOfRoot
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

open WittVector

namespace GlobalTheory

theorem detData_indep_eps : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε ε' : PreTilt O p) (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (ψ : RL p O Λ →+* RL p O Λ) (N : ℕ) (Δ : RL p O Λ) (a : (Λ →+* O) → ℕ) (c : (Λ →+* O) → C), Associated (xi ε) (xi ε') → Associated (mu ε) (mu ε') → IsDetElt ε ψ N Δ → HasOrders C ε N Δ a c → ∃ c' : (Λ →+* O) → C, IsDetElt ε' ψ N Δ ∧ HasOrders C ε' N Δ a c' ∧ ∀ σ, v (c' σ) = v (c σ) := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε ε' Λ _ _ ψ N Δ a c hxi hmu hD hH
  obtain ⟨u, hu⟩ := hxi
  obtain ⟨w, hw⟩ := hmu
  have key : ∀ (σ : Λ →+* O) (f : RL p O Λ →+* O), IsTheta σ f → ∀ x : Ainf p O,
      f (inA x) = fontaineTheta O p x := by
    intro σ f hf x
    have := hf x 1
    rw [map_one, mul_one] at this
    rw [← this]
    rfl
  have hxd : (inA (xi ε) : RL p O Λ) ^ N ∣ (inA (xi ε') : RL p O Λ) ^ N :=
    pow_dvd_pow_of_dvd (map_dvd _ ⟨(u : Ainf p O), hu.symm⟩) N
  have hmd : (inA (mu ε) : RL p O Λ) ^ N ∣ (inA (mu ε') : RL p O Λ) ^ N :=
    pow_dvd_pow_of_dvd (map_dvd _ ⟨(w : Ainf p O), hw.symm⟩) N
  have hunit : IsUnit (fontaineTheta O p (↑u⁻¹ : Ainf p O)) := (Units.isUnit u⁻¹).map _
  refine ⟨fun σ => algebraMap O C (fontaineTheta O p (↑u⁻¹ : Ainf p O)) ^ a σ * c σ, ?_, ?_, ?_⟩
  · obtain ⟨h1, g, hg, hg2⟩ := hD
    exact ⟨h1.trans hmd, g, hg, hg2.trans hxd⟩
  · intro σ f hf
    obtain ⟨h1, h2, s, t, hs, hst, ht⟩ := hH σ f hf
    refine ⟨h1, mul_ne_zero (pow_ne_zero _ (hunit.map _).ne_zero) h2, s,
      (inA (↑u⁻¹ : Ainf p O) : RL p O Λ) ^ a σ * t, hs, ?_, ?_⟩
    · rw [hst, ← hu, ← mul_assoc, ← mul_pow, ← map_mul, mul_assoc, Units.mul_inv, mul_one]
    · simp only [RingHom.comp_apply, map_mul, map_pow] at ht ⊢
      rw [key σ f hf, ht]
      ring
  · intro σ
    simp only [map_mul, map_pow, hv.one_of_isUnit hunit, one_pow, one_mul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorsOfConstantsClosedPointsOfOriginStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisorsOfConstantsClosedPoints_of_origin : GlobalTheory.VertUnits.DivConstOrigin → GlobalTheory.VertUnits.DivConstClosedPts := by
  first | (exact @GlobalTheory.VertUnits.divConstClosedPts_of_divConstOrigin) | (exact GlobalTheory.VertUnits.divConstClosedPts_of_divConstOrigin) | (intros; apply GlobalTheory.VertUnits.divConstClosedPts_of_divConstOrigin  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenDecompositionTraceMultiple
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem finrank_eig_eq_mul_of_trace_eq_mul :
    ∀ (C : Type) [Field C] [CharZero C] (O : Type) [CommRing O] [Algebra O C] (Λ : Type) [CommRing Λ]
      (h h' m : ℕ) (ρ : Λ → Matrix (Fin h) (Fin h) O) (ρ' : Λ → Matrix (Fin h') (Fin h') O),
      Function.Injective (algebraMap O C) → iSupIndep (fun σ : Λ →+* O => eig C ρ σ) →
      (⨆ σ : Λ →+* O, eig C ρ σ) = ⊤ → iSupIndep (fun σ : Λ →+* O => eig C ρ' σ) →
      (⨆ σ : Λ →+* O, eig C ρ' σ) = ⊤ → (∀ a, (ρ a).trace = (m : O) * (ρ' a).trace) →
      ∀ τ : Λ →+* O, Module.finrank C (eig C ρ τ) = m * Module.finrank C (eig C ρ' τ) := by
  intro C _ _ O _ _ Λ _ h h' m ρ ρ' hinj hind htop hind' htop' htr τ
  obtain ⟨hf, hsum⟩ := GlobalTheory.T.trace_eq_sum_eigen_multiplicities C O Λ h ρ hind htop
  obtain ⟨hf', hsum'⟩ := GlobalTheory.T.trace_eq_sum_eigen_multiplicities C O Λ h' ρ' hind' htop'
  classical
  let S : Finset (Λ →+* O) := insert τ (hf.toFinset ∪ hf'.toFinset)
  have hS : ∀ σ, eig C ρ σ ≠ ⊥ → σ ∈ S := fun σ hσ =>
    Finset.mem_insert_of_mem (Finset.mem_union_left _ (hf.mem_toFinset.2 hσ))
  have hS' : ∀ σ, eig C ρ' σ ≠ ⊥ → σ ∈ S := fun σ hσ =>
    Finset.mem_insert_of_mem (Finset.mem_union_right _ (hf'.mem_toFinset.2 hσ))
  let c : (Λ →+* O) → C := fun σ =>
    (Module.finrank C (eig C ρ σ) : C) - (m : C) * (Module.finrank C (eig C ρ' σ) : C)
  have key : ∀ a : Λ, ∑ σ ∈ S, c σ * algebraMap O C (σ a) = 0 := by
    intro a
    have e1 := hsum S hS a
    have e2 := hsum' S hS' a
    simp only [c, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
    rw [← e1, ← e2, htr a, map_mul, map_natCast, sub_self]
  have hc := GlobalTheory.T.ring_homs_linearly_independent C O Λ hinj S c key τ (Finset.mem_insert_self _ _)
  have : (Module.finrank C (eig C ρ τ) : C) = (m : C) * (Module.finrank C (eig C ρ' τ) : C) :=
    sub_eq_zero.1 hc
  exact_mod_cast this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleFaithfullyFlatRingHomBasicProperties
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem etFF_eq_toMorphismProperty :
    EtFF = RingHom.toMorphismProperty (fun f => RingHom.Etale f ∧ RingHom.FaithfullyFlat f) := by
  ext A B g; rfl

theorem etFF_iff_spec {A B : CommRingCat.{0}} (g : A ⟶ B) :
    EtFF g ↔ Etale (Spec.map g) ∧ Surjective (Spec.map g) := by
  have he : Etale (Spec.map g) ↔ g.hom.Etale := HasRingHomProperty.Spec_iff
  have hs : Surjective (Spec.map g) ↔ Function.Surjective (PrimeSpectrum.comap g.hom) := by
    rw [surjective_iff]; rfl
  rw [he, hs]
  change g.hom.Etale ∧ g.hom.FaithfullyFlat ↔ _
  rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
  constructor
  · rintro ⟨h1, -, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, (RingHom.Etale.iff_flat_and_formallyUnramified.1 h1).1, h2⟩

theorem etFF_isMultiplicative : EtFF.IsMultiplicative where
  id_mem A := ⟨RingHom.Etale.of_bijective Function.bijective_id,
    RingHom.FaithfullyFlat.of_bijective Function.bijective_id⟩
  comp_mem f g hf hg := by
    change (f ≫ g).hom.Etale ∧ (f ≫ g).hom.FaithfullyFlat
    rw [CommRingCat.hom_comp]
    exact ⟨RingHom.Etale.stableUnderComposition _ _ hf.1 hg.1,
      RingHom.FaithfullyFlat.stableUnderComposition _ _ hf.2 hg.2⟩

theorem etFF_isStableUnderCobaseChange : EtFF.IsStableUnderCobaseChange := by
  rw [etFF_eq_toMorphismProperty]
  exact RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.2
    (RingHom.Etale.isStableUnderBaseChange.and RingHom.FaithfullyFlat.isStableUnderBaseChange)

theorem etFF_respectsIso : EtFF.RespectsIso := by
  rw [etFF_eq_toMorphismProperty]
  exact RingHom.toMorphismProperty_respectsIso_iff.1
    (RingHom.Etale.respectsIso.and RingHom.FaithfullyFlat.respectsIso)

theorem finiteType_of_etFF {A B : CommRingCat.{0}} (g : A ⟶ B) (hg : EtFF g)
    (hA : Algebra.FiniteType ℤ A) : Algebra.FiniteType ℤ B := by
  letI := g.hom.toAlgebra
  haveI : Algebra.Etale A B := RingHom.Etale.toAlgebra hg.1
  exact Algebra.FiniteType.trans hA inferInstance

theorem etFF_basic :
    (EtFF.IsMultiplicative ∧ EtFF.IsStableUnderCobaseChange ∧ EtFF.RespectsIso) ∧
    (∀ (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g ↔ Etale (Spec.map g) ∧ Surjective (Spec.map g)) ∧
    ∀ (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g → Algebra.FiniteType ℤ A → Algebra.FiniteType ℤ B :=
  ⟨⟨etFF_isMultiplicative, etFF_isStableUnderCobaseChange, etFF_respectsIso⟩,
    fun _ _ g => etFF_iff_spec g, fun _ _ g hg hA => finiteType_of_etFF g hg hA⟩

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleQuotientOfEtalePuncturedStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_quotient_of_etale_punctured' : ∀ (R A : Type) [CommRing R] [IsLocalRing R] [CommRing A] [Algebra R A] (f : R) [IsLocalRing (R ⧸ Ideal.span {f})], (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → ∀ (P : Ideal (R ⧸ Ideal.span {f})) [P.IsPrime], P ≠ maximalIdeal (R ⧸ Ideal.span {f}) → Algebra.Etale (Localization.AtPrime P) (TensorProduct (R ⧸ Ideal.span {f}) (Localization.AtPrime P) (A ⧸ (Ideal.span {f}).map (algebraMap R A))) := by
  first | exact @GlobalTheory.etale_quotient_of_etale_punctured | exact GlobalTheory.etale_quotient_of_etale_punctured | (intros; apply GlobalTheory.etale_quotient_of_etale_punctured <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExactAtOfProd
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.WExactProd

theorem exactAt_of_prod {ι : Type} {c : ComplexShape ℕ} {K : HomologicalComplex AddCommGrpCat.{1} c}
    {L : ι → HomologicalComplex AddCommGrpCat.{1} c} (φ : ∀ i, K ⟶ L i)
    (hφ : ∀ n, Function.Bijective (fun (x : K.X n) (i : ι) => (φ i).f n x)) (p : ℕ)
    (hL : ∀ i, (L i).ExactAt p) : K.ExactAt p := by
  rw [HomologicalComplex.exactAt_iff, ShortComplex.ab_exact_iff]
  suffices key : ∀ z : K.X p, K.d p (c.next p) z = 0 → ∃ v : K.X (c.prev p), K.d (c.prev p) p v = z from key
  intro z hz
  have hcomm : ∀ i {q r : ℕ} (x : K.X q), (L i).d q r ((φ i).f q x) = (φ i).f r (K.d q r x) := by
    intro i q r x
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, (φ i).comm]
  have hw : ∀ i, ∃ w : (L i).X (c.prev p), (L i).d (c.prev p) p w = (φ i).f p z := by
    intro i
    have hex := hL i
    rw [HomologicalComplex.exactAt_iff, ShortComplex.ab_exact_iff] at hex
    refine hex ((φ i).f p z) ?_
    change (L i).d p (c.next p) ((φ i).f p z) = 0
    rw [hcomm, hz, map_zero]
  choose w hw using hw
  obtain ⟨v, hv⟩ := (hφ (c.prev p)).2 w
  refine ⟨v, ?_⟩
  apply (hφ p).1
  funext i
  change (φ i).f p (K.d (c.prev p) p v) = (φ i).f p z
  rw [← hcomm, ← hw i]
  exact congrArg _ (congrFun hv i)

theorem wexact_of_prod (T : Type 1) [Category.{0} T] (U : T) (X : CosimplicialObject T)
    (a : (CosimplicialObject.const T).obj U ⟶ X) (ι : Type) (M : ι → T ⥤ AddCommGrpCat.{1})
    (N : T ⥤ AddCommGrpCat.{1}) (π : ∀ i, N ⟶ M i)
    (hπ : ∀ V, Function.Bijective (fun (x : N.obj V) (i : ι) => (π i).app V x))
    (hM : ∀ i, WExact (M i) a) : WExact N a := by
  have nat : ∀ i {P Q : T} (f : P ⟶ Q) (x : N.obj P), (π i).app Q (N.map f x) = (M i).map f ((π i).app P x) := by
    intro i P Q f x
    exact ConcreteCategory.congr_hom ((π i).naturality f) x
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy
    apply (hπ U).1
    funext i
    apply (hM i).1
    have h := congrArg ((π i).app _) hxy
    rw [nat, nat] at h
    exact h
  · intro y hy
    have hx : ∀ i, ∃ x : (M i).obj U, (M i).map (a.app (SimplexCategory.mk 0)) x = (π i).app _ y := by
      intro i
      refine (hM i).2.1 ((π i).app _ y) ?_
      rw [← nat, ← nat, hy]
    choose x hx using hx
    obtain ⟨x', hx'⟩ := (hπ U).2 x
    refine ⟨x', ?_⟩
    apply (hπ _).1
    funext i
    change (π i).app _ (N.map (a.app (SimplexCategory.mk 0)) x') = (π i).app _ y
    rw [nat, ← hx i]
    exact congrArg _ (congrFun hx' i)
  · intro n
    refine exactAt_of_prod (fun i => (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).map
      (Functor.whiskerLeft X (π i))) (fun k => ?_) (n + 1) (fun i => (hM i).2.2 n)
    exact hπ (X.obj (SimplexCategory.mk k))

end GlobalTheory.EtC.WExactProd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdicCompletionNoetherianFlatCompleteStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adicCompletion_noetherian_flat_complete : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (I : Ideal B), ∃ (C : Type) (_ : CommRing C) (φ : B →+* C), IsNoetherianRing C ∧ φ.Flat ∧ IsAdicComplete (I.map φ) C ∧ ∀ (m : ℕ) (a : Ideal B), I ^ m ≤ a → (a.map φ).comap φ = a := by
  first | exact @GlobalTheory.AdicPackage.adicCompletion_package | exact GlobalTheory.AdicPackage.adicCompletion_package | (intros; apply GlobalTheory.AdicPackage.adicCompletion_package <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineCombinationSquareZeroLiftsChart
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SecGlue.CombEx

theorem chart_rebuild {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {S : Type} [CommRing S]
    (x : Sp S ⟶ Y) (hx : x ⁻¹ᵁ V = ⊤) : spMap (chartHom V x hx) ≫ hV.fromSpec = x := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec x hV (isAffineOpen_top (Sp S)) hx.ge
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  have e : CommRingCat.ofHom (chartHom V x hx) = x.appLE V ⊤ hx.ge ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).hom := rfl
  show Spec.map (CommRingCat.ofHom (chartHom V x hx)) ≫ hV.fromSpec = x
  rw [e, Spec.map_comp, Category.assoc, h, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
    Category.id_comp]

theorem top_of_comp {A B Y : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ Y) (V : Y.Opens) (h : g ⁻¹ᵁ V = ⊤) :
    (f ≫ g) ⁻¹ᵁ V = ⊤ :=
  top_le_iff.1 fun x _ => h.ge (show f x ∈ (⊤ : B.Opens) from trivial)

theorem fromSpec_comp_top {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {S : Type} [CommRing S]
    (χ : Γ(Y, V) →+* S) : (spMap χ ≫ hV.fromSpec) ⁻¹ᵁ V = ⊤ :=
  top_le_iff.1 fun _ _ => hV.range_fromSpec.subset ⟨_, rfl⟩

theorem chartHom_congr {Y : Scheme.{0}} (V : Y.Opens) {S : Type} [CommRing S] {x x' : Sp S ⟶ Y}
    (e : x = x') (h : x ⁻¹ᵁ V = ⊤) (h' : x' ⁻¹ᵁ V = ⊤) : chartHom V x h = chartHom V x' h' := by
  subst e; rfl

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map (CommRingCat.ofHom (g.comp f)) = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]; rfl

theorem chartHom_fromSpec {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {S : Type} [CommRing S]
    (χ : Γ(Y, V) →+* S) (hc : (spMap χ ≫ hV.fromSpec) ⁻¹ᵁ V = ⊤) :
    chartHom V (spMap χ ≫ hV.fromSpec) hc = χ := by
  have e := chart_rebuild hV (spMap χ ≫ hV.fromSpec) hc
  rw [cancel_mono] at e
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)

theorem chartHom_spMap_comp {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {S S' : Type} [CommRing S]
    [CommRing S'] (g : S →+* S') (x : Sp S ⟶ Y) (hx : x ⁻¹ᵁ V = ⊤) (h' : (spMap g ≫ x) ⁻¹ᵁ V = ⊤) :
    chartHom V (spMap g ≫ x) h' = g.comp (chartHom V x hx) := by
  have e : spMap (chartHom V (spMap g ≫ x) h') ≫ hV.fromSpec =
      spMap (g.comp (chartHom V x hx)) ≫ hV.fromSpec := by
    rw [chart_rebuild, spMap_comp', Category.assoc, chart_rebuild]
  rw [cancel_mono] at e
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)

end GlobalTheory.SecGlue.CombEx

namespace GlobalTheory.SecGlue.CombEx

theorem mul_eq_zero_of_sq {S T : Type} [CommRing S] [CommRing T] (q : S →+* T) (hsq : RingHom.ker q ^ 2 = ⊥)
    {s t : S} (hs : q s = 0) (ht : q t = 0) : s * t = 0 := by
  have h : s * t ∈ RingHom.ker q ^ 2 := by
    rw [sq]; exact Ideal.mul_mem_mul (RingHom.mem_ker.2 hs) (RingHom.mem_ker.2 ht)
  rw [hsq] at h
  exact (Submodule.mem_bot S).1 h

def combHom {A S T : Type} [CommRing A] [CommRing S] [CommRing T] (q : S →+* T) (hsq : RingHom.ker q ^ 2 = ⊥)
    {ι : Type} [Fintype ι] (φ : A →+* S) (ψ : ι → (A →+* S)) (a : ι → S) (hq : ∀ i, q.comp (ψ i) = q.comp φ) :
    A →+* S where
  toFun x := φ x + ∑ i, a i * (ψ i x - φ x)
  map_one' := by simp
  map_zero' := by simp
  map_add' x y := by
    simp only [map_add, mul_sub, mul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring
  map_mul' x y := by
    have hd : ∀ i z, q (ψ i z - φ z) = 0 := fun i z => by
      rw [map_sub, ← RingHom.comp_apply, hq i, RingHom.comp_apply, sub_self]
    have hD : ∀ z, q (∑ i, a i * (ψ i z - φ z)) = 0 := fun z => by
      simp only [map_sum, map_mul, hd, mul_zero, Finset.sum_const_zero]
    have e1 : ∀ i, ψ i (x * y) - φ (x * y) = φ x * (ψ i y - φ y) + (ψ i x - φ x) * φ y := fun i => by
      have := mul_eq_zero_of_sq q hsq (hd i x) (hd i y)
      rw [map_mul, map_mul]; linear_combination this
    have e2 := mul_eq_zero_of_sq q hsq (hD x) (hD y)
    have s : ∑ i, a i * (ψ i (x * y) - φ (x * y)) =
        φ x * ∑ i, a i * (ψ i y - φ y) + φ y * ∑ i, a i * (ψ i x - φ x) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [e1 i]; ring
    show φ (x * y) + ∑ i, a i * (ψ i (x * y) - φ (x * y)) =
      (φ x + ∑ i, a i * (ψ i x - φ x)) * (φ y + ∑ i, a i * (ψ i y - φ y))
    linear_combination s + map_mul φ x y - e2

theorem combHom_apply {A S T : Type} [CommRing A] [CommRing S] [CommRing T] (q : S →+* T)
    (hsq : RingHom.ker q ^ 2 = ⊥) {ι : Type} [Fintype ι] (φ : A →+* S) (ψ : ι → (A →+* S)) (a : ι → S)
    (hq : ∀ i, q.comp (ψ i) = q.comp φ) (x : A) :
    combHom q hsq φ ψ a hq x = φ x + ∑ i, a i * (ψ i x - φ x) := rfl

theorem comp_combHom {A S T : Type} [CommRing A] [CommRing S] [CommRing T] (q : S →+* T)
    (hsq : RingHom.ker q ^ 2 = ⊥) {ι : Type} [Fintype ι] (φ : A →+* S) (ψ : ι → (A →+* S)) (a : ι → S)
    (hq : ∀ i, q.comp (ψ i) = q.comp φ) : q.comp (combHom q hsq φ ψ a hq) = q.comp φ := by
  ext x
  have hd : ∀ i, q (ψ i x - φ x) = 0 := fun i => by
    rw [map_sub, ← RingHom.comp_apply, hq i, RingHom.comp_apply, sub_self]
  simp only [RingHom.comp_apply, combHom_apply, map_add, map_sum, map_mul, hd, mul_zero,
    Finset.sum_const_zero, add_zero]

theorem combHom_comp_eq {R A S T : Type} [CommRing R] [CommRing A] [CommRing S] [CommRing T] (q : S →+* T)
    (hsq : RingHom.ker q ^ 2 = ⊥) {ι : Type} [Fintype ι] (φ : A →+* S) (ψ : ι → (A →+* S)) (a : ι → S)
    (hq : ∀ i, q.comp (ψ i) = q.comp φ) (θ : R →+* A) (hθ : ∀ i, (ψ i).comp θ = φ.comp θ) :
    (combHom q hsq φ ψ a hq).comp θ = φ.comp θ := by
  ext r
  have h : ∀ i, ψ i (θ r) = φ (θ r) := fun i => RingHom.congr_fun (hθ i) r
  simp only [RingHom.comp_apply, combHom_apply, h, sub_self, mul_zero, Finset.sum_const_zero, add_zero]

theorem exists_comb : ∀ (Y : Scheme.{0}) (V : Y.Opens), IsAffineOpen V →
    ∀ (S T : Type) [CommRing S] [CommRing T] (q : S →+* T), Function.Surjective q → RingHom.ker q ^ 2 = ⊥ →
    ∀ (ι : Type) [Fintype ι] (u : Sp S ⟶ Y) (w : ι → (Sp S ⟶ Y)) (a : ι → S), u ⁻¹ᵁ V = ⊤ →
    (∀ i, spMap q ≫ w i = spMap q ≫ u) →
    ∃ c : Sp S ⟶ Y, GlobalTheory.SecGlue.IsCombIn V u c w a ∧ spMap q ≫ c = spMap q ≫ u ∧
      ∀ (R' : Type) [CommRing R'] (p : Y ⟶ Sp R'), (∀ i, w i ≫ p = u ≫ p) → c ≫ p = u ≫ p := by
  intro Y V hV S T _ _ q hqs hsq ι _ u w a hu hw
  have hwV : ∀ i, w i ⁻¹ᵁ V = ⊤ := fun i => (GlobalTheory.SecGlue.preimage_eq_of_comp_eq_of_sqZero S T q hqs hsq Y (w i) u (hw i) V).trans hu
  have hq : ∀ i, q.comp (chartHom V (w i) (hwV i)) = q.comp (chartHom V u hu) := fun i => by
    rw [← chartHom_spMap_comp hV q (w i) (hwV i) (top_of_comp _ _ V (hwV i)),
      ← chartHom_spMap_comp hV q u hu (top_of_comp _ _ V hu)]
    exact chartHom_congr V (hw i) _ _
  let χ := combHom q hsq (chartHom V u hu) (fun i => chartHom V (w i) (hwV i)) a hq
  have hc := fromSpec_comp_top hV χ
  refine ⟨spMap χ ≫ hV.fromSpec, ⟨hu, hc, hwV, fun x => ?_⟩, ?_, ?_⟩
  · rw [chartHom_fromSpec hV χ hc]; rfl
  · calc spMap q ≫ spMap χ ≫ hV.fromSpec = spMap (q.comp χ) ≫ hV.fromSpec := by
          rw [spMap_comp', Category.assoc]
      _ = spMap (q.comp (chartHom V u hu)) ≫ hV.fromSpec := by rw [comp_combHom]
      _ = spMap q ≫ u := by rw [spMap_comp', Category.assoc, chart_rebuild]
  · intro R' _ p hp
    let θ : CommRingCat.of R' ⟶ Γ(Y, V) := Spec.preimage (hV.fromSpec ≫ p)
    have key : ∀ (x : Sp S ⟶ Y) (hx : x ⁻¹ᵁ V = ⊤), x ≫ p = spMap ((chartHom V x hx).comp θ.hom) := by
      intro x hx
      calc x ≫ p = spMap (chartHom V x hx) ≫ hV.fromSpec ≫ p := by rw [← Category.assoc, chart_rebuild]
        _ = spMap (chartHom V x hx) ≫ Spec.map θ := by rw [Spec.map_preimage]
        _ = spMap ((chartHom V x hx).comp θ.hom) := by
          show _ = Spec.map (CommRingCat.ofHom _)
          rw [show CommRingCat.ofHom ((chartHom V x hx).comp θ.hom) = θ ≫ CommRingCat.ofHom (chartHom V x hx)
            from rfl, Spec.map_comp]
    have hθ : ∀ i, (chartHom V (w i) (hwV i)).comp θ.hom = (chartHom V u hu).comp θ.hom := fun i => by
      have e := (key (w i) (hwV i)).symm.trans ((hp i).trans (key u hu))
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
    rw [key _ hc, key u hu, chartHom_fromSpec hV χ hc]
    exact congrArg spMap (combHom_comp_eq q hsq _ _ a hq θ.hom hθ)

end GlobalTheory.SecGlue.CombEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenCoverAffineOpenSpecStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basicOpen_cover_affineOpen_spec : ∀ (S : Type) [CommRing S] (Y : Scheme.{0}) (u : Sp S ⟶ Y),
    ∃ (n : ℕ) (s : Fin n → S) (W : Fin n → Y.Opens), Ideal.span (Set.range s) = ⊤ ∧
      (∀ i, IsAffineOpen (W i)) ∧ ∀ i, (spMap (algebraMap S (Localization.Away (s i))) ≫ u) ⁻¹ᵁ W i = ⊤ := by
  first | exact @GlobalTheory.SecGlue.exists_basicOpen_cover_affine | exact GlobalTheory.SecGlue.exists_basicOpen_cover_affine | (intros; apply GlobalTheory.SecGlue.exists_basicOpen_cover_affine <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisQuotientLatticeEigen
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem eigenQuotient_basis_detLattice_eq_span_wedge : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (Λ : Type) [CommRing Λ] (h N : ℕ), v.Integers O → ∀ (ρ : Λ → Matrix (Fin h) (Fin h) O) (τ : Λ →+* O), iSupIndep (fun σ : Λ →+* O => eig C ρ σ) → (⨆ σ : Λ →+* O, eig C ρ σ) = ⊤ → Module.finrank C (eig C ρ τ) = N → ∃ b : Module.Basis (Fin N) C (eig C ρ τ), quotLattice C ρ τ = (Submodule.span O (Set.range b) : Set (eig C ρ τ)) ∧ Module.finrank C (detLine C ρ τ N) = 1 ∧ exteriorPower.ιMulti C N b ≠ 0 ∧ detLattice C ρ τ N = Submodule.span O {exteriorPower.ιMulti C N b} := by
  intro C _ v O _ _ Λ _ h N hv ρ τ hind hsup hrank
  obtain ⟨π, hπ1, -, hq⟩ := GlobalTheory.T.eigen_projection_quotient_lattice C O Λ h ρ τ hind hsup
  have hsurj : Function.Surjective π := fun x => ⟨(x : Fin h → C), hπ1 x⟩
  obtain ⟨g, hgC, hgO⟩ := GlobalTheory.T.exists_spanning_image_lattice C O (eig C ρ τ) h π hsurj
  obtain ⟨b, hb⟩ := GlobalTheory.T.exists_basis_of_lattice_span C v O (eig C ρ τ) h N g hv hgC hrank
  have hQ : quotLattice C ρ τ = (Submodule.span O (Set.range b) : Set (eig C ρ τ)) := by
    rw [hq, hgO, hb]
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.exteriorPower_basis_lattice_principal C O (eig C ρ τ) N b
  refine ⟨b, hQ, h1, h2, ?_⟩
  unfold detLattice
  rw [hQ]
  exact h3

end GlobalTheory
end

