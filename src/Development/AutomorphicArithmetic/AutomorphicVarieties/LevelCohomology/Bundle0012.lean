import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.QuotRepMk
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0011

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.KatoConj
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published.Kato

theorem UpperTheory.V.X.Kato.conj :
    ∀ (l : ℕ) [Fact l.Prime] (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (n : ℕ) (r r' : G F Ω →* GL (Fin n) (Qbar l)), RepIso r r' → BlochKatoSelmerVanishes l (Loc.colRep r) → BlochKatoSelmerVanishes l (Loc.colRep r') := by
  intro l _ F Ω _ _ _ _ n r r' ⟨P, hP⟩ h c hc hbk
  let f : (Fin n → Qbar l) →ₗ[ℚ_[l]] (Fin n → Qbar l) :=
    (Matrix.mulVecLin ((P⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l))).restrictScalars ℚ_[l]
  have hfa : ∀ x, f x = ((P⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)).mulVec x := fun _ => rfl
  have hcol : ∀ (ρ : G F Ω →* GL (Fin n) (Qbar l)) g x,
      Loc.colRep ρ g x = (ρ g : Matrix (Fin n) (Fin n) (Qbar l)).mulVec x := fun _ _ _ => rfl
  have hf : ∀ g x, f (Loc.colRep r' g x) = Loc.colRep r g (f x) := by
    intro g x
    rw [hfa, hfa, hcol, hcol, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, hP]
    congr 2
    group
  have hinj : Function.Injective f := by
    intro x y hxy
    have := congrArg ((P : Matrix (Fin n) (Fin n) (Qbar l)).mulVec) hxy
    rwa [hfa, hfa, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec, Matrix.one_mulVec] at this
  have hsurj : Function.Surjective f := by
    intro y
    refine ⟨(P : Matrix (Fin n) (Fin n) (Qbar l)).mulVec y, ?_⟩
    rw [hfa, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hcont : Continuous (fun g => f (c g)) := by
    simp only [hfa]
    exact continuous_const.matrix_mulVec hc.1
  have hz : (fun g => f (c g)) ∈ Z1 (Loc.colRep r) := by
    refine ⟨hcont, fun g g' => ?_⟩
    have h1 := congrArg f (hc.2 g g')
    simpa only [map_add, hf] using h1
  obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 (h _ hz (UpperTheory.V.X.Kato.bkMap l F Ω _ _ _ _ _ _ f hf c hcont hbk))
  obtain ⟨m', rfl⟩ := hsurj m
  refine (mem_coboundaries1 _ _).2 ⟨m', fun g => hinj ?_⟩
  have := hm g
  simp only [map_sub, hf]
  exact this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.KatoDesc
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published.Kato

theorem UpperTheory.V.X.Kato.desc :
    ∀ (l : ℕ) [Fact l.Prime] (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (E : IntermediateField ℚ_[l] (Qbar l)) [FiniteDimensional ℚ_[l] ↥E] (n : ℕ) (r : G F Ω →* GL (Fin n) ↥E), BlochKatoSelmerVanishes l (Loc.colRep r) → BlochKatoSelmerVanishes l (Loc.colRep (toBar r)) := by
  intro l _ F Ω _ _ _ _ _ E _ n r h c hc hbk
  haveI : IsGalois F Ω := {}
  obtain ⟨E', hE', hle, hmem⟩ := UpperTheory.V.X.Kato.finExt l (G F Ω) E n r c hc
  obtain ⟨d, ε, π, hsum, hcont⟩ := UpperTheory.V.X.Kato.basis l E E' hle
  obtain ⟨hcc, hcoc⟩ := (mem_Z1_iff_cocycle _ _).1 hc
  let f : Fin d → ((Fin n → Qbar l) →ₗ[ℚ_[l]] (Fin n → ↥E)) := fun i =>
    ((π i).restrictScalars ℚ_[l]).compLeft (Fin n)
  have hf : ∀ i g x, f i (Loc.colRep (toBar r) g x) = Loc.colRep r g (f i x) := by
    intro i g x
    funext j
    show π i (∑ k, ((r g : Matrix (Fin n) (Fin n) ↥E) j k : Qbar l) * x k) =
      ∑ k, (r g : Matrix (Fin n) (Fin n) ↥E) j k * π i (x k)
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact (π i).map_smul ((r g : Matrix (Fin n) (Fin n) ↥E) j k) (x k)
  have hfc : ∀ i, Continuous fun g => f i (c g) := fun i =>
    continuous_pi fun j =>
      (hcont i).comp_continuous ((continuous_apply j).comp hcc) fun g => hmem g j
  have hB : ∀ i, ∃ m : Fin n → ↥E, ∀ g, f i (c g) = Loc.colRep r g m - m := fun i => by
    refine (mem_coboundaries1 _ _).1 (h (fun g => f i (c g)) ((mem_Z1_iff_cocycle _ _).2 ⟨hfc i, fun g g' => ?_⟩) ?_)
    · rw [hcoc, map_add, hf]
    · exact UpperTheory.V.X.Kato.bkMap l F Ω _ _ _ _ _ _ (f i) (hf i) c (hfc i) hbk
  choose m hm using hB
  refine (mem_coboundaries1 _ _).2 ⟨fun j => ∑ i, ε i * (m i j : Qbar l), fun g => ?_⟩
  funext j
  have h1 : ∀ i, (π i (c g j) : Qbar l) =
      (∑ k, ((r g : Matrix (Fin n) (Fin n) ↥E) j k : Qbar l) * (m i k : Qbar l)) - (m i j : Qbar l) := fun i => by
    have h2 : π i (c g j) = (∑ k, (r g : Matrix (Fin n) (Fin n) ↥E) j k * m i k) - m i j := congrFun (hm i g) j
    rw [h2]
    push_cast
    rfl
  show c g j = (∑ k, ((r g : Matrix (Fin n) (Fin n) ↥E) j k : Qbar l) * ∑ i, ε i * (m i k : Qbar l)) -
    ∑ i, ε i * (m i j : Qbar l)
  rw [hsum _ (hmem g j)]
  simp only [h1, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring
end

