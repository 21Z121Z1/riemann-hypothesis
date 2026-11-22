import Mathlib
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.X0OfStarCondition
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0022
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0027
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LatticeDataThicknessBound

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsRegAlgTwistOfHalfIntegral
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong

namespace GlobalTheory.Row9

def plusChars {Γ K : Type} [Group Γ] [Field K] {n k : ℕ} (r : Γ →* GL (Fin n) K) (ν : Fin k → (Γ →* Kˣ)) :
    Γ →* GL (Fin (n + k)) K :=
  MonoidHom.toHomUnits
    ((Matrix.reindexAlgEquiv K K finSumFinEquiv).toMonoidHom.comp
      { toFun := fun g => Matrix.fromBlocks (r g : Matrix (Fin n) (Fin n) K) 0 0 (Matrix.diagonal fun i => ((ν i g : Kˣ) : K))
        map_one' := by simp [Matrix.fromBlocks_one]
        map_mul' := fun g h => by simp [Matrix.fromBlocks_multiply, Matrix.diagonal_mul_diagonal] })

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [IsCMField E]

def FieldOK (l : ℕ) (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  (∃ x : E, ∃ d : ℕ, 0 < d ∧ x ^ 2 = -(d : E)) ∧ Even (Module.finrank ℚ (maximalRealSubfield E)) ∧
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) ∧
    (∀ w : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → IsSplitAt w) ∧
    ∃ w₁ w₂ w₃ : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w₁.asIdeal ∧ ((l : ℕ) : 𝓞 E) ∈ w₂.asIdeal ∧
      ((l : ℕ) : 𝓞 E) ∈ w₃.asIdeal ∧ Apart w₁ w₂ ∧ Apart w₁ w₃ ∧ Apart w₂ w₃

def SatU {a : ℕ} (U : Submodule ℂ (UA E a → ℂ)) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ) : Prop :=
  IsSplitAt w ∧ ∃ σ : SmIrr (GL (Fin a) (w.adicCompletion E)),
    IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ ∧ GlobalTheory.LFun.HasSatGL w σ.ρ B

def SphG (c : GlobalTheory.RoadU.Sph) {l : ℕ} [Fact l.Prime] {a : ℕ} (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l))
    (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ) (inf : (E →+* ℂ) → Multiset ℂ) : Prop :=
  match c with
  | .unr => ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → UpperTheory.V.Af.FrobEig ι r w (UpperTheory.V.Af.algSat a (normV w) B)
  | .dR => ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (A : ValuationSubring Ω), IsPlaceOver A w →
      ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O), Pst.Induces Bw →
      IsdRAt P Bw (r.comp (Dec (F := E) A).subtype) ∧
        ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' → ∀ J : Multiset ℤ,
          J.map (fun n : ℤ => (n : ℂ)) = (inf (ι.toRingHom.comp τ)).map (fun z => ((a : ℂ) - 1) / 2 - z) →
          IsJumpsAt P Bw (r.comp (Dec (F := E) A).subtype) τ J
  | .crys => ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (A : ValuationSubring Ω), IsPlaceOver A w →
      ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O), Pst.Induces Bw →
      IsCrysAt P Bw (r.comp (Dec (F := E) A).subtype)
  | .phi => ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw),
      ∀ g : Weil h, (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)).charPol g = (GlobalTheory.RoadU.satWD h a B).charPol g

def CoreUFor (m : ℕ) : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ), FieldOK l E →
    ∀ U : Submodule ℂ (UA E m → ℂ), IsAutRepU U → ∀ lam : (E →+* ℂ) → DomWeight m, (∀ τ, HasWeightAt U τ (lam τ)) →
    ∃ r : G E Ω →* GL (Fin m) (Qbar l), Continuous r ∧ IsSSRep r ∧
      ∀ w B, SatU U w B → ∀ c, SphG c ι r w B fun τ => infOfWeight (lam τ)

def CoreU : Prop := ∀ m : ℕ, Odd m → CoreUFor m

def HalfIntegral {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (α : CG K 1) : Prop :=
  ∀ τ, ∀ z ∈ α.infChar τ, ∃ k : ℤ, z = (k : ℂ) + 1 / 2

def ThetaPlus : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) →
    ∀ n : ℕ, Even n → 1 ≤ n → ∀ U : Submodule ℂ (UA E n → ℂ), IsAutRepU U → ∀ lam : (E →+* ℂ) → DomWeight n,
    (∀ τ, HasWeightAt U τ (lam τ)) → ∀ (w₁ : HeightOneSpectrum (𝓞 E)), IsSplitAt w₁ → ∀ Y : Finset ℂ,
    ∃ (α β : CuspSub E 1) (a₁ c₁ : ℂˣ), α.IsCsd ∧ β.IsCsd ∧ HalfIntegral (CG.mk α) ∧ (CG.mk β).IsRegAlg ∧
      (CG.mk α).HasSat w₁ {a₁} ∧ (CG.mk β).HasSat w₁ {c₁} ∧ ((c₁ : ℂ) / a₁) ∉ Y ∧
      ∃ (U' : Submodule ℂ (UA E (2 * n + 1) → ℂ)) (lam' : (E →+* ℂ) → DomWeight (2 * n + 1)), IsAutRepU U' ∧
        (∀ τ, HasWeightAt U' τ (lam' τ)) ∧
        (∀ τ x y, (CG.mk α).infChar τ = {x} → (CG.mk β).infChar τ = {y} →
          infOfWeight (lam' τ) = (infOfWeight (lam τ)).map (· + x) +
            (Multiset.range (n + 1)).map fun j : ℕ => y + (j : ℂ) - (n : ℂ) / 2) ∧
        ∀ w B (a c : ℂˣ), SatU U w B → (CG.mk α).HasSat w {a} → (CG.mk β).HasSat w {c} →
          ∃ B', SatU U' w B' ∧ B'.map (fun b : ℂˣ => (b : ℂ)) =
            B.map (fun b : ℂˣ => (b : ℂ) * a) + (Multiset.range (n + 1)).map fun j : ℕ => (c : ℂ) * (normV w : ℂ) ^ ((j : ℤ) - (n / 2 : ℕ))

def CoreGL : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ), FieldOK l E → ∀ a : ℕ, 1 ≤ a → ∀ π : CuspSub E a,
    InScope .csd l π (quadChar E ^ a) →
    ∃ r : G E Ω →* GL (Fin a) (Qbar l), SplitAtt π ι r ∧
      ∀ w B, IsSplitAt w → (CG.mk π).HasSat w B → ∀ c, GlobalTheory.RoadU.SphAt c π ι r w B

namespace Basic

section Sum

variable {Γ K : Type} [Group Γ] [Field K] {n k : ℕ} (r : Γ →* GL (Fin n) K) (ν : Fin k → (Γ →* Kˣ))

end Sum

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]

theorem not_halfIntegral_of_isRegAlg {α : CG K 1} (h : α.IsRegAlg) : ¬ HalfIntegral α := fun h' => by
  obtain ⟨τ⟩ : Nonempty (K →+* ℂ) := inferInstance
  obtain ⟨x, hx⟩ := Multiset.card_eq_one.1 (α.card_infChar τ)
  obtain ⟨k, hk⟩ := (h τ).2 x (by rw [hx]; exact Multiset.mem_singleton_self x)
  obtain ⟨m, hm⟩ := h' τ x (by rw [hx]; exact Multiset.mem_singleton_self x)
  have e : (((2 * (k - m) : ℤ)) : ℂ) = ((1 : ℤ) : ℂ) := by
    push_cast at hk ⊢
    linear_combination 2 * hm - 2 * hk
  have := Int.cast_injective e
  omega

def liftWeight {n : ℕ} (lam : DomWeight n) (t : ℤ) (ht : ∀ k, t ≤ lam.w k) : DomWeight (2 * n + 1) where
  w i := if h : (i : ℕ) < n then lam.w ⟨i, h⟩ - t else 0
  anti i j hij := by
    have hij' : (i : ℕ) ≤ j := hij
    dsimp only
    split_ifs with h1 h2 h2
    · have := lam.anti (show (⟨i, h2⟩ : Fin n) ≤ ⟨j, h1⟩ from hij')
      omega
    · omega
    · have := ht ⟨i, h2⟩
      omega
    · exact le_rfl

theorem infOfWeight_liftWeight {n : ℕ} (lam : DomWeight n) (t : ℤ) (ht : ∀ k, t ≤ lam.w k) :
    infOfWeight (liftWeight lam t ht) = (infOfWeight lam).map (· + (((n : ℂ) + 1) / 2 - t)) +
      (Multiset.range (n + 1)).map fun j : ℕ => -(n : ℂ) / 2 + (j : ℂ) - (n : ℂ) / 2 := by
  let f : ℕ → ℂ := fun i => ((if h : i < n then lam.w ⟨i, h⟩ - t else 0 : ℤ) : ℂ) + ((n : ℂ) - i)
  have h1 : infOfWeight (liftWeight lam t ht) = (Multiset.range (n + (n + 1))).map f := by
    rw [show n + (n + 1) = 2 * n + 1 by ring, ← Finset.range_val, ← Nat.Iio_eq_range, ← Fin.map_valEmbedding_univ,
      Finset.map_val, Multiset.map_map]
    refine Multiset.map_congr rfl fun i _ => ?_
    simp only [liftWeight, f, Function.comp, Fin.valEmbedding_apply]
    push_cast
    ring
  rw [h1, Multiset.range_add, Multiset.map_add, Multiset.map_map]
  congr 1
  · rw [← Finset.range_val, ← Nat.Iio_eq_range, ← Fin.map_valEmbedding_univ, Finset.map_val, Multiset.map_map, infOfWeight,
      Multiset.map_map]
    refine Multiset.map_congr rfl fun i _ => ?_
    simp only [f, Function.comp, Fin.valEmbedding_apply, dif_pos i.2]
    push_cast
    ring
  · have h2 : Multiset.range (n + 1) = (Multiset.range (n + 1)).map (n - ·) := by
      have := congrArg Finset.val (Finset.range_image_pred_top_sub (n + 1))
      rw [Finset.image_val_of_injOn] at this
      · simpa using this.symm
      · intro a ha b hb hab
        simp only [Finset.coe_range, Set.mem_Iio] at ha hb hab
        omega
    conv_rhs => rw [h2, Multiset.map_map]
    refine Multiset.map_congr rfl fun i hi => ?_
    have hi' : i ≤ n := Nat.lt_succ_iff.1 (Multiset.mem_range.1 hi)
    simp only [f, Function.comp, dif_neg (show ¬ n + i < n by omega), Nat.cast_sub hi']
    push_cast
    ring

example : infOfWeight (liftWeight (⟨0, antitone_const⟩ : DomWeight 2) 0 fun _ => le_rfl) =
    (infOfWeight (⟨0, antitone_const⟩ : DomWeight 2)).map (· + 3 / 2) +
      (Multiset.range 3).map fun j : ℕ => (-1 : ℂ) + (j : ℂ) - 1 := by
  rw [infOfWeight_liftWeight]
  norm_num

example : ¬ HalfIntegral (CG.ofChar (1 : HChar K)) :=
  not_halfIntegral_of_isRegAlg ((CG.isRegAlg_ofChar _).2 fun τ => ⟨0, by simp [CG.expo_one]⟩)

example (h : CoreU) : CoreUFor 5 := h 5 (by decide)

end Basic

end GlobalTheory.Row9

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LimWPhi
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong MvPolynomial

namespace GlobalTheory.CongL

def DGen (a : ℕ) : MvPolynomial (Fin a) ℤ :=
  (∏ i : Fin a, ∏ j : Fin a, if i = j then 1 else ∏ c ∈ Finset.range a, (X i ^ (c + 1) - X j ^ (c + 1))) *
  (∏ i : Fin a, ∏ j : Fin a, ∏ k : Fin a, if j = i ∨ j = k then 1 else (X i * X k - X j ^ 2)) *
  (∏ m ∈ (Finset.univ : Finset (Fin a → Fin (a + 1))).filter (fun m => (∑ i, (m i : ℕ)) = a ∧ m ≠ fun _ => 1),
    ((∏ i, X i ^ (m i : ℕ)) - ∏ i, X i))

def GapJ (a : ℕ) (J : Multiset ℤ) : Prop :=
  ∀ i : ℕ, i + 1 < a →
    (J.sort (· ≤ ·)).getD (i + 1) 0 - (J.sort (· ≤ ·)).getD 0 0 > (a : ℤ) * ((J.sort (· ≤ ·)).getD i 0 - (J.sort (· ≤ ·)).getD 0 0)

def WtLac : SeedWtU := fun E _ _ _ l _ a ι w₀ v' U U' =>
  SameWtOff ι w₀ v' U U' ∧ ∃ τ₀ : E →+* ℂ, OverPl ι τ₀ v' ∧ ∀ lam, HasWeightAt U' τ₀ lam → ∀ J : Multiset ℤ,
    J.map (fun n : ℤ => (n : ℂ)) = (infOfWeight lam).map (fun z => ((a : ℂ) - 1) / 2 - z) → GapJ a J

def FinitenessCondition : Prop := UnitaryWeightConditionWithWeights GlobalTheory.CongW.TyEll (GlobalTheory.CongW.GenOf DGen) WtLac

def CongFin : Prop := CongUW3 GlobalTheory.CongW.TyEll (GlobalTheory.CongW.GenOf DGen) WtLac

def LimFin : Prop := LimWU3

def LimWPhi : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ d : ℕ, ImQ E d → SqAt d l →
    ∀ π : CuspSub E a, InScope .csd l π (quadChar E ^ a) →
    ∀ w₀ v' : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal → ((l : ℕ) : 𝓞 E) ∈ v'.asIdeal → Apart v' w₀ →
    ∃ r : G E Ω →* GL (Fin a) (Qbar l), Continuous r ∧ IsSSRep r ∧
      (∀ w, UsPl d w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ B, (CG.mk π).HasSat w B →
        UpperTheory.V.Af.FrobEig ι r w (UpperTheory.V.Af.algSat a (normV w) B)) ∧
      (∀ w, ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → Apart w w₀ → Apart w v' → (∃ B, (CG.mk π).HasSat w B) →
        ClauseAt .crys π ι r w ∧ ClauseAt .dR π ι r w) ∧
      (∀ w, ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → Apart w w₀ → Apart w v' → ∀ B, (CG.mk π).HasSat w B →
        GlobalTheory.RoadU.SphAt .phi π ι r w B)

example : GapJ 1 0 := fun i hi => absurd hi (by omega)

end GlobalTheory.CongL

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PstIneAt
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.PositiveInequalities

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ} [IsCMField E]

def PstIneAt (π : CuspSub E a) (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l)) (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw),
      IsPstAt P Bw (r.comp (Dec (F := E) A).subtype) ∧
      (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)).mono0 ∧
      ∀ rc : IrrGL (w.adicCompletion E) → WD h, UpperTheory.Zero.LLC.IsRecT h rc → ∀ σ, π.IsLocComp w σ →
        ∀ t : Ine (F := E) A, (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)).charPol (ineIncl h t) =
          (rc (algNorm σ)).charPol (ineIncl h t)

def RowPst : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)),
    InScope .all l π χ → ∀ r : G E Ω →* GL (Fin a) (Qbar l), Weak π ι r →
    ∀ w : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → GlobalTheory.RoadU.MixAt π w → PstIneAt π ι r w

end GlobalTheory.PositiveInequalities

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RowStarCoreAtUOfRowStarCoreU
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong

namespace GlobalTheory.RoadW

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [IsCMField E] {l : ℕ} [Fact l.Prime] {a : ℕ}

def SatAtU (U : Submodule ℂ (UA E a → ℂ)) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ) : Prop :=
  ∃ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ ∧
    GlobalTheory.LGrp.HasSatakeGL σ.ρ B

def HasRepU (ι : Qbar l ≃+* ℂ) (U : Submodule ℂ (UA E a → ℂ)) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (r : G E Ω →* GL (Fin a) (Qbar l)) : Prop :=
  Continuous r ∧ IsSSRep r ∧ ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → w ∉ S → ∀ B : Multiset ℂˣ, SatAtU U w B →
    (((l : ℕ) : 𝓞 E) ∉ w.asIdeal → UpperTheory.V.Af.FrobEig ι r w (UpperTheory.V.Af.algSat a (normV w) B)) ∧
    (((l : ℕ) : 𝓞 E) ∈ w.asIdeal → SstAt r w ∧ GlobalTheory.CongL.CrysDRU U ι r w ∧
      ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
        (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O)
        (hj : Pst.Induces Bw), (IsCrysAt P Bw (r.comp (Dec (F := E) A).subtype)) ∧
        ∀ g : Weil h, (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)).charPol g = (GlobalTheory.RoadU.satWD h a B).charPol g)

def RowStarCoreU : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (S T : Finset (HeightOneSpectrum (𝓞 E))), NonSplitSet T → (∀ w ∈ S, IsSplitAt w) →
    ∀ U : Submodule ℂ (UA E a → ℂ), IsAutRepU U → (∀ w, ¬ IsSplitAt w → w ∉ T → IsUnramU U w) →
      ∃ r : G E Ω →* GL (Fin a) (Qbar l), HasRepU ι U S r

def UnitaryBaseConditions : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (S T : Finset (HeightOneSpectrum (𝓞 E))), NonSplitSet T → (∀ w ∈ S, IsSplitAt w) →
    ∀ w₀ : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal → IsSplitAt w₀ →
    w₀ ∈ S → ∀ U : Submodule ℂ (UA E a → ℂ), IsAutRepU U → (∀ w, ¬ IsSplitAt w → w ∉ T → IsUnramU U w) → ScU U w₀ →
      ∃ r : G E Ω →* GL (Fin a) (Qbar l), HasRepU ι U S r

def RowStarCoreAtU : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (S T : Finset (HeightOneSpectrum (𝓞 E))), NonSplitSet T → (∀ w ∈ S, IsSplitAt w) →
    ∀ w₀ : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal → IsSplitAt w₀ → (∀ w, ¬ Apart w w₀ → w ∈ S) →
    ∀ U : Submodule ℂ (UA E a → ℂ), IsAutRepU U → (∀ w, ¬ IsSplitAt w → w ∉ T → IsUnramU U w) →
      ∃ r : G E Ω →* GL (Fin a) (Qbar l), HasRepU ι U S r

def LimitStepU : Prop := CongU → UnitaryBaseConditions → RowStarCoreAtU

def SplitPlaceUnramifiedGalois : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ π : CuspSub E a, InScope .csd l π (quadChar E ^ a) →
    ∃ r : G E Ω →* GL (Fin a) (Qbar l), Continuous r ∧ IsSSRep r ∧
      ∀ (w : HeightOneSpectrum (𝓞 E)), IsSplitAt w → ∀ B : Multiset ℂˣ, (CG.mk π).HasSat w B →
        GlobalTheory.RoadU.SphAt .unr π ι r w B

theorem HasRepU.mono {ι : Qbar l ≃+* ℂ} {U : Submodule ℂ (UA E a → ℂ)} {S S' : Finset (HeightOneSpectrum (𝓞 E))} (hS : S ⊆ S')
    {r : G E Ω →* GL (Fin a) (Qbar l)} (h : HasRepU ι U S r) : HasRepU ι U S' r :=
  ⟨h.1, h.2.1, fun w hw hn => h.2.2 w hw fun hm => hn (hS hm)⟩

theorem finite_not_apart (w₀ : HeightOneSpectrum (𝓞 E)) : {w : HeightOneSpectrum (𝓞 E) | ¬ Apart w w₀}.Finite := by
  set p := w₀.under (𝓞 (maximalRealSubfield E))
  haveI := p.isMaximal
  have hf : (p.asIdeal.primesOver (𝓞 E)).Finite := IsDedekindDomain.primesOver_finite p.asIdeal (𝓞 E)
  refine (hf.preimage (f := fun w : HeightOneSpectrum (𝓞 E) => w.asIdeal)
    (fun x _ y _ e => HeightOneSpectrum.ext e)).subset fun w hw => ?_
  have e : w.under (𝓞 (maximalRealSubfield E)) = p := not_not.1 hw
  exact ⟨w.isPrime, ⟨by rw [← e]; rfl⟩⟩

def nearPlaces (w₀ : HeightOneSpectrum (𝓞 E)) : Finset (HeightOneSpectrum (𝓞 E)) :=
  (finite_not_apart w₀).toFinset

theorem mem_nearPlaces {w w₀ : HeightOneSpectrum (𝓞 E)} : w ∈ nearPlaces w₀ ↔ ¬ Apart w w₀ :=
  Set.Finite.mem_toFinset _

theorem isSplitAt_of_not_apart {w w₀ : HeightOneSpectrum (𝓞 E)} (h₀ : IsSplitAt w₀) (h : ¬ Apart w w₀) : IsSplitAt w := by
  have e := not_not.1 h
  by_cases hw : w = w₀
  · exact hw ▸ h₀
  · exact ⟨w₀, Ne.symm hw, e.symm⟩

theorem RowStarCoreAtU.near (h : RowStarCoreAtU) (ι : Qbar l ≃+* ℂ) (ha : 1 ≤ a) {T : Finset (HeightOneSpectrum (𝓞 E))}
    (hT : NonSplitSet T) {w₀ : HeightOneSpectrum (𝓞 E)} (hl : ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal) (h₀ : IsSplitAt w₀)
    {U : Submodule ℂ (UA E a → ℂ)} (hU : IsAutRepU U) (hu : ∀ w, ¬ IsSplitAt w → w ∉ T → IsUnramU U w) :
    ∃ r : G E Ω →* GL (Fin a) (Qbar l), HasRepU ι U (nearPlaces w₀) r :=
  h E Ω l ι a ha _ T hT (fun _ hw => isSplitAt_of_not_apart h₀ (mem_nearPlaces.1 hw)) w₀ hl h₀
    (fun _ hw => mem_nearPlaces.2 hw) U hU hu

example (w₀ : HeightOneSpectrum (𝓞 E)) : w₀ ∈ nearPlaces w₀ := mem_nearPlaces.2 (not_apart_self w₀)

example (h : RowStarCoreU) (ι : Qbar l ≃+* ℂ) (ha : 1 ≤ a) : ∃ r : G E Ω →* GL (Fin a) (Qbar l),
    HasRepU ι (Submodule.span ℂ {(fun _ => 1 : UA E a → ℂ)}) ∅ r :=
  h E Ω l ι a ha ∅ ∅ nonSplitSet_empty (fun _ hw => absurd hw (Finset.notMem_empty _)) _ isAutRepU_const
    fun w _ _ => isUnramU_const w

example (h : RowStarCoreAtU) (ι : Qbar l ≃+* ℂ) (ha : 1 ≤ a) {w₀ : HeightOneSpectrum (𝓞 E)} (hl : ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal)
    (h₀ : IsSplitAt w₀) : ∃ r : G E Ω →* GL (Fin a) (Qbar l),
      HasRepU ι (Submodule.span ℂ {(fun _ => 1 : UA E a → ℂ)}) (nearPlaces w₀) r :=
  h.near ι ha nonSplitSet_empty hl h₀ isAutRepU_const fun w _ _ => isUnramU_const w

end GlobalTheory.RoadW

end
end

