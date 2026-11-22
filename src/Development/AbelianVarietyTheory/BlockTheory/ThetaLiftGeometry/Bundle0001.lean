import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.LocalRingCardinality.DataRows

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.AgreementAtAlmostAllSplitPrimes
section
open Formalism.BasicNotions Formalism.MainNotions.N

namespace GlobalTheory.IndefiniteRowSideFullHecke.AgreementAtAlmostAllSplitPrimes

def AgreeAtAlmostAllSplit {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂}
    (A : NAut N) (χ χ' : A.CG 1) : Prop :=
  {w : PlE H | IsSplitPl H w ∧ A.locG χ w ≠ A.locG χ' w}.Finite

def HeckeCharEqOfSplit {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)
    (A : NAut N) : Prop :=
  ∀ χ χ' : A.CG 1, AgreeAtAlmostAllSplit A χ χ' → χ = χ'

theorem agreeAtAlmostAllSplit_iff {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂}
    (A : NAut N) (χ χ' : A.CG 1) :
    AgreeAtAlmostAllSplit A χ χ' ↔
      ∀ᶠ w in Filter.cofinite, IsSplitPl H w → A.locG χ w = A.locG χ' w := by
  simp only [AgreeAtAlmostAllSplit, Filter.eventually_cofinite, Classical.not_imp]

example {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂}
    (A : NAut N) (χ : A.CG 1) : AgreeAtAlmostAllSplit A χ χ := by
  simp [AgreeAtAlmostAllSplit]

theorem HeckeCharEqOfSplit.of_forall {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂}
    {A : NAut N} (h : HeckeCharEqOfSplit N A) (χ χ' : A.CG 1)
    (hw : ∀ w, IsSplitPl H w → A.locG χ w = A.locG χ' w) : χ = χ' :=
  h χ χ' ((agreeAtAlmostAllSplit_iff A χ χ').2 (Filter.Eventually.of_forall hw))

end GlobalTheory.IndefiniteRowSideFullHecke.AgreementAtAlmostAllSplitPrimes
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.GaloisRepresentations
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.GaloisRepresentations

open Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

abbrev Rep (i : N.Loc) (a : ℕ) : Type := G H.E N.Om →* GL (Fin a) (Qbar (N.l i))

def IsCont (i : N.Loc) {a : ℕ} (r : Rep N i a) : Prop :=
  Continuous fun g => ((r g : GL (Fin a) (Qbar (N.l i))) : Matrix (Fin a) (Fin a) (Qbar (N.l i)))

def cycPow (i : N.Loc) (k : ℤ) (g : G H.E N.Om) : Qbar (N.l i) :=
  algebraMap ℚ_[N.l i] (Qbar (N.l i))
    ((((cycZ (F := H.E) (Ω := N.Om) (N.l i) g) ^ k : ℤ_[N.l i]ˣ) : ℤ_[N.l i]) : ℚ_[N.l i])

def IsPolarized (i : N.Loc) {a : ℕ} (r : Rep N i a) : Prop :=
  ∀ c : N.Om ≃+* N.Om, (∀ x : H.E, c (algebraMap H.E N.Om x) = algebraMap H.E N.Om (H.conj x)) →
    ∃ P : GL (Fin a) (Qbar (N.l i)), ∀ g g' : G H.E N.Om, (∀ y, g' y = c (g (c.symm y))) →
      ((r g' : GL (Fin a) (Qbar (N.l i))) : Matrix (Fin a) (Fin a) (Qbar (N.l i))) *
          (P : Matrix (Fin a) (Fin a) (Qbar (N.l i))) =
        (P : Matrix (Fin a) (Fin a) (Qbar (N.l i))) *
          (cycPow N i (1 - (a : ℤ)) g •
            (((r g)⁻¹ : GL (Fin a) (Qbar (N.l i))) : Matrix (Fin a) (Fin a) (Qbar (N.l i))).transpose)

def IsGalRep (i : N.Loc) {a : ℕ} (π : A.CG a) (r : Rep N i a) : Prop :=
  IsCont N i r ∧ IsSSRep r ∧
  (∀ w : PlE H, A.wdOf i r w = A.lpTw (A.locG π w) ((1 - (a : ℝ)) / 2)) ∧
  (∀ w ∈ placesOver H.E (N.l i), A.IsdRW i r w) ∧
  ∀ τ : H.E →+* Qbar (N.l i), (A.jumpsW i r τ).map (fun n : ℤ => (n : ℂ)) =
    (A.infG π ((A.iotaQC i).toRingHom.comp τ)).map (fun α => ((a : ℂ) - 1) / 2 - α)

def GalRep (i : N.Loc) : Prop :=
  ∀ (a : ℕ) (π : A.CG a), 1 ≤ a → A.csd π → A.ralg π →
    (∃ r : Rep N i a, IsGalRep N A i π r) ∧
    ∀ w : PlE H, w ∉ placesOver H.E (N.l i) → A.tempered (A.locG π w)

def GalRepFull (i : N.Loc) : Prop :=
  ∀ (a : ℕ) (π : A.CG a), 1 ≤ a → A.csd π → A.ralg π →
    (∃ r : Rep N i a, IsGalRep N A i π r ∧ IsPolarized N i r ∧
      ∀ w ∈ placesOver H.E (N.l i), A.unr (A.locG π w) → A.IsCrysW i r w) ∧
    ∀ w : PlE H, A.tempered (A.locG π w)

def IsAlg {a : ℕ} (π : A.CG a) : Prop :=
  ∀ τ : H.E →+* ℂ, ∀ z ∈ A.infG π τ, ∃ n : ℤ, z = (n : ℂ) + ((a : ℂ) - 1) / 2

def ClozelPurity : Prop :=
  ∀ (a : ℕ) (π : A.CG a), 1 ≤ a → IsAlg N A π →
    ∃ u : ℤ, (∀ τ : H.E →+* ℂ,
        A.infG π ((starRingEnd ℂ).comp τ) = (A.infG π τ).map (fun z => (u : ℂ) - z)) ∧
      (A.csd π → u = 0)

def ExistsGaloisRepresentationOfHeckeCharacter (i : N.Loc) : Prop :=
  ∀ (χ : A.CG 1) (s : ℝ) (n : (H.E →+* ℂ) → ℤ),
    (∀ τ, (A.infG χ τ).map (fun z => z + (s : ℂ)) = {(n τ : ℂ)}) →
    ∃ r : Rep N i 1, IsCont N i r ∧
      (∀ w : PlE H, A.wdOf i r w = A.lpTw (A.locG χ w) s) ∧
      (∀ w ∈ placesOver H.E (N.l i), A.IsdRW i r w) ∧
      ∀ τ : H.E →+* Qbar (N.l i), A.jumpsW i r τ = {-n ((A.iotaQC i).toRingHom.comp τ)}

def Gal : Prop :=
  ∀ i : N.Loc, GalRep N A i ∧ ClozelPurity N A ∧ ExistsGaloisRepresentationOfHeckeCharacter N A i

def GalFull : Prop :=
  ∀ i : N.Loc, GalRepFull N A i ∧ ClozelPurity N A ∧ ExistsGaloisRepresentationOfHeckeCharacter N A i

theorem GalFull.gal (h : GalFull N A) : Gal N A := fun i =>
  ⟨fun a π ha hc hr =>
    let ⟨⟨r, h₁, _⟩, h₂⟩ := (h i).1 a π ha hc hr
    ⟨⟨r, h₁⟩, fun w _ => h₂ w⟩, (h i).2⟩

theorem IsGalRep.crys {i : N.Loc} {a : ℕ} {π : A.CG a} {r : Rep N i a} (h : IsGalRep N A i π r)
    (w : PlE H) (hw : w ∈ placesOver H.E (N.l i)) (hu : A.unr (A.locG π w)) : A.IsCrysW i r w := by
  refine (A.wdOf_unrL i r w hw h.1 (h.2.2.2.1 w hw)).1 ?_
  rw [h.2.2.1 w]
  exact (A.unr_tw _ _).2 hu

end GlobalTheory.IndefiniteRowSideFullHecke.GaloisRepresentations
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.LocalInvariantsOfColumns
section
noncomputable section

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N

namespace GlobalTheory.IndefiniteRowSideFullHecke.LocalInvariantsOfColumns

def charTwist {k Γ V : Type} [Field k] [Group Γ] [AddCommGroup V] [Module k V]
    (ρ : Representation k Γ V) (χ : Γ →* kˣ) : Representation k Γ V where
  toFun g := ((χ g : kˣ) : k) • ρ g
  map_one' := by simp
  map_mul' g h := by
    rw [map_mul, map_mul, Units.val_mul, smul_mul_smul_comm]

def colRep {k Γ : Type} [Field k] [Group Γ] {a : ℕ} (ρ : Γ →* GL (Fin a) k) :
    Representation k Γ (Fin a → k) where
  toFun g := Matrix.toLin' (ρ g : Matrix (Fin a) (Fin a) k)
  map_one' := by
    rw [map_one, Units.val_one, Matrix.toLin'_one]; rfl
  map_mul' g h := by
    rw [map_mul, Units.val_mul, Matrix.toLin'_mul]; rfl

def NoInv {k Γ V : Type} [Field k] [Group Γ] [AddCommGroup V] [Module k V]
    (ρ : Representation k Γ V) (D : Subgroup Γ) : Prop :=
  Representation.invariants (ρ.comp D.subtype) = ⊥

theorem noInv_iff {k Γ V : Type} [Field k] [Group Γ] [AddCommGroup V] [Module k V]
    (ρ : Representation k Γ V) (D : Subgroup Γ) :
    NoInv ρ D ↔ ∀ v : V, (∀ g ∈ D, ρ g v = v) → v = 0 := by
  unfold NoInv
  rw [Submodule.eq_bot_iff]
  refine forall_congr' fun v => imp_congr ?_ Iff.rfl
  rw [Representation.mem_invariants]
  exact ⟨fun h g hg => h ⟨g, hg⟩, fun h g => h g.1 g.2⟩

example {k Γ V : Type} [Field k] [Group Γ] [AddCommGroup V] [Module k V] [Nontrivial V]
    (D : Subgroup Γ) : ¬ NoInv (Representation.trivial k Γ V) D := by
  rw [noInv_iff]
  intro h
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  exact hv (h v fun _ _ => rfl)

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def chiOneK (i : N.Loc) : G H.E N.Om →* (Kf N i)ˣ :=
  (Units.map (algebraMap (N.O i) (Kf N i)).toMonoidHom).comp (N.chi i 1)

def cycK (i : N.Loc) : G H.E N.Om →* (Kf N i)ˣ :=
  (Units.map ((algebraMap (N.O i) (Kf N i)).comp (algebraMap ℤ_[N.l i] (N.O i))).toMonoidHom).comp
    (cycZ (F := H.E) (Ω := N.Om) (N.l i))

def Wtw (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) :
    Representation (Kf N i) (G H.E N.Om) (Fin R.r → Kf N i) :=
  charTwist (colRep (mapRep (algebraMap (N.O i) (Kf N i)) ρ)) (chiOneK N i)⁻¹

def TateDual (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) :
    Representation (Kf N i) (G H.E N.Om) (Module.Dual (Kf N i) (Fin R.r → Kf N i)) :=
  charTwist (Representation.dual (Wtw N i ρ)) (cycK N i)

def IsRankPart (i : N.Loc) (Sig : List (Part A.CG))
    (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) : Prop :=
  Continuous (fun g => ((ρ g : GL (Fin R.r) (N.O i)) : Matrix (Fin R.r) (Fin R.r) (N.O i))) ∧
  IsSSRep (mapRep (algebraMap (N.O i) (Kf N i)) ρ) ∧
  ∀ w : PlE H, SplitOut N i w → ∀ (B : ValuationSubring N.Om) (σ : G H.E N.Om),
    IsPlaceOver (F := H.E) B w → IsFrob (F := H.E) B (normV w) σ →
    ((ρ σ : GL (Fin R.r) (N.O i)) : Matrix (Fin R.r) (Fin R.r) (N.O i)).charpoly.map (iotaO N A i) =
      galPol A (A.lpTw (isoLoc N A (twistIso N A Sig A.etaTinv) w) ((1 - (R.nV : ℝ)) / 2))

def NoLocalInvariants : Prop :=
  ∀ (i : N.Loc) (x : N.X i), x ∈ ZN N A i →
    ∀ Sig : List (Part A.CG), HasParamX N A i x Sig → IsCuspIso N A Sig →
    ∀ ρ : G H.E N.Om →* GL (Fin R.r) (N.O i), IsRankPart N A i Sig ρ →
    ∀ w : PlE H,
      NoInv (Wtw N i ρ) (Dec (F := H.E) (N.plOm.1 w)) ∧
      NoInv (TateDual N i ρ) (Dec (F := H.E) (N.plOm.1 w))

end GlobalTheory.IndefiniteRowSideFullHecke.LocalInvariantsOfColumns

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.NoLocalInvariants
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts

open NumberField IsDedekindDomain Polynomial Matrix Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def eps (i : N.Loc) : G H.E N.Om →* (N.O i)ˣ :=
  (Units.map (algebraMap ℤ_[N.l i] (N.O i)).toMonoidHom).comp
    (cycZ (F := H.E) (Ω := N.Om) (N.l i))

def IsRankPart (i : N.Loc) (x : N.X i) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) : Prop :=
  Continuous (fun g => ((ρ g : GL (Fin R.r) (N.O i)) : Matrix (Fin R.r) (Fin R.r) (N.O i))) ∧
  IsSSRep (mapRep (algebraMap (N.O i) (Kf N i)) ρ) ∧
  ∀ w, SplitOut N i w → ∀ (B : ValuationSubring N.Om) (σ : G H.E N.Om),
    IsPlaceOver (F := H.E) B w → IsFrob (F := H.E) B (normV w) σ →
    ((ρ σ : GL (Fin R.r) (N.O i)) : Matrix (Fin R.r) (Fin R.r) (N.O i)).charpoly *
        ∏ c ∈ Finset.Icc 1 R.t, (X - C ((N.chi i c σ : (N.O i)ˣ) : N.O i)) =
      heckePol N i x w

def matW (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) (g : G H.E N.Om) :
    Matrix (Fin R.r) (Fin R.r) (Kf N i) :=
  ((((N.chi i 1 g)⁻¹ : (N.O i)ˣ) : N.O i) •
    ((ρ g : GL (Fin R.r) (N.O i)) : Matrix (Fin R.r) (Fin R.r) (N.O i))).map
      (algebraMap (N.O i) (Kf N i))

def matT (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) (g : G H.E N.Om) :
    Matrix (Fin R.r) (Fin R.r) (Kf N i) :=
  algebraMap (N.O i) (Kf N i) ((eps N i g : (N.O i)ˣ) : N.O i) • (matW N i ρ g⁻¹)ᵀ

def NoInv {Γ K : Type} [Group Γ] [Field K] {a : ℕ} (D : Subgroup Γ)
    (M : Γ → Matrix (Fin a) (Fin a) K) : Prop :=
  ∀ v : Fin a → K, (∀ g ∈ D, (M g).mulVec v = v) → v = 0

def NoLocalInv (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) : Prop :=
  ∀ w : PlE H, NoInv (Dec (F := H.E) (N.plOm.1 w)) (matW N i ρ) ∧
    NoInv (Dec (F := H.E) (N.plOm.1 w)) (matT N i ρ)

def IsCuspPoint (i : N.Loc) (x : N.X i) : Prop :=
  x ∈ ZN N A i ∧ ∃ Sig, HasParamX N A i x Sig ∧ IsCuspIso N A Sig

def NoLocalInvCusp : Prop :=
  ∀ (i : N.Loc) (x : N.X i), IsCuspPoint N A i x →
    ∀ ρ, IsRankPart N i x ρ → NoLocalInv N i ρ

def NoLocalInvGood : Prop :=
  ∀ (i : N.Loc) (x : N.X i), x ∈ ZgoodN N A i →
    ∀ ρ, IsRankPart N i x ρ → NoLocalInv N i ρ

def NoLocalInvariants : Prop :=
  ∀ (i : N.Loc) (x : N.X i), (IsCuspPoint N A i x ∨ x ∈ ZgoodN N A i) →
    ∀ ρ, IsRankPart N i x ρ → NoLocalInv N i ρ

theorem matW_mul (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) (g h : G H.E N.Om) :
    matW N i ρ (g * h) = matW N i ρ g * matW N i ρ h := by
  unfold matW
  rw [← Matrix.map_mul, smul_mul_smul_comm, map_mul, map_mul, mul_inv, Units.val_mul, Units.val_mul]

theorem matW_one (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) : matW N i ρ 1 = 1 := by
  simp [matW]

theorem matT_transpose_mul_matW (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i))
    (g : G H.E N.Om) :
    (matT N i ρ g)ᵀ * matW N i ρ g =
      algebraMap (N.O i) (Kf N i) ((eps N i g : (N.O i)ˣ) : N.O i) • (1 : Matrix _ _ (Kf N i)) := by
  unfold matT
  rw [Matrix.transpose_smul, Matrix.transpose_transpose, Matrix.smul_mul, ← matW_mul, inv_mul_cancel,
    matW_one]

end GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.SmallRowEigenvalues
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SmallBlockEigenvalues

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N

def RowEigSmall {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) :
    Prop :=
  ∀ (i : N.Loc) (σ : what₂.FT), what₂.isot (N.j i) σ ≠ ⊥ →
    ∀ w : PlE H, IsSplitPl H w → A.unr (A.locW i σ w) →
      ∀ α ∈ A.frobEig (A.locW i σ w), ‖α‖ < ((normV w : ℕ) : ℝ) ^ (((R.t : ℝ) - 1) / 2)

theorem one_lt_normV {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    1 < normV w := by
  unfold normV
  have : Finite (𝓞 E ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  have : Nontrivial (𝓞 E ⧸ w.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr w.isPrime.ne_top
  exact Finite.one_lt_card

theorem rowEigSmall_of_le {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)
    (A : NAut N)
    (h : ∀ (i : N.Loc) (σ : what₂.FT), what₂.isot (N.j i) σ ≠ ⊥ →
      ∀ w : PlE H, IsSplitPl H w → A.unr (A.locW i σ w) →
        ∀ α ∈ A.frobEig (A.locW i σ w), ‖α‖ ≤ ((normV w : ℕ) : ℝ) ^ (((R.r : ℝ) - 1) / 2)) :
    RowEigSmall N A := by
  intro i σ hσ w hw hu α hα
  have hrt : R.r < R.t := by have := R.rank_add_five_le; unfold Ranks.r; omega
  refine lt_of_le_of_lt (h i σ hσ w hw hu α hα) ?_
  have h1 : (1 : ℝ) < ((normV w : ℕ) : ℝ) := by exact_mod_cast one_lt_normV w
  have h2 : (R.r : ℝ) < (R.t : ℝ) := by exact_mod_cast hrt
  exact Real.rpow_lt_rpow_of_exponent_lt h1 (by linarith)

end GlobalTheory.IndefiniteRowSideFullHecke.SmallBlockEigenvalues
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.TemperedRepresentations
section
namespace GlobalTheory.IndefiniteRowSideFullHecke.TemperedRepresentations

open Formalism.BasicNotions Formalism.MainNotions.N

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

def TemperedRank (N : NData R H what₂) (A : NAut N) (a : ℕ) : Prop :=
  ∀ π : A.CG a, A.csd π → A.ralg π → ∀ w : PlE H, A.tempered (A.locG π w)

def Tempered (N : NData R H what₂) (A : NAut N) : Prop :=
  ∀ (a : ℕ), 1 ≤ a → ∀ π : A.CG a, A.csd π → A.ralg π →
    ∀ w : PlE H, A.tempered (A.locG π w)

end GlobalTheory.IndefiniteRowSideFullHecke.TemperedRepresentations
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.ThetaEigenspaceImage
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaEigenspaceImage

open Formalism.BasicNotions Formalism.MainNotions.N

def ThetaTMapsIntoEig {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)
    (A : NAut N) : Prop :=
  ∀ (i : N.Loc) (x : N.X i) (Sig : List (Part A.CG)),
    x ∈ ZgoodN N A i → HasParamX N A i x Sig →
      ∀ f ∈ MjSig N A i Sig, what₂.thetaT (N.mu i) (N.j i) f ∈ eigC N A i x

def MjSigOut {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
    (i : N.Loc) (Sig : List (Part A.CG)) : Submodule ℂ (what₂.Mj (N.j i)) :=
  ⨆ σ ∈ {σ | ∀ w, SplitOut N i w → isoLoc N A Sig w = A.locW i σ w}, what₂.isot (N.j i) σ

def ThetaTMapsIntoEigOut {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)
    (A : NAut N) : Prop :=
  ∀ (i : N.Loc) (x : N.X i) (Sig : List (Part A.CG)),
    x ∈ ZgoodN N A i → HasParamX N A i x Sig →
      ∀ f ∈ MjSigOut N A i Sig, what₂.thetaT (N.mu i) (N.j i) f ∈ eigC N A i x

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem mjSig_le_mjSigOut (i : N.Loc) (Sig : List (Part A.CG)) :
    MjSig N A i Sig ≤ MjSigOut N A i Sig := by
  unfold MjSig MjSigOut
  exact biSup_mono fun σ hσ w hw => hσ.2.2 w hw.1

theorem thetaTMapsIntoEig_of_out (h : ThetaTMapsIntoEigOut N A) : ThetaTMapsIntoEig N A :=
  fun i x Sig hx hp f hf => h i x Sig hx hp f (mjSig_le_mjSigOut N A i Sig hf)

theorem thetaTMapsIntoEig_iff_map_le : ThetaTMapsIntoEig N A ↔
    ∀ (i : N.Loc) (x : N.X i) (Sig : List (Part A.CG)),
      x ∈ ZgoodN N A i → HasParamX N A i x Sig →
        (MjSig N A i Sig).map (what₂.thetaT (N.mu i) (N.j i)) ≤ eigC N A i x := by
  unfold ThetaTMapsIntoEig
  simp only [Submodule.map_le_iff_le_comap]
  rfl

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaEigenspaceImage
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.ThetaEigenspaceMapping
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.N

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaEigenspaceMapping

def ThetaPMapsEigenspaceInto {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)
    (A : NAut N) : Prop :=
  ∀ (i : N.Loc) (x : N.X i), x ∈ ZgoodN N A i →
    ∀ Sig : List (Formalism.BasicNotions.Part A.CG), HasParamX N A i x Sig →
      ∀ F ∈ eigC N A i x, what₂.thetaP (N.mu i) (N.j i) F ∈ MjSig N A i Sig

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaEigenspaceMapping
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.ThetaGramMatrix
section
namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaGramMatrix

open Formalism.BasicNotions Formalism.MainNotions.N

noncomputable def thetaGram {R : Ranks} (what₂ : Rows.Data R) (μ : what₂.Tup) (j : ℕ) :
    what₂.Mj j →ₗ[ℂ] what₂.Mj j :=
  what₂.thetaP μ j ∘ₗ what₂.thetaT μ j

def ThetaGramPositiveScalar {R : Ranks} {H : Host R} {what₂ : Rows.Data R}
    (N : NData R H what₂) (_A : NAut N) : Prop :=
  ∀ (i : N.Loc) (σ : what₂.FT),
    (∀ f ∈ what₂.isot (N.j i) σ,
      thetaGram what₂ (N.mu i) (N.j i) f = ((what₂.lamP (N.mu i) (N.j i) σ : ℝ) : ℂ) • f) ∧
    (what₂.isot (N.j i) σ ≠ ⊥ → 0 < what₂.lamP (N.mu i) (N.j i) σ)

theorem ThetaGramPositiveScalar.norm_sq {R : Ranks} {H : Host R} {what₂ : Rows.Data R}
    {N : NData R H what₂} {A : NAut N} (h : ThetaGramPositiveScalar N A) (i : N.Loc) (σ : what₂.FT)
    (f : what₂.Mj (N.j i)) (hf : f ∈ what₂.isot (N.j i) σ) :
    ‖what₂.thetaT (N.mu i) (N.j i) f‖ ^ 2 = what₂.lamP (N.mu i) (N.j i) σ * ‖f‖ ^ 2 := by
  have hg := (h i σ).1 f hf
  simp only [thetaGram, LinearMap.comp_apply] at hg
  have key : inner ℂ (what₂.thetaT (N.mu i) (N.j i) f) (what₂.thetaT (N.mu i) (N.j i) f)
      = ((what₂.lamP (N.mu i) (N.j i) σ : ℝ) : ℂ) * inner ℂ f f := by
    show inner ℂ (LinearMap.adjoint (what₂.thetaP (N.mu i) (N.j i)) f)
      (what₂.thetaT (N.mu i) (N.j i) f) = _
    rw [LinearMap.adjoint_inner_left, hg, inner_smul_right]
  rw [@norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ, key]
  simp

theorem ThetaGramPositiveScalar.eq_zero {R : Ranks} {H : Host R} {what₂ : Rows.Data R}
    {N : NData R H what₂} {A : NAut N} (h : ThetaGramPositiveScalar N A) (i : N.Loc) (σ : what₂.FT)
    (f : what₂.Mj (N.j i)) (hf : f ∈ what₂.isot (N.j i) σ)
    (h0 : what₂.thetaT (N.mu i) (N.j i) f = 0) : f = 0 := by
  by_contra hne
  have hpos : 0 < what₂.lamP (N.mu i) (N.j i) σ := by
    apply (h i σ).2
    intro hb
    rw [hb] at hf
    exact hne ((Submodule.mem_bot ℂ).1 hf)
  have e := h.norm_sq i σ f hf
  rw [h0, norm_zero] at e
  have e2 : what₂.lamP (N.mu i) (N.j i) σ * ‖f‖ ^ 2 = 0 := by rw [← e]; norm_num
  rcases mul_eq_zero.1 e2 with h1 | h1
  · exact absurd h1 hpos.ne'
  · exact hne (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h1))

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaGramMatrix
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.ThetaLiftOfEachRow
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaLiftOfEachComponent

open Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N

def EachRowHasThetaLift {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)
    (A : NAut N) : Prop :=
  ∀ (i : N.Loc) (σ : what₂.FT), what₂.isot (N.j i) σ ≠ ⊥ → ∃ P : A.AV i, thetaOf N A i σ P

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaLiftOfEachComponent
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.ThetaLiftUniqueness
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaLiftUniqueness

open Formalism.BasicNotions Formalism.MainNotions.N

def EachRowHasThetaLift {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)
    (A : NAut N) : Prop :=
  ∀ (i : N.Loc) (σ : what₂.FT), what₂.isot (N.j i) σ ≠ ⊥ → ∃ P : A.AV i, thetaOf N A i σ P

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem eachRowHasThetaLift_iff :
    EachRowHasThetaLift N A ↔
      ∀ (i : N.Loc) (σ : what₂.FT), (∃ f ∈ what₂.isot (N.j i) σ, f ≠ 0) → ∃ P : A.AV i,
        (∃ f ∈ what₂.isot (N.j i) σ, what₂.thetaT (N.mu i) (N.j i) f ≠ 0) ∧
        ∀ f ∈ what₂.isot (N.j i) σ, what₂.thetaT (N.mu i) (N.j i) f ∈ A.typeV i P := by
  unfold EachRowHasThetaLift thetaOf
  refine forall_congr' fun i => forall_congr' fun σ => ?_
  rw [Submodule.ne_bot_iff]
  refine imp_congr_right fun _ => exists_congr fun P => and_congr ?_ ?_
  · rw [Submodule.ne_bot_iff]
    constructor
    · rintro ⟨_, ⟨f, hf, rfl⟩, h⟩
      exact ⟨f, hf, h⟩
    · rintro ⟨f, hf, h⟩
      exact ⟨_, ⟨f, hf, rfl⟩, h⟩
  · rw [Submodule.map_le_iff_le_comap]
    rfl

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaLiftUniqueness
end
end

