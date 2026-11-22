import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.DegreeAdditiveFrobenius
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.QCoh (IsFiniteQC)
open GlobalTheory.VB

namespace GlobalTheory.IndefiniteRowSideFullHecke.DegreeAdditiveFrobenius

def IsFiniteOfDegree {C' C : Scheme.{0}} [IsIntegral C'] [IsIntegral C] (π : C' ⟶ C) (m : ℕ) :
    Prop :=
  IsFinite π ∧ π (genericPoint C') = genericPoint C ∧ π.residueDegree (genericPoint C') = m

section Clauses

variable (k : Type) [Field k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] [IsIntegral C]

def DegAdditive : Prop :=
  ∀ S : ShortComplex C.Modules, S.ShortExact → IsFiniteQC S.X₁ → IsFiniteQC S.X₂ →
    IsFiniteQC S.X₃ → deg k S.X₂ = deg k S.X₁ + deg k S.X₃

def DegDual : Prop :=
  ∀ (E : C.Modules) (r : ℕ), IsVB E r → deg k (dual E) = -deg k E

def DegDet : Prop :=
  ∀ (E : C.Modules) (r : ℕ), IsVB E r → degLB k (det E r) = deg k E

def DegLeSat : Prop :=
  ∀ (E ξ : C.Modules) (r : ℕ) (i : ξ ⟶ E), IsVB E r → IsCohSub i → deg k ξ ≤ deg k (sat i)

def SubDegBounded : Prop :=
  ∀ (E : C.Modules) (r : ℕ), IsVB E r →
    BddAbove (subDegs k E) ∧ ∃ P : ℤ, IsMaxSubDeg k E P ∧ 0 ≤ P

variable {C} in

def PullbackRules {C' : Scheme.{0}} [Algebra k Γ(C', ⊤)] [IsIntegral C'] (π : C' ⟶ C) (m : ℕ) :
    Prop :=
  Flat π ∧
  (∀ (E : C.Modules) (r : ℕ), IsVB E r →
    deg k ((Scheme.Modules.pullback π).obj E) = (m : ℤ) * deg k E) ∧
  (∀ (E ξ : C.Modules) (r : ℕ) (i : ξ ⟶ E), IsVB E r → IsCohSub i →
    IsCohSub ((Scheme.Modules.pullback π).map i) ∧
      deg k ((Scheme.Modules.pullback π).obj ξ) = (m : ℤ) * deg k ξ) ∧
  (∀ (E : C.Modules) (r : ℕ) (P P' : ℤ), IsVB E r → IsMaxSubDeg k E P →
    IsMaxSubDeg k ((Scheme.Modules.pullback π).obj E) P' → (m : ℤ) * P ≤ P')

def CoverRules : Prop :=
  ∀ (C' : Scheme.{0}) [Algebra k Γ(C', ⊤)] [IsIntegral C'] (π : C' ⟶ C) (m : ℕ),
    IsSmoothProjCurve k C' → π ≫ strHom k C = strHom k C' → IsFiniteOfDegree π m →
      PullbackRules k π m

def FrobeniusRules : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] [CharP k p],
    IsFiniteOfDegree (frob C p (natCast_eq_zero C p k)) p ∧
      PullbackRules k (frob C p (natCast_eq_zero C p k)) p

end Clauses

def CurveDegrees : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] [IsIntegral C],
    IsSmoothProjCurve k C →
      DegAdditive k C ∧ DegDual k C ∧ DegDet k C ∧ DegLeSat k C ∧ CoverRules k C ∧
        FrobeniusRules k C ∧ SubDegBounded k C

theorem IsFiniteOfDegree.unique {C' C : Scheme.{0}} [IsIntegral C'] [IsIntegral C] {π : C' ⟶ C}
    {m n : ℕ} (h : IsFiniteOfDegree π m) (h' : IsFiniteOfDegree π n) : m = n :=
  h.2.2.symm.trans h'.2.2

open GlobalTheory.ProjSpace GlobalTheory.ProjCoh in
attribute [local instance] MvPolynomial.gradedAlgebra in

example (H : CurveDegrees) (k : Type) [Field k] [IsAlgClosed k] [Fact (Nat.Prime 3)] [CharP k 3] :
    deg k ((frobPull 3 (natCast_eq_zero (PSpace k 1) 3 k)).obj (sheafO k 1 2)) = 6 := by
  have h := ((H k (PSpace k 1) (isSmoothProjCurve_line k)).2.2.2.2.2.1 3).2.2.1 _ 1
    (isVB_sheafO k 2)
  rw [deg_sheafO] at h
  exact h

end GlobalTheory.IndefiniteRowSideFullHecke.DegreeAdditiveFrobenius
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FiniteDegreeMorphisms
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.QCoh (IsFiniteQC)
open GlobalTheory.VB

namespace GlobalTheory.IndefiniteRowSideFullHecke.FiniteDegreeMorphisms

structure IsFiniteOfDegree {C' C : Scheme.{0}} [IsIntegral C] (π : C' ⟶ C) (m : ℕ) : Prop where

  isFinite : IsFinite π

  finrank_eq : π.finrank (genericPoint C) = m

section Clauses

variable (k : Type) [Field k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] [IsIntegral C]

def DegAdditive : Prop :=
  ∀ S : ShortComplex C.Modules, S.ShortExact → IsFiniteQC S.X₁ → IsFiniteQC S.X₂ →
    IsFiniteQC S.X₃ → deg k S.X₂ = deg k S.X₁ + deg k S.X₃

def DegDual : Prop :=
  ∀ (E : C.Modules) (r : ℕ), IsVB E r → deg k (dual E) = -deg k E

def DegDet : Prop :=
  ∀ (E : C.Modules) (r : ℕ), IsVB E r → degLB k (det E r) = deg k E

def DegLeSat : Prop :=
  ∀ (E : C.Modules) (r : ℕ), IsVB E r → ∀ (G : C.Modules) (i : G ⟶ E), IsCohSub i →
    deg k G ≤ deg k (sat i)

def MaxSubDegExists : Prop :=
  ∀ (E : C.Modules) (r : ℕ), IsVB E r →
    BddAbove (subDegs k E) ∧ ∃ P : ℤ, IsMaxSubDeg k E P

variable {C} in

def ScalesDeg {C' : Scheme.{0}} [Algebra k Γ(C', ⊤)] [IsIntegral C'] (π : C' ⟶ C) (m : ℕ) : Prop :=
  ∀ (E : C.Modules) (r : ℕ), IsVB E r →
    deg k ((Scheme.Modules.pullback π).obj E) = m * deg k E ∧
    ∀ (G : C.Modules) (i : G ⟶ E), IsCohSub i →
      IsCohSub ((Scheme.Modules.pullback π).map i) ∧
      deg k ((Scheme.Modules.pullback π).obj G) = m * deg k G

def DegCover : Prop :=
  ∀ (C' : Scheme.{0}) [Algebra k Γ(C', ⊤)] [IsIntegral C'], IsSmoothProjCurve k C' →
    ∀ (π : C' ⟶ C) (m : ℕ), π ≫ strHom k C = strHom k C' → IsFiniteOfDegree π m →
      Flat π ∧ ScalesDeg k π m

def DegFrob (p : ℕ) [Fact p.Prime] [CharP k p] : Prop :=
  IsFiniteOfDegree (frob C p (natCast_eq_zero C p k)) p ∧
    Flat (frob C p (natCast_eq_zero C p k)) ∧ ScalesDeg k (frob C p (natCast_eq_zero C p k)) p

end Clauses

def CurveDegrees : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] [CharP k p]
    (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] [IsIntegral C], IsSmoothProjCurve k C →
    DegAdditive k C ∧ DegDual k C ∧ DegDet k C ∧ DegLeSat k C ∧ DegCover k C ∧ DegFrob k C p ∧
      MaxSubDegExists k C

section Basic₂

open ProjSpace ProjCoh

variable {k : Type} [Field k] {C C' : Scheme.{0}} [Algebra k Γ(C, ⊤)] [IsIntegral C]
  [Algebra k Γ(C', ⊤)] [IsIntegral C']

theorem ScalesDeg.mul_le {π : C' ⟶ C} {m : ℕ} (h : ScalesDeg k π m) {E : C.Modules} {r : ℕ}
    (hE : IsVB E r) {P P' : ℤ} (hP : IsMaxSubDeg k E P)
    (hP' : IsMaxSubDeg k ((Scheme.Modules.pullback π).obj E) P') : m * P ≤ P' := by
  obtain ⟨G, i, hi, rfl⟩ := hP.exists_isCohSub
  obtain ⟨h₁, h₂⟩ := (h E r hE).2 G i hi
  rw [← h₂]
  exact hP'.2 h₁.deg_mem

example [Fact (Nat.Prime 3)] : IsSmoothProjCurve (AlgebraicClosure (ZMod 3))
    (PSpace (AlgebraicClosure (ZMod 3)) 1) := isSmoothProjCurve_line _

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.FiniteDegreeMorphisms
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FrobeniusTwistEigen
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.VB
open GlobalTheory.QCoh (freeModule)

namespace GlobalTheory.IndefiniteRowSideFullHecke.FrobeniusTwistEigen

def IsExtension {X : Scheme.{0}} (A H B : X.Modules) : Prop :=
  ∃ (i : A ⟶ H) (q : H ⟶ B) (w : i ≫ q = 0), (ShortComplex.mk i q w).ShortExact

abbrev frobTwist (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] {X : Scheme.{0}}
    [Algebra k Γ(X, ⊤)] (M : X.Modules) : X.Modules :=
  (frobPull p (natCast_eq_zero X p k)).obj M

def SlopeInequality : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] [CharP k p]
    (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] [IsIntegral C], IsSmoothProjCurve k C →
    ∀ (L H : C.Modules) (g : ℕ), IsVB L g → IsVB H (2 * g) →
      IsExtension (dual L) H L →
      (∃ v : frobTwist p k L ⟶ H, Mono v) →
      ∀ P : ℤ, IsMaxSubDeg k L P → (p : ℤ) * P ≤ -deg k L + 2 * P

def EigenDegrees : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] [CharP k p]
    (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] [IsIntegral C], IsSmoothProjCurve k C →
    ∀ (ι : Type) [Fintype ι] (φ : Equiv.Perm ι) (c : ι → ι), Function.Involutive c →
    ∀ (L H : ι → C.Modules) (m n : ι → ℕ), (∀ τ, IsVB (L τ) (m τ)) → (∀ τ, IsVB (H τ) (n τ)) →
      (∀ τ, IsExtension (dual (L (c τ))) (H τ) (L τ)) →
      (∀ τ, IsExtension (frobTwist p k (L τ)) (H (φ τ)) (frobTwist p k (dual (L (c τ))))) →
      (∀ τ, deg k (H τ) = 0) ∧ (∀ τ, deg k (L τ) = deg k (L (c τ))) ∧
        ∀ (M : C.Modules), Nonempty (M ≅ ∐ L) →
          ∀ Ψ : Finset ι, (∀ τ, τ ∈ Ψ ↔ c τ ∉ Ψ) →
            2 * ∑ τ ∈ Ψ, deg k (dual (L τ)) = -deg k M

def SlopeAndEigenDegrees : Prop := SlopeInequality ∧ EigenDegrees

end GlobalTheory.IndefiniteRowSideFullHecke.FrobeniusTwistEigen
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GenericFiniteMaps
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (toMod)
open GlobalTheory.VB

namespace GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps

section Defs

variable (k : Type) [Field k] (T : Scheme.{0}) [Algebra k Γ(T, ⊤)]

structure IsProjSurface : Prop where

  isIntegral : IsIntegral T

  dim_eq : topologicalKrullDim T = 2

  isProjOver : IsProjOver (strHom k T)

variable {T} in

def degCh2 [IsIntegral T] (E : T.Modules) : ℚ :=
  ((chi k E : ℚ) + (chi k (dual E) : ℚ)) / 2 - (genRank E : ℚ) * (chi k (structureModule T) : ℚ)

variable [IsIntegral T]

def AdditiveLaw : Prop :=
  ∀ (S : ShortComplex T.Modules), S.ShortExact → ∀ r₁ r₂ r₃ : ℕ,
    IsVB S.X₁ r₁ → IsVB S.X₂ r₂ → IsVB S.X₃ r₃ →
      degCh2 k S.X₂ = degCh2 k S.X₁ + degCh2 k S.X₃

def DualLaw : Prop :=
  ∀ (E : T.Modules) (r : ℕ), IsVB E r → degCh2 k (dual E) = degCh2 k E

def FrobeniusLaw (p : ℕ) [Fact p.Prime] [CharP k p] : Prop :=
  ∀ (E : T.Modules) (r : ℕ), IsVB E r →
    degCh2 k ((frobPull p (natCast_eq_zero T p k)).obj E) = (p : ℚ) ^ 2 * degCh2 k E

end Defs

def Statement : Prop :=
  ∀ (k : Type) [Field k] (T : Scheme.{0}) [Algebra k Γ(T, ⊤)] [IsIntegral T], IsProjSurface k T →
    AdditiveLaw k T ∧ DualLaw k T ∧ ∀ (p : ℕ) [Fact p.Prime] [CharP k p], FrobeniusLaw k T p

def StatementPrimeField : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (T : Scheme.{0}) [Algebra (ZMod p) Γ(T, ⊤)] [IsIntegral T],
    IsProjSurface (ZMod p) T →
      AdditiveLaw (ZMod p) T ∧ DualLaw (ZMod p) T ∧ FrobeniusLaw (ZMod p) T p

theorem Statement.primeField (h : Statement) : StatementPrimeField := fun p _ T _ _ hT =>
  ⟨(h _ T hT).1, (h _ T hT).2.1, (h _ T hT).2.2 p⟩

inductive HasFlag {T : Scheme.{0}} : T.Modules → List (LB T) → Prop

  | nil {E : T.Modules} (h : IsZero E) : HasFlag E []

  | cons {L : LB T} {l : List (LB T)} (S : ShortComplex T.Modules) (hS : S.ShortExact)
      (hL : L.IsLB) (e : S.X₃ ≅ toMod L) (h : HasFlag S.X₁ l) : HasFlag S.X₂ (L :: l)

structure IsGenFinite {T' T : Scheme.{0}} [IsIntegral T'] (ρ : T' ⟶ T) (d : ℕ) : Prop where

  isDominant : IsDominant ρ

  pos : 0 < d

  finrank_eq : letI := (ρ.stalkMap (genericPoint T')).hom.toAlgebra
    Module.finrank (T.presheaf.stalk (ρ (genericPoint T')))
      (T'.presheaf.stalk (genericPoint T')) = d

section Covers

variable (k : Type) [Field k] (T : Scheme.{0}) [Algebra k Γ(T, ⊤)] [IsIntegral T]

def PullbackLaw : Prop :=
  ∀ (T' : Scheme.{0}) [Algebra k Γ(T', ⊤)] [IsIntegral T'], IsProjSurface k T' →
    ∀ (ρ : T' ⟶ T) (d : ℕ), ρ ≫ strHom k T = strHom k T' → IsGenFinite ρ d →
      ∀ (E : T.Modules) (r : ℕ), IsVB E r →
        degCh2 k ((Scheme.Modules.pullback ρ).obj E) = d * degCh2 k E

def FlagLaw : Prop :=
  ∀ (E : T.Modules) (l : List (LB T)), HasFlag E l →
    degCh2 k E = (l.map fun L => (interNum k (structureModule T) ![L, L] : ℚ) / 2).sum

def FlagCoverExists : Prop :=
  ∀ (E : T.Modules) (r : ℕ), IsVB E r →
    ∃ (T' : Scheme.{0}) (_ : Algebra k Γ(T', ⊤)) (_ : IsIntegral T') (ρ : T' ⟶ T) (d : ℕ)
      (l : List (LB T')), IsProjSurface k T' ∧ ρ ≫ strHom k T = strHom k T' ∧ IsGenFinite ρ d ∧
        HasFlag ((Scheme.Modules.pullback ρ).obj E) l

end Covers

def CoverStatement : Prop :=
  ∀ (k : Type) [Field k] (T : Scheme.{0}) [Algebra k Γ(T, ⊤)] [IsIntegral T], IsProjSurface k T →
    PullbackLaw k T ∧ FlagLaw k T ∧ FlagCoverExists k T

section Checks

variable {k : Type} [Field k] {T : Scheme.{0}} [Algebra k Γ(T, ⊤)] {E F : T.Modules} {r : ℕ}

theorem IsProjSurface.finiteCoh (hT : IsProjSurface k T) (h : IsVB E r) :
    FiniteCoh k E ∧ FiniteCoh k (dual E) ∧ FiniteCoh k (structureModule T) :=
  have := h.isFiniteQC
  have := h.dual.isFiniteQC
  have := (isVB_structureModule T).isFiniteQC
  ⟨finiteCoh_of_isProjOver (algebraMap_eq_strHom k T) _ hT.isProjOver,
    finiteCoh_of_isProjOver (algebraMap_eq_strHom k T) _ hT.isProjOver,
    finiteCoh_of_isProjOver (algebraMap_eq_strHom k T) _ hT.isProjOver⟩

variable [IsIntegral T]

theorem degCh2_eq (h : IsVB E r) : degCh2 k E =
    ((chi k E : ℚ) + chi k (dual E)) / 2 - r * (chi k (structureModule T) : ℚ) := by
  rw [degCh2, h.genRank_eq]

theorem degCh2_congr (φ : E ≅ F) : degCh2 k E = degCh2 k F := by
  have ψ : dual F ≅ dual E := (dualFunctor T).mapIso φ.op
  rw [degCh2, degCh2, chi_congr k φ, chi_congr k ψ, genRank_congr φ]

variable (k T) in

theorem dualLaw : DualLaw k T := fun E r h => by
  have := h.isIso_toBidual_of_local_frames
  rw [degCh2_eq h, degCh2_eq h.dual, ← chi_congr k (asIso (cartierDualToBidual E)), add_comm]

theorem IsProjSurface.degCh2_toMod (hT : IsProjSurface k T) {L : LB T} (hL : L.IsLB) :
    degCh2 k (toMod L) = (interNum k (structureModule T) ![L, L] : ℚ) / 2 := by
  have := (isVB_structureModule T).isFiniteQC
  have h := isVB_toMod hL
  have hv : DiffVanish (2 + 1) (chiPic k (structureModule T)) :=
    diffVanish_chiPic_of_isProjOver (algebraMap_eq_strHom k T) _ hT.isProjOver
      (by rw [QCoh.suppDim_structureModule, hT.dim_eq]; rfl)
  set f := chiPic k (structureModule T) with hf
  set c := CechPic.cls L hL with hc
  have e₁ : chi k (toMod L) = f c := (chi_congr k (Twist.unitTwistIso L)).symm
  have e₂ : chi k (dual (toMod L)) = f (-c) := by
    have : CechPic.cls _ h.dual.isLB_det = -c := by
      rw [← (CechPic.cls_eq_iff (CechPic.isLB_dual h.isLB_det) _).2 h.lbIso_det_dual,
        CechPic.cls_dual h.isLB_det, hc, (CechPic.cls_eq_iff hL h.isLB_det).2 (lbIso_det_toMod hL)]
    rw [← this, chi_congr k h.dual.isoDet]
    exact (chi_congr k (Twist.unitTwistIso _)).symm
  have e₃ : chi k (structureModule T) = f 0 := (chiPic_zero k _).symm
  have hLL : ∀ i, ((![L, L] : Fin 2 → LB T) i).IsLB := fun i => by fin_cases i <;> exact hL
  have e₄ : interNum k (structureModule T) ![L, L] = f 0 - f (-c) - (f (-c) - f (-c - c)) := by
    rw [interNum_eq_multiDiff k _ hLL, show (fun i => CechPic.cls _ (hLL i)) = fun _ : Fin 2 => c from
      funext fun i => by fin_cases i <;> rfl, multiDiff_const]
    simp [bwdDiff_apply, hf]
  have e₅ := congrFun (hv.multiDiff_eq_zero (g := fun _ : Fin 3 => c) (by simp)) c
  rw [multiDiff_const] at e₅
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp, id, bwdDiff_apply,
    sub_self, zero_sub, Pi.zero_apply] at e₅
  rw [degCh2_eq h, e₁, e₂, e₃, e₄]
  have e₆ : f c + f (-c) - 2 * f 0 = f 0 - f (-c) - (f (-c) - f (-c - c)) := by linarith
  rw [← e₆]
  push_cast
  ring

theorem isGenFinite_id : IsGenFinite (𝟙 T) 1 := by
  refine ⟨inferInstance, one_pos, ?_⟩
  letI := ((𝟙 T : T ⟶ T).stalkMap (genericPoint T)).hom.toAlgebra
  exact Module.finrank_of_bijective_algebraMap
    (ConcreteCategory.bijective_of_isIso ((𝟙 T : T ⟶ T).stalkMap (genericPoint T)))

open ProjSpace ProjCoh in

theorem isProjSurface_plane (k : Type) [Field k] : IsProjSurface k (PSpace k 2) :=
  ⟨inferInstance, topologicalKrullDim_eq k 2,
    strHom_eq (algebraMap_top_eq k 2) ▸ isProjOver_str k 2⟩

open ProjSpace ProjCoh in

theorem degree_ch2_projective_plane_O1 (k : Type) [Field k] : degCh2 k (toMod (On k 2 1)) = 1 / 2 := by
  have hL := On_isLB k 2 1
  have h := isVB_toMod hL
  have e₀ : chi k (structureModule (PSpace k 2)) = 1 := by
    rw [chi_congr k (Twist.twistZZeroIso (structureModule _) (O1_isLB k 2))]
    exact (chi_sheafO k 2 0).trans (by decide)
  have e₁ : chi k (toMod (On k 2 1)) = 3 :=
    (chi_congr k (sheafOIso k 2 1)).symm.trans ((chi_sheafO k 2 1).trans (by decide))
  have e₂ : chi k (dual (toMod (On k 2 1))) = 0 := by
    have : CechPic.cls _ h.dual.isLB_det = CechPic.cls _ (On_isLB k 2 (-1)) := by
      rw [← (CechPic.cls_eq_iff (CechPic.isLB_dual h.isLB_det) _).2 h.lbIso_det_dual,
        CechPic.cls_dual h.isLB_det, ← (CechPic.cls_eq_iff hL h.isLB_det).2 (lbIso_det_toMod hL)]
      exact ((congrArg Neg.neg (cls_lbZPow (O1_isLB k 2) 1 hL)).trans (neg_smul _ _).symm).trans
        (cls_lbZPow (O1_isLB k 2) (-1) _).symm
    obtain ⟨φ⟩ := LB.nonempty_iso_of_lbIso h.dual.isLB_det (On_isLB k 2 (-1))
      ((CechPic.cls_eq_iff _ _).1 this)
    rw [chi_congr k (h.dual.isoDet ≪≫ φ ≪≫ (sheafOIso k 2 (-1)).symm)]
    exact (chi_sheafO k 2 (-1)).trans (by decide)
  rw [degCh2_eq h, e₀, e₁, e₂]
  norm_num

omit [IsIntegral T] in
open ZeroObject in

theorem hasFlag_biprod {L M : LB T} (hL : L.IsLB) (hM : M.IsLB) :
    HasFlag (toMod L ⊞ toMod M) [M, L] := by
  have h₁ : HasFlag (toMod L) [L] :=
    HasFlag.cons (ShortComplex.mk (0 : (0 : T.Modules) ⟶ toMod L) (𝟙 _) (by simp))
      { exact := (ShortComplex.exact_iff_mono _ rfl).2 inferInstance
        mono_f := (isZero_zero _).mono _
        epi_g := inferInstance } hL (Iso.refl _) (.nil (isZero_zero _))
  exact HasFlag.cons _ (ShortComplex.Splitting.ofHasBinaryBiproduct (toMod L) (toMod M)).shortExact
    hM (Iso.refl _) h₁

end Checks

end GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps
end
end

