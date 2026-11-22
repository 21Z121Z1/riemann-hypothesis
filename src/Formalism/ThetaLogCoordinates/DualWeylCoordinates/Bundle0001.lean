import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DefsMod

-- bundled from Formalism.ThetaLogCoordinates.DualWeylCoordinates.StatementA
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

def LemmaA : Prop :=
  ∀ (n : ℕ) [NeZero n] (mu : Fin n → ℤ), Dominant mu → ∀ (F : Type) [Field F],
    LinearIndependent F (fun I : {I : TIdx mu // StdT I} => mapCoord (n := n) F (brk mu I.1))

def SBasis : Prop :=
  ∀ (n : ℕ) [NeZero n] (mu : Fin n → ℤ), Dominant mu →
    LinearIndependent ℤ (fun I : {I : TIdx mu // StdT I} => brk mu I.1) ∧
    Submodule.span ℤ (Set.range fun I : {I : TIdx mu // StdT I} => brk mu I.1) = SMu mu

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

-- bundled from Formalism.ThetaLogCoordinates.DualWeylCoordinates.StatementB
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

def ColumnFamilyStandardVectorsBasis : Prop :=
  ∀ (n : ℕ) [NeZero n] (M : GLMod n) (CF : ColFam M),
    (LinearIndependent ℤ (fun x : (Σ j, {I : TIdx (CF.mu j) // StdT I}) => CF.vec x.1 x.2.1) ∧
      Submodule.span ℤ (Set.range fun x : (Σ j, {I : TIdx (CF.mu j) // StdT I}) => CF.vec x.1 x.2.1) = ⊤) ∧
    ∀ (R : Type) [CommRing R],
      LinearIndependent R (fun x : (Σ j, {I : TIdx (CF.mu j) // StdT I}) => fun i => (CF.vec x.1 x.2.1 i : R)) ∧
      Submodule.span R (Set.range fun x : (Σ j, {I : TIdx (CF.mu j) // StdT I}) =>
        fun i => (CF.vec x.1 x.2.1 i : R)) = ⊤

def ColumnFamilyFiltrationProperties : Prop :=
  ∀ (n : ℕ) [NeZero n] (M : GLMod n) (CF : ColFam M) (pi : Set (Fin n → ℤ)), DomLowerSet pi →
    CF.Mpi pi = Submodule.span ℤ {x | ∃ j, CF.mu j ∈ pi ∧ ∃ I : TIdx (CF.mu j), StdT I ∧ x = CF.vec j I} ∧
    (∀ x : M.ι → ℤ, x ∈ CF.Mpi pi ↔ (fun i => (x i : ℚ)) ∈ typeSum M pi) ∧
    (∀ x ∈ CF.Mpi pi, ∀ ℓ : GLCoord ℤ n →ₗ[ℤ] ℤ,
      (fun i => ℓ (Matrix.mulVec M.A (fun j => ((x j : ℤ) : GLCoord ℤ n)) i)) ∈ CF.Mpi pi) ∧
    (∃ C : Submodule ℤ (M.ι → ℤ), IsCompl (CF.Mpi pi) C) ∧
    ∀ mu ∈ pi, (∀ nu ∈ pi, DomLE mu nu → nu = mu) →
      (∃ Φ : (↥(CF.Mpi pi) ⧸ (CF.Mpi (pi \ {mu})).comap (CF.Mpi pi).subtype) ≃ₗ[ℤ]
          TensorProduct ℤ ↥(SMu mu) ↥(CF.MM mu),
        ∀ (j : CF.J) (I : TIdx (CF.mu j)) (x : ↥(CF.Mpi pi)) (y : ↥(SMu mu)) (z : ↥(CF.MM mu)),
          CF.mu j = mu → StdT I → x.1 = CF.vec j I → y.1 = brk (CF.mu j) I → z.1 = CF.vec j (canT (CF.mu j)) →
          Φ (Submodule.Quotient.mk x) = y ⊗ₜ z) ∧
      (CF.MM mu : Set (M.ι → ℤ)) = {x | IsHighest M ℤ mu x}

def FiltrationGenericPointCriterion : Prop :=
  ∀ (n : ℕ) [NeZero n] (M : GLMod n) (CF : ColFam M) (pi : Set (Fin n → ℤ)), DomLowerSet pi →
    ∀ (F : Type) [Field F] (x : M.ι → F),
      x ∈ Submodule.span F {y | ∃ j, CF.mu j ∈ pi ∧ ∃ I : TIdx (CF.mu j), StdT I ∧ y = fun i => (CF.vec j I i : F)} ↔
      ∀ mu, Dominant mu → mu ∉ pi →
        Matrix.mulVec ((prMu M mu).map (Int.castRingHom (GLCoord F n)))
          (Matrix.mulVec (M.A.map (mapCoord F)) (fun i => algebraMap F (GLCoord F n) (x i))) = 0

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

-- bundled from Formalism.ThetaLogCoordinates.DualWeylCoordinates.StatementC
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

def ClosureBasicModules : Prop :=
  ∀ (n : ℕ) [NeZero n],
    (∀ M : GLMod n, Fintype.card M.ι = 1 → (∀ i j, M.A i j = 1) → Nonempty (ColFam M)) ∧
    (∀ (M : GLMod n) (mu : Fin n → ℤ) (β : M.ι → GLCoord ℤ n), Dominant mu → IsSMu M mu β → Nonempty (ColFam M)) ∧
    ∀ (M M' : GLMod n) (ε : ℤ), (ε = 1 ∨ ε = -1) → ∀ e : M'.ι ≃ M.ι,
      (∀ i j, M'.A i j = ((detU n ^ ε : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) * M.A (e i) (e j)) →
      Nonempty (ColFam M) → Nonempty (ColFam M')

def ClosureTensorPowers : Prop :=
  ∀ (n : ℕ) [NeZero n] (M M' : GLMod n) (b : ℕ), Nonempty (ColFam M) →
    (∀ e, IsTensor M M' (SymMat n b) e → Nonempty (ColFam M')) ∧
    (∀ e, IsTensor M M' (SymDMat n b) e → Nonempty (ColFam M')) ∧
    (∀ e, IsTensor M M' (LamMat n b) e → Nonempty (ColFam M'))

def ClosureBranching : Prop :=
  ∀ (m : ℕ) [NeZero m] (M : GLMod (m + 1)) (lam : Fin (m + 1) → ℤ) (β : M.ι → GLCoord ℤ (m + 1)),
    Dominant lam → IsSMu M lam β →
    ∃ (Sg : Finset (Fin m → ℤ)) (ph : (nu : ↥Sg) → Matrix M.ι (TIdx (nu : Fin m → ℤ)) ℤ),
      (∀ nu : Fin m → ℤ, nu ∈ Sg ↔ Dominant nu ∧ Interl lam nu) ∧
      (∀ (nu : ↥Sg) (R : Type) [CommRing R] (h : GL (Fin (m + 1)) R) (g1 : GL (Fin m) R) (t : Rˣ), IsBlock h g1 t →
        M.A.map (evGL h) * (ph nu).map (Int.castRingHom R) =
          (((t ^ (∑ a, lam a - ∑ a, (nu : Fin m → ℤ) a) : Rˣ) : R)) • ((ph nu).map (Int.castRingHom R) *
            (TMat (nu : Fin m → ℤ)).map (evGL g1))) ∧
      (∀ nu : ↥Sg, (∀ (p : ℕ), p.Prime → (fun i => ((ph nu i (canT _) : ℤ) : ZMod p)) ≠ 0) ∧
        (fun i => ((ph nu i (canT _) : ℤ) : ℚ)) ≠ 0) ∧
      Fintype.card M.ι = ∑ nu : ↥Sg, dMu (nu : Fin m → ℤ)

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

-- bundled from Formalism.ThetaLogCoordinates.DualWeylCoordinates.StatementH
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

def InducedSectionsSpanStatement : Prop :=
  ∀ (n : ℕ) [NeZero n] (mu : Fin n → ℤ) (R : Type) [CommRing R] [IsDomain R],
    (IsField R ∨ IsDiscreteValuationRing R ∨ Nonempty (R ≃+* ℤ)) →
    (Dominant mu → inducedSections R mu = (Submodule.span R (Set.range fun I : TIdx mu => mapCoord (n := n) R (brk mu I)) : Set _)) ∧
    (¬ Dominant mu → inducedSections R mu = {0})

def RationalBitableauLatticeStatement : Prop :=
  ∀ (n : ℕ) [NeZero n] (mu : Fin n → ℤ), Dominant mu →
    (Submodule.span ℤ (Set.range fun I : TIdx mu => MvPolynomial.map (Int.castRingHom ℚ) (brkPol mu I)) :
        Set (MvPolynomial (Fin n × Fin n) ℚ)) =
      {x | x ∈ Submodule.span ℚ (Set.range fun I : TIdx mu => MvPolynomial.map (Int.castRingHom ℚ) (brkPol mu I)) ∧
        x ∈ Nabla (O := ℤ) (glOps ℚ n (rowLetters n) Set.univ) (fun a => mu a + ((-(mu (lastIdx n))).toNat : ℤ))
          (MvPolynomial.map (Int.castRingHom ℚ) (brkPol mu (canT mu)))}

def WeightLatticeSaturationStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    (_S : UniformizedDVR p O) (n : ℕ) (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V]
    [IsScalarTower O (KK O) V] (E : GLOps n (KK O) V) (mu : Fin n → ℤ) (La : Submodule O V),
    IsGLRep E → Dominant mu → isoSub E mu = ⊤ → UZLattice E La →
    (∀ x ∈ La, ∀ nu e, IsWtProj E nu e → e x ∈ La) →
    Submodule.span O {x | ∃ u ∈ UZmon E, ∃ y ∈ La, y ∈ weightSp E mu ∧ x = u y} ≤ La ∧
    ∀ y ∈ La, ∀ u ∈ UZmon E, ∀ e, IsWtProj E mu e → e (u y) ∈ La ∧ e (u y) ∈ weightSp E mu

def dualOps {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V) :
    GLOps n K (Module.Dual K V) := fun a b => -(LinearMap.dualMap (E a b))

def MinimalLatticeDualityStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    (_S : UniformizedDVR p O) (n : ℕ) (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V]
    [IsScalarTower O (KK O) V] (E : GLOps n (KK O) V) (mu : Fin n → ℤ) (v : V) (v' : Module.Dual (KK O) V),
    IsIrrHW E mu v → IsHWV (dualOps E) (dualWt mu) v' →
    v' '' (Delta (O := O) E v : Set V) = Set.range (algebraMap O (KK O)) →
    (Delta (O := O) E v : Set V) =
      {x | ∀ φ ∈ Nabla (O := O) (dualOps E) (dualWt mu) v', φ x ∈ Set.range (algebraMap O (KK O))}

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

