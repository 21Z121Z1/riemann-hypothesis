import Mathlib
import Formalism.LocalRingCardinality.DataLevel
import Formalism.LocalRingCardinality.Bundle0001
import Formalism.SatakeDualWeyl.Bundle0001
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SplittingProjection
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions
open scoped TensorProduct

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def IsSplitting (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))
    (φ : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F) : Prop :=
  (∀ a : v.adicCompletion F, φ ((1 : E) ⊗ₜ[F] a) = (a, a)) ∧
  (∀ x, φ (sigR σ (v.adicCompletion F) x) = swapR _ (φ x)) ∧
  (∀ x, x ∈ intV E v ↔
    (φ x).1 ∈ v.adicCompletionIntegers F ∧ (φ x).2 ∈ v.adicCompletionIntegers F)

variable {v : HeightOneSpectrum (𝓞 F)}
  (φ : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)

def prP : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F := (RingHom.fst _ _).comp φ.toRingHom

def prPbar : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F := (RingHom.snd _ _).comp φ.toRingHom

def primeOf (p : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F) : Ideal (intV E v) :=
  Ideal.span {a : intV E v | Valued.v (p a) < 1}

def partOf {n : Type} (p : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F)
    (Λ : Submodule (intV E v) (n → E ⊗[F] v.adicCompletion F)) :
    Submodule (v.adicCompletionIntegers F) (n → v.adicCompletion F) :=
  Submodule.span (v.adicCompletionIntegers F)
    ((fun x : n → E ⊗[F] v.adicCompletion F => fun i => p (x i)) '' (Λ : Set _))

abbrev locLat {n : Type} [Fintype n] [DecidableEq n] (v : HeightOneSpectrum (𝓞 F))
    (Λ : Submodule (𝓞 E) (n → E)) : Submodule (intV E v) (n → E ⊗[F] v.adicCompletion F) :=
  latS (F := F) (v.adicCompletion F) (intV E v) Λ

theorem mem_primeOf_prP {σ : E →ₐ[F] E} (hφ : IsSplitting σ v φ) (a : intV E v) :
    a ∈ primeOf (prP φ) ↔ Valued.v (prP φ a) < 1 := by
  refine ⟨fun h => ?_, fun h => Ideal.subset_span h⟩
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Subring.coe_add, map_add]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hx hy)
  | smul c x _ hx =>
    have hc : Valued.v (prP φ c) ≤ 1 := ((hφ.2.2 c).1 c.2).1
    rw [smul_eq_mul, Subring.coe_mul, map_mul, map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right hc zero_le' hx

theorem primeOf_prP_ne_top {σ : E →ₐ[F] E} (hφ : IsSplitting σ v φ) : primeOf (prP φ) ≠ ⊤ := by
  rw [Ideal.ne_top_iff_one, mem_primeOf_prP φ hφ]
  simp

end Local

section Level

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι : Type} [Fintype ι] {hc : ι → HCParam R} {C : ColumnChain R ι hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}

abbrev dualLb (L : ColLevel R F E sp gp C A clsLat) : Submodule (𝓞 E) (Fin R.k → E) :=
  Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) sp.gram0 L.Lb)

def IsOverLattice (L : ColLevel R F E sp gp C A clsLat) (N : Submodule (𝓞 E) (Fin R.k → E)) : Prop :=
  Module.Finite (𝓞 E) N ∧ Submodule.span E (N : Set (Fin R.k → E)) = ⊤ ∧
  dualSet (sp.cm.sig : E →+* E) sp.gram0 N = (N : Set (Fin R.k → E)) ∧
  L.Lb ≤ N ∧ N ≤ dualLb L ∧
  ∀ v : HeightOneSpectrum (𝓞 F), (A.T : 𝓞 F) ∉ v.asIdeal → locLat v N = locLat v L.Lb

def LocalAtT (L : ColLevel R F E sp gp C A clsLat) (N : Submodule (𝓞 E) (Fin R.k → E))
    (v : HeightOneSpectrum (𝓞 F)) (h : (A.T : 𝓞 F) ∈ v.asIdeal)
    (φ : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F) : Prop :=

  IsSplitting sp.cm.sig v φ ∧

  (∀ x : locLat v (dualLb L), (∀ i, prP φ (x.1 i) = 0) → L.fT v h x = 0) ∧

  Nonempty ((locLat v (dualLb L) ⧸ (locLat v L.Lb).submoduleOf (locLat v (dualLb L))) ≃ₗ[intV E v]
    (intV E v ⧸ primeOf (prP φ)) × (intV E v ⧸ primeOf (prPbar φ))) ∧

  partOf (prP φ) (locLat v N) = partOf (prP φ) (locLat v (dualLb L)) ∧
  partOf (prPbar φ) (locLat v N) = partOf (prPbar φ) (locLat v L.Lb) ∧

  (∀ g' : GL (Fin R.k) (v.adicCompletion F),
    ∃! g : UPts sp.cm.sig sp.gram0 (v.adicCompletion F), bc (prP φ) g.1 = g') ∧

  (∀ g ∈ UPts sp.cm.sig sp.gram0 (v.adicCompletion F),
    g ∈ levelVL sp.cm.sig sp.gram0 v N ↔ bc (prP φ) g ∈ stabGL (partOf (prP φ) (locLat v N))) ∧

  (∃ b : GL (Fin R.k) (v.adicCompletion F),
    (∀ y : Fin R.k → v.adicCompletion F,
      (b : Matrix (Fin R.k) (Fin R.k) (v.adicCompletion F)) *ᵥ y ∈ partOf (prP φ) (locLat v N) ↔
        ∀ i, y i ∈ v.adicCompletionIntegers F) ∧
    ∀ g ∈ UPts sp.cm.sig sp.gram0 (v.adicCompletion F),
      g ∈ levelVL sp.cm.sig sp.gram0 v N ↔ b⁻¹ * bc (prP φ) g * b ∈
        (bc (n := Fin R.k) (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))).range) ∧

  ∃ (f : partOf (prP φ) (locLat v N) →ₗ[v.adicCompletionIntegers F]
      IsLocalRing.ResidueField (v.adicCompletionIntegers F))
    (ε : L.fM v h ≃+ IsLocalRing.ResidueField (v.adicCompletionIntegers F)),
    (∀ (a : intV E v) (a' : v.adicCompletionIntegers F), (a' : v.adicCompletion F) = prP φ a →
      ∀ m, ε (a • m) = a' • ε m) ∧
    (∀ (x : locLat v (dualLb L)) (y : partOf (prP φ) (locLat v N)),
      (∀ i, y.1 i = prP φ (x.1 i)) → f y = ε (L.fT v h x)) ∧
    f ≠ 0 ∧
    (∀ y, f ((A.T : v.adicCompletionIntegers F) • y) = 0) ∧
    (∀ y, f y = 0 ↔ y.1 ∈ partOf (prP φ) (locLat v L.Lb)) ∧
    ∀ g, g ∈ L.Uloc v ↔
      g ∈ levelVL sp.cm.sig sp.gram0 v N ∧ bc (prP φ) g ∈ stabFun (partOf (prP φ) (locLat v N)) f

def HasOverLattice (L : ColLevel R F E sp gp C A clsLat) : Prop :=
  (∀ i : Fin 2, A.T ≠ gp i) ∧
  ∃ N : Submodule (𝓞 E) (Fin R.k → E), IsOverLattice L N ∧
    (∀ (v : HeightOneSpectrum (𝓞 F)) (h : (A.T : 𝓞 F) ∈ v.asIdeal), ∃ φ, LocalAtT L N v h φ) ∧
    (∀ v, L.Uloc v ≤ levelVL sp.cm.sig sp.gram0 v N) ∧
    L.U ≤ levelAfL sp.cm.sig sp.gram0 N

def IndexAtT (L : ColLevel R F E sp gp C A clsLat) : Prop :=
  ∀ N, IsOverLattice L N → ∀ (v : HeightOneSpectrum (𝓞 F)) (h : (A.T : 𝓞 F) ∈ v.asIdeal) φ,
    LocalAtT L N v h φ → (L.Uloc v).relIndex (levelVL sp.cm.sig sp.gram0 v N) = A.T ^ R.k - 1

end Level

def SelfDualOverBase : Prop :=
  ∀ (D : D7) (Lv : LevelData D) (u : D.what₂.Word),
    letI := D.host.cmStar
    Formalism.MainNotions.StandardLattice.SplitsF D (D.mem u).A.T → HasOverLattice (Lv u)

def IndexOverBase : Prop :=
  ∀ (D : D7) (Lv : LevelData D) (u : D.what₂.Word),
    letI := D.host.cmStar
    Formalism.MainNotions.StandardLattice.SplitsF D (D.mem u).A.T → IndexAtT (Lv u)

end GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.StabilizerCompletions
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeOrthogonalParts

open scoped TensorProduct Pointwise
open NumberField IsDedekindDomain
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice

def UnramifiedAtFinite (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] : Prop :=
  ∀ P : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 F) P.asIdeal

section Lattice

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

def IsSelfDualLattice (L : Submodule (𝓞 E) (Fin M → E)) : Prop :=
  L.FG ∧ Submodule.span E (L : Set (Fin M → E)) = ⊤ ∧
    ∀ y : Fin M → E, y ∈ L ↔ ∀ x ∈ L, IsIntegral ℤ (hE σ J x y)

def perpPart (L : Set (Fin M → E)) (x : Fin M → E) : Set (Fin M → E) :=
  {y | y ∈ L ∧ hE σ J x y = 0}

def actVec (k : HA (Af F) σ J) (y : Fin M → Af F ⊗[F] E) : Fin M → Af F ⊗[F] E :=
  ((HA.mat (Af F) σ J k : GL (Fin M) (Af F ⊗[F] E)) :
    Matrix (Fin M) (Fin M) (Af F ⊗[F] E)).mulVec y

def ratVec (F : Type) [Field F] [NumberField F] [Algebra F E] (x : Fin M → E) :
    Fin M → Af F ⊗[F] E := fun i => inclR (Af F) (x i)

omit [NumberField E] in
theorem actVec_one (y : Fin M → Af F ⊗[F] E) : actVec σ J 1 y = y := by
  show ((1 : GL (Fin M) (Af F ⊗[F] E)) : Matrix (Fin M) (Fin M) _).mulVec y = y
  simp

omit [NumberField E] in
theorem actVec_mul (g k : HA (Af F) σ J) (y : Fin M → Af F ⊗[F] E) :
    actVec σ J (g * k) y = actVec σ J g (actVec σ J k y) := by
  show (((HA.mat (Af F) σ J g) * (HA.mat (Af F) σ J k) : GL (Fin M) (Af F ⊗[F] E)) :
      Matrix (Fin M) (Fin M) _).mulVec y = _
  unfold actVec
  rw [Units.val_mul, Matrix.mulVec_mulVec]

def stabHat (L : Set (Fin M → E)) : Subgroup (HA (Af F) σ J) where
  carrier := {k | ∀ y, y ∈ latHat F E L ↔ actVec σ J k y ∈ latHat F E L}
  one_mem' := by intro y; rw [actVec_one]
  mul_mem' := by
    intro a b ha hb y
    rw [actVec_mul]
    exact (hb y).trans (ha _)
  inv_mem' := by
    intro g hg y
    have := hg (actVec σ J g⁻¹ y)
    rw [← actVec_mul, mul_inv_cancel, actVec_one] at this
    exact this.symm

abbrev stabVec (x : Fin M → E) : Subgroup (HA (Af F) σ J) := Hstab (Af F) σ J (fun _ => x)

def OrbitClaims (L : Set (Fin M → E)) (x : Fin M → E) (β : F) : Prop :=
  (∀ y ∈ latHat F E L, qR (Af F) σ J y = algebraMap F (Af F) β →
    ∃ k ∈ stabHat σ J L, actVec σ J k (ratVec F x) = y) ∧
  {h : HA (Af F) σ J | actVec σ J h⁻¹ (ratVec F x) ∈ latHat F E L} =
    (stabVec σ J x : Set (HA (Af F) σ J)) * (stabHat σ J L : Set (HA (Af F) σ J)) ∧
  stabHat σ J L ⊓ stabVec σ J x = stabHat σ J (perpPart σ J L x) ⊓ stabVec σ J x

end Lattice

def StabTransitive : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → UnramifiedAtFinite F E →
    ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ L : Submodule (𝓞 E) (Fin M → E), IsSelfDualLattice σ J L →
    ∀ (β : F), (β = 1 ∨ β = -1) →
    ∀ x ∈ L, hE σ J x x = algebraMap F E β →
      OrbitClaims σ J (L : Set (Fin M → E)) x β

section Basic₂

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

omit [NumberField E] in

theorem mem_stabVec (x : Fin M → E) (k : HA (Af F) σ J) :
    k ∈ stabVec σ J x ↔ actVec σ J k (ratVec F x) = ratVec F x := by
  constructor
  · intro h
    exact congrFun (MulAction.mem_stabilizer_iff.1 h) 0
  · intro h
    exact MulAction.mem_stabilizer_iff.2 (funext fun _ => h)

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeOrthogonalParts
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.StabilizerLattices
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers

open scoped TensorProduct Pointwise
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice

section Lat

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def IsSelfDualLat (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (L : Submodule (𝓞 E) (Fin M → E)) : Prop :=
  L.FG ∧ Submodule.span E (L : Set (Fin M → E)) = ⊤ ∧
    ∀ y : Fin M → E, y ∈ L ↔ ∀ x ∈ L, IsIntegral ℤ (hE σ J x y)

def perpIn (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (L : Submodule (𝓞 E) (Fin M → E)) (x : Fin M → E) : Set (Fin M → E) :=
  {y | y ∈ L ∧ hE σ J x y = 0}

variable (R : Type) [CommRing R] [Algebra F R]

def actV (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (h : HA R σ J)
    (y : Fin M → R ⊗[F] E) : Fin M → R ⊗[F] E :=
  (h • (fun _ => y : Fin 1 → Fin M → R ⊗[F] E)) 0

theorem actV_eq (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (h : HA R σ J)
    (y : Fin M → R ⊗[F] E) :
    actV R σ J h y = ((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) :
      Matrix (Fin M) (Fin M) (R ⊗[F] E)).mulVec y := rfl

theorem actV_one (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (y : Fin M → R ⊗[F] E) : actV R σ J 1 y = y := by
  unfold actV
  rw [one_smul]

theorem actV_mul (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (g h : HA R σ J)
    (y : Fin M → R ⊗[F] E) : actV R σ J (g * h) y = actV R σ J g (actV R σ J h y) := by
  unfold actV
  rw [mul_smul]
  rfl

def stabLat (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (Λ : AddSubgroup (Fin M → R ⊗[F] E)) : Subgroup (HA R σ J) where
  carrier := {h | ∀ y, y ∈ Λ ↔ actV R σ J h y ∈ Λ}
  one_mem' := by intro y; rw [actV_one]
  mul_mem' := by
    intro a b ha hb y
    rw [actV_mul]
    exact (hb y).trans (ha _)
  inv_mem' := by
    intro g hg y
    have := hg (actV R σ J g⁻¹ y)
    rw [← actV_mul, mul_inv_cancel, actV_one] at this
    exact this.symm

end Lat

def UnramifiedAtFinite (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] : Prop :=
  ∀ (P : Ideal (𝓞 E)) [P.IsPrime], P ≠ ⊥ → Algebra.IsUnramifiedAt (𝓞 F) P

def OrbitConcl (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (L : Submodule (𝓞 E) (Fin M → E)) (x : Fin M → E) (β : F) : Prop :=
  (∀ y ∈ latHat F E (L : Set (Fin M → E)), qR (Af F) σ J y = algebraMap F (Af F) β →
      ∃ k ∈ stabLat (Af F) σ J (latHat F E (L : Set (Fin M → E))),
        actV (Af F) σ J k (fun i => inclR (F := F) (Af F) (x i)) = y) ∧
  ({h : HA (Af F) σ J | actV (Af F) σ J h⁻¹ (fun i => inclR (F := F) (Af F) (x i)) ∈
        latHat F E (L : Set (Fin M → E))} =
      (Hstab (Af F) σ J (fun _ => x) : Set (HA (Af F) σ J)) *
        (stabLat (Af F) σ J (latHat F E (L : Set (Fin M → E))) : Set (HA (Af F) σ J))) ∧
  (stabLat (Af F) σ J (latHat F E (L : Set (Fin M → E))) ⊓ Hstab (Af F) σ J (fun _ => x) =
      stabLat (Af F) σ J (latHat F E (perpIn σ J L x)) ⊓ Hstab (Af F) σ J (fun _ => x))

def StabTransitive : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → UnramifiedAtFinite F E →
    ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ L : Submodule (𝓞 E) (Fin M → E), IsSelfDualLat σ J L →
    ∀ β : F, (β = 1 ∨ β = -1) →
    ∀ x ∈ L, hE σ J x x = algebraMap F E β → OrbitConcl F E σ J L x β

example (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] {M : ℕ}
    (L : Submodule (𝓞 E) (Fin M → E)) (x : Fin M → E) (hx : x ∈ L) :
    (fun i => inclR (F := F) (Af F) (x i)) ∈ latHat F E (L : Set (Fin M → E)) :=
  AddSubgroup.subset_closure ⟨1, fun v => by rw [map_one]; exact one_mem _, x, hx, rfl⟩

def stdLat (E : Type) [Field E] (M : ℕ) : Submodule (𝓞 E) (Fin M → E) :=
  Submodule.span (𝓞 E) (Set.range fun i : Fin M => (Pi.single i 1 : Fin M → E))

theorem mem_stdLat (E : Type) [Field E] (M : ℕ) (y : Fin M → E) :
    y ∈ stdLat E M ↔ ∀ i, IsIntegral ℤ (y i) := by
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨j, rfl⟩ := hz
      intro i
      by_cases h : i = j
      · subst h; simpa using isIntegral_one
      · simpa [Pi.single_eq_of_ne h] using isIntegral_zero
    | zero => intro i; exact isIntegral_zero
    | add a b _ _ ha hb => intro i; exact (ha i).add (hb i)
    | smul c a _ ha => intro i; exact (c.2 : IsIntegral ℤ (c : E)).mul (ha i)
  · intro hy
    rw [← Finset.univ_sum_single y]
    refine Submodule.sum_mem _ fun i _ => ?_
    have : (Pi.single i (y i) : Fin M → E) =
        (⟨y i, hy i⟩ : 𝓞 E) • (Pi.single i 1 : Fin M → E) := by
      funext j
      by_cases h : j = i
      · subst h
        rw [Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_same, Algebra.smul_def, mul_one]; rfl
      · rw [Pi.smul_apply, Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, smul_zero]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem isSelfDualLat_std {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) :
    IsSelfDualLat σ (1 : Matrix (Fin M) (Fin M) E) (stdLat E M) := by
  have hh : ∀ x y : Fin M → E, hE σ 1 x y = ∑ i, σ (x i) * y i := by
    intro x y
    simp [hE, Formalism.UG.hform, Matrix.one_apply]
  refine ⟨Submodule.fg_span (Set.finite_range _), ?_, fun y => ?_⟩
  · rw [eq_top_iff]
    intro y _
    rw [← Finset.univ_sum_single y]
    refine Submodule.sum_mem _ fun i _ => ?_
    have : (Pi.single i (y i) : Fin M → E) = y i • (Pi.single i 1 : Fin M → E) := by
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Submodule.subset_span ⟨i, rfl⟩))
  · constructor
    · intro hy x hx
      rw [hh]
      rw [mem_stdLat] at hx hy
      exact IsIntegral.sum _ fun i _ =>
        ((hx i).map (σ : E →+* E).toIntAlgHom).mul (hy i)
    · intro H
      rw [mem_stdLat]
      intro i
      have := H (Pi.single i 1) (Submodule.subset_span ⟨i, rfl⟩)
      rw [hh, Finset.sum_eq_single i] at this
      · simpa using this
      · intro j _ hj; simp [Pi.single_eq_of_ne hj]
      · simp

end GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.TrivialColumnStabiliser
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TrivialColumnStabiliser

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.MainNotions.StandardLattice
open scoped TensorProduct

def GAf (D : D7) :
    Subgroup (GL (Fin D.R.k) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :=
  letI := D.host.cmStar
  UPts D.sp.cm.sig D.sp.gram0 (FiniteAdeleRing (𝓞 D.host.F) D.host.F)

def GRat (D : D7) :
    Subgroup (GL (Fin D.R.k) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :=
  letI := D.host.cmStar
  ratPts D.sp.cm.sig D.sp.gram0 (FiniteAdeleRing (𝓞 D.host.F) D.host.F)

def colU (D : D7) (Lv : LevelData D) (u : D.what₂.Word) :
    Subgroup (GL (Fin D.R.k) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :=
  letI := D.host.cmStar
  ColLevel.U (Lv u)

def stabGroup (D : D7) (Lv : LevelData D) (u : D.what₂.Word)
    (y : GL (Fin D.R.k) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
    Subgroup (GL (Fin D.R.k) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :=
  GRat D ⊓ (colU D Lv u).map (MulAut.conj y).toMonoidHom

def ColumnStabilisersTrivial : Prop :=
  ∀ (D : D7) (Lv : LevelData D) (u : D.what₂.Word),
    GBig D → (∀ i : Fin 2, SplitsF D (D.host.g i)) →
      ∀ y ∈ GAf D, stabGroup D Lv u y = ⊥

theorem mem_stabGroup (D : D7) (Lv : LevelData D) (u : D.what₂.Word)
    (y γ : GL (Fin D.R.k) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
    γ ∈ stabGroup D Lv u y ↔ γ ∈ GRat D ∧ y⁻¹ * γ * y ∈ colU D Lv u := by
  unfold stabGroup
  rw [Subgroup.mem_inf, Subgroup.mem_map]
  refine and_congr_right fun _ => ⟨?_, fun h => ⟨_, h, ?_⟩⟩
  · rintro ⟨x, hx, rfl⟩
    simpa [mul_assoc] using hx
  · simp [mul_assoc]

end GlobalTheory.IndefiniteRowSideFullHecke.TrivialColumnStabiliser

end
end

