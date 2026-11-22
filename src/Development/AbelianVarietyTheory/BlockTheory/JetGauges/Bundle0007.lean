import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0003
import ReciprocityTheory.DualLattices.Bundle0005

-- bundled from Development.AbelianVarietyTheory.BlockTheory.JetGauges.DiagonalPowerBalanced
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.DiagonalPowerBalanced

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out

section Defs

variable {R : Type} [CommRing R] [IsDomain R]

def CLinear (D : DegPre R) (f : D.P.A ⟶ D.P.A) (a : D.X → D.X) : Prop :=
  ∀ y : D.X, D.c (a y) = D.c y ≫ f

def DiagOnB {D' D : DegPre R} {n : ℕ} (p : IsPowDeg D' D n) (F : D'.P.A ⟶ D'.P.A)
    (f : D.P.A ⟶ D.P.A) : Prop :=
  ∀ i : Fin n, F ≫ p.pw.pr i = p.pw.pr i ≫ f

def DiagOnX {D' D : DegPre R} {n : ℕ} (p : IsPowDeg D' D n) (A : D'.X → D'.X)
    (a : D.X → D.X) : Prop :=
  ∀ (x : D'.X) (i : Fin n), p.xe (A x) i = a (p.xe x i)

def diagB {D' D : DegPre R} {n : ℕ} (p : IsPowDeg D' D n) (f : D.P.A ⟶ D.P.A) :
    D'.P.A ⟶ D'.P.A :=
  p.pw.lim.lift (Fan.mk D'.P.A (fun i => p.pw.pr i ≫ f))

def diagX {D' D : DegPre R} {n : ℕ} (p : IsPowDeg D' D n) (a : D.X → D.X) : D'.X → D'.X :=
  fun x => p.xe.symm (fun i => a (p.xe x i))

theorem diagOnB_iff {D' D : DegPre R} {n : ℕ} (p : IsPowDeg D' D n) (F : D'.P.A ⟶ D'.P.A)
    (f : D.P.A ⟶ D.P.A) : DiagOnB p F f ↔ F = diagB p f := by
  have hfac : ∀ i, diagB p f ≫ p.pw.pr i = p.pw.pr i ≫ f := fun i =>
    p.pw.lim.fac (Fan.mk D'.P.A (fun i => p.pw.pr i ≫ f)) ⟨i⟩
  constructor
  · intro h
    apply p.pw.lim.hom_ext
    rintro ⟨i⟩
    exact (h i).trans (hfac i).symm
  · rintro rfl
    exact hfac

theorem diagOnX_iff {D' D : DegPre R} {n : ℕ} (p : IsPowDeg D' D n) (A : D'.X → D'.X)
    (a : D.X → D.X) : DiagOnX p A a ↔ A = diagX p a := by
  constructor
  · intro h
    funext x
    apply p.xe.injective
    funext i
    simp [diagX, h x i]
  · rintro rfl x i
    simp [diagX]

theorem CLinear.pow {D' D : DegPre R} {n : ℕ} (p : IsPowDeg D' D n) {F : D'.P.A ⟶ D'.P.A}
    {f : D.P.A ⟶ D.P.A} {A : D'.X → D'.X} {a : D.X → D.X} (hF : DiagOnB p F f)
    (hA : DiagOnX p A a) (h : CLinear D f a) : CLinear D' F A := by
  intro x
  apply p.pw.lim.hom_ext
  rintro ⟨i⟩
  change D'.c (A x) ≫ p.pw.pr i = (D'.c x ≫ F) ≫ p.pw.pr i
  rw [p.c_pr, hA x i, h, Category.assoc, hF i, ← Category.assoc, p.c_pr]

end Defs

def PowTauBalanced : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) (n : ℕ) (p : IsPowDeg D' D n)
    (f g : D.P.A ⟶ D.P.A) (a a' : D.X → D.X)
    (F G : D'.P.A ⟶ D'.P.A) (A A' : D'.X → D'.X),
    DiagOnB p F f → DiagOnB p G g → DiagOnX p A a → DiagOnX p A' a' →
    CLinear D f a → CLinear D g a' →
    D.TauBal f g a a' → D'.TauBal F G A A'

def PowTauBalancedAct : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D' : DegData R I) (n : ℕ)
    (p : IsPowDeg D'.toPre D.toPre n) (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X]
    (act : DegData.OAct O D) (a : O),
    D'.toPre.TauBal (diagB p (act.onB.act a)) (diagB p (act.onB.act (star a)))
      (diagX p (fun y => a • y)) (diagX p (fun y => star a • y))

theorem PowTauBalanced.act (h : PowTauBalanced) : PowTauBalancedAct := by
  intro R _ _ I D D' n p O _ _ _ act a
  exact h R D.toPre D'.toPre n p _ _ _ _ _ _ _ _
    ((diagOnB_iff p _ _).2 rfl) ((diagOnB_iff p _ _).2 rfl)
    ((diagOnX_iff p _ _).2 rfl) ((diagOnX_iff p _ _).2 rfl)
    (act.c_lin a) (act.c_lin (star a)) (act.tau_bal a)

example {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) : CLinear D (𝟙 _) id :=
  fun _ => (Category.comp_id _).symm

end GlobalTheory.IndefiniteRowSideFullHecke.DiagonalPowerBalanced
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.JetGauges.LieMatrixCoordinates
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LieMatrixCoordinates

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Out

attribute [local instance] Over.cartesianMonoidalCategory

section Chart

variable {T : Type} [CommRing T]

def jetOf {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (f : MvPowerSeries κ T) : JetR T κ m :=
  Ideal.Quotient.mk _
    (MvPowerSeries.trunc' T (Finsupp.equivFunOnFinite.symm fun _ : κ => m) f)

abbrev JetFam (G : Over (Sp T)) (d : ℕ) : Type := ∀ m : ℕ, algOver T (JetR T (Fin d) m) ⟶ G

def IsJetChart (G : Over (Sp T)) [GrpObj G] {d : ℕ} (x : JetFam G d) : Prop :=
  (∀ m, algOverHom (jetTruncR T (Fin d) m) ≫ x (m + 1) = x m) ∧
  (∀ m, algOverHom (jetZeroR T (Fin d) m) ≫ x m = toUnit _ ≫ η[G]) ∧
  ∀ (κ : Type) (m : ℕ) (y : algOver T (JetR T κ m) ⟶ G),
    algOverHom (jetZeroR T κ m) ≫ y = toUnit _ ≫ η[G] →
    ∃! ψ : JetR T (Fin d) m →ₐ[T] JetR T κ m,
      (∀ j, jetZeroR T κ m (ψ (zR m j)) = 0) ∧ y = algOverHom ψ ≫ x m

def HasCoords {G : Over (Sp T)} {d : ℕ} (x : JetFam G d) {κ : Type} [Fintype κ] [DecidableEq κ]
    (m : ℕ) (a : Fin d → MvPowerSeries κ T) (y : algOver T (JetR T κ m) ⟶ G) : Prop :=
  ∃ ψ : JetR T (Fin d) m →ₐ[T] JetR T κ m,
    (∀ j, ψ (zR m j) = jetOf m (a j)) ∧ y = algOverHom ψ ≫ x m

def IsLawOf (G : Over (Sp T)) [GrpObj G] {d : ℕ} (x : JetFam G d) (F : FGLaw T d) : Prop :=
  ∀ m : ℕ, ∃ y₀ y₁ : algOver T (JetR T (Fin 2 × Fin d) m) ⟶ G,
    HasCoords x m (pt T (n := 2) d 0) y₀ ∧ HasCoords x m (pt T (n := 2) d 1) y₁ ∧
      HasCoords x m F.F (lift y₀ y₁ ≫ μ[G])

def IsActOf (G : Over (Sp T)) [GrpObj G] [IsCommMonObj G] {d : ℕ} (x : JetFam G d)
    {Λ : Type} [CommRing Λ] (ιG : RingAct G Λ) {F : FGLaw T d} (α : Germ.OAct Λ F) : Prop :=
  ∀ (m : ℕ) (a : Λ), ∃ y : algOver T (JetR T (Fin 1 × Fin d) m) ⟶ G,
    HasCoords x m (pt T (n := 1) d 0) y ∧ HasCoords x m (α.act a) (y ≫ ιG.act a)

end Chart

section Characters

variable {O : Type} [CommRing O] {d : ℕ}

def IsMultSeries (F : Fin d → PS O 2 d) (χ : PS O 1 d) : Prop :=
  MvPowerSeries.constantCoeff χ = 1 ∧
    ev (n := 2) ![F] χ = ev (n := 2) ![pt O d 0] χ * ev (n := 2) ![pt O d 1] χ

def linCoeff (χ : PS O 1 d) : Fin d → O :=
  fun j => MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) χ

def dlogSpan (F : Fin d → PS O 2 d) {s : ℕ} (u : Fin s → Fin d → O) : Submodule O (Fin s → O) :=
  Submodule.span O {l | ∃ χ : PS O 1 d, IsMultSeries F χ ∧ l = fun i => linCoeff χ ⬝ᵥ u i}

example (F : Fin d → PS O 2 d) : IsMultSeries F 1 := ⟨by simp, by simp⟩

example :
    IsMultSeries (O := O) (d := 1)
      (fun i => MvPowerSeries.X (0, i) + MvPowerSeries.X (1, i) +
        MvPowerSeries.X (0, i) * MvPowerSeries.X (1, i))
      (1 + MvPowerSeries.X (0, 0)) ∧
    linCoeff (O := O) (d := 1) (1 + MvPowerSeries.X (0, 0)) 0 = 1 := by
  have key : ∀ a : Fin 1 → Pt O 2 1, (∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) →
      ev a (1 + MvPowerSeries.X (0, 0) : PS O 1 1) = 1 + a 0 0 := by
    intro a ha
    have hs : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin 1 => a q.1 q.2) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => ha q.1 q.2
    have h1 := ev_one a
    unfold ev at h1 ⊢
    rw [MvPowerSeries.subst_add hs, h1, MvPowerSeries.subst_X hs]
  refine ⟨⟨by simp, ?_⟩, ?_⟩
  · rw [key, key, key]
    · simp only [Matrix.cons_val_fin_one, pt]; ring
    all_goals (intro i j; fin_cases i; simp [pt])
  · simp [linCoeff, MvPowerSeries.coeff_one, MvPowerSeries.coeff_X]

end Characters

section Types

variable {T : Type} [CommRing T] {O : Type} [CommRing O] {C : Type} [Field C] [Algebra O C]
  {E : Type} [Field E] {d : ℕ}

def lieMat {F : FGLaw T d} (α : Germ.OAct (𝓞 E) F) (io : T →+* O) (a : 𝓞 E) :
    Matrix (Fin d) (Fin d) O :=
  Matrix.of fun i j => io (linCoeff (α.act a i) j)

def lieTau {F : FGLaw T d} (α : Germ.OAct (𝓞 E) F) (io : T →+* O) (τ : E →+* C) :
    Submodule O (Fin d → O) where
  carrier := {u | ∀ (a : 𝓞 E) (i : Fin d),
    algebraMap O C ((lieMat α io a).mulVec u i) = τ (a : E) * algebraMap O C (u i)}
  zero_mem' := by intro a i; simp
  add_mem' := by
    intro u u' hu hu' a i
    simp only [Matrix.mulVec_add, Pi.add_apply, map_add, hu a i, hu' a i, mul_add]
  smul_mem' := by
    intro c u hu a i
    simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, map_mul, hu a i]
    ring

def IsEigenBasis {F : FGLaw T d} (α : Germ.OAct (𝓞 E) F) (io : T →+* O) (τ : E →+* C) {s : ℕ}
    (u : Fin s → Fin d → O) : Prop :=
  LinearIndependent O u ∧ Submodule.span O (Set.range u) = lieTau α io τ

def HasColength_vp (p : ℕ) (v : Valuation C NNReal) (F : FGLaw T d) (io : T →+* O) {s : ℕ}
    (u : Fin s → Fin d → O) (a : ℝ) : Prop :=
  ReciprocityTheory.PGsh.Up.HasLen v O ((Fin s → O) ⧸ dlogSpan (F.mapF io) u) (v (p : C) ^ a)

def Induces (v : Valuation C NNReal) (τ : E →+* C) (w : Ideal (𝓞 E)) : Prop :=
  ∀ a : 𝓞 E, a ∈ w ↔ v (τ (a : E)) < 1

end Types

section Place

variable {E : Type} [Field E] [NumberField E]

def ramIdx (p : ℕ) (w : Ideal (𝓞 E)) : ℕ :=
  (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(p : 𝓞 E)})).count w

def localDeg (p : ℕ) (w : Ideal (𝓞 E)) : ℕ :=
  ramIdx p w * padicValNat p (Ideal.absNorm w)

def vd_vp (p : ℕ) (w : Ideal (𝓞 E)) : ℝ :=
  ((UniqueFactorizationMonoid.normalizedFactors (differentIdeal ℤ (𝓞 E))).count w : ℝ) /
    (ramIdx p w : ℝ)

end Place

open Classical in

def AvChartSt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime]
    (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [IsNoetherianRing T] [CharZero T]
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T], ¬ IsUnit (p : T) →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)],
    (∀ a : 𝓞 E, ((star a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) →
  ∀ (I : Ideal T), I ≠ ⊤ →
  ∀ (D : DegData T I) [Module (𝓞 E) D.toPre.X]
    (A : PolAV (Spec (CommRingCat.of (FractionRing T))))
    (G : Over (Sp T)) [GrpObj G] [IsCommMonObj G]
    (U : UnifPre I D A G)
    (ιD : D.OAct (𝓞 E)) (ιA : A.OAct (𝓞 E)) (ιG : RingAct G (𝓞 E)),
    U.OLinear (𝓞 E) ιD ιA ιG →
  ∀ (d : ℕ) (x : JetFam G d) (F : FGLaw T d) (α : Germ.OAct (𝓞 E) F),
    IsJetChart G x → IsLawOf G x F → IsActOf G x ιG α →
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal)
    (O : Type) [CommRing O] [Algebra O C] [IsAdicComplete (Ideal.span {(p : O)}) O],
    v.Integers O →
  ∀ (io : T →+* O), IsLocalHom io →
  ∀ (w : Ideal (𝓞 E)), w.IsPrime → (p : 𝓞 E) ∈ w → w ≠ w.comap (starRingEnd (𝓞 E)) →
  ∀ (rp rm : ℕ) (u : (E →+* C) → Fin rp → Fin d → O) (u' : (E →+* C) → Fin rm → Fin d → O),
    (∀ τ, Induces v τ w → IsEigenBasis α io τ (u τ)) →
    (∀ σ, Induces v σ (w.comap (starRingEnd (𝓞 E))) → IsEigenBasis α io σ (u' σ)) →
    (∀ τ, Induces v τ w → ∃ a : ℝ, HasColength_vp p v F io (u τ) a) ∧
    ∀ a : (E →+* C) → ℝ, (∀ τ, Induces v τ w → HasColength_vp p v F io (u τ) (a τ)) →
      ∑ τ ∈ Finset.univ.filter (fun τ : E →+* C => Induces v τ w), a τ ≤
        (localDeg p w : ℝ) * ((rm : ℝ) - (Module.finrank (𝓞 E) D.toPre.X : ℝ)) *
          (1 / ((p : ℝ) - 1) + vd_vp p w / 2)

end GlobalTheory.IndefiniteRowSideFullHecke.LieMatrixCoordinates
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.JetGauges.OriginChartMultiplication
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open scoped TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.OriginChartMultiplication

def jetOfSeries {R : Type} [CommRing R] {κ : Type} [Finite κ] (m : ℕ) (f : MvPowerSeries κ R) :
    JetR R κ m :=
  Ideal.Quotient.mk _ (MvPowerSeries.truncTotal (m + 1) f)

def IsOriginChart {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] {d : ℕ}
    (x : ∀ m : ℕ, algOver R (JetR R (Fin d) m) ⟶ G) (F : FGLaw R d) : Prop :=
  (∀ m, algOverHom (jetTruncR R (Fin d) m) ≫ x (m + 1) = x m) ∧
  (∀ m, algOverHom (jetZeroR R (Fin d) m) ≫ x m = toUnit _ ≫ η[G]) ∧
  (∀ (κ : Type) (m : ℕ) (y : algOver R (JetR R κ m) ⟶ G),
    algOverHom (jetZeroR R κ m) ≫ y = toUnit _ ≫ η[G] →
    ∃! ψ : JetR R (Fin d) m →ₐ[R] JetR R κ m,
      (∀ j, jetZeroR R κ m (ψ (zR m j)) = 0) ∧ y = algOverHom ψ ≫ x m) ∧
  (∀ m, ∃ ψ₀ ψ₁ ψ : JetR R (Fin d) m →ₐ[R] JetR R (Fin 2 × Fin d) m,
    (∀ j, ψ₀ (zR m j) = zR m ((0 : Fin 2), j)) ∧ (∀ j, ψ₁ (zR m j) = zR m ((1 : Fin 2), j)) ∧
    (∀ j, ψ (zR m j) = jetOfSeries m (F.F j)) ∧
    lift (algOverHom ψ₀ ≫ x m) (algOverHom ψ₁ ≫ x m) ≫ μ[G] = algOverHom ψ ≫ x m)

def mulSeries {R : Type} [CommRing R] {d : ℕ} (F : FGLaw R d) (n : ℕ) : Pt R 1 d :=
  Nat.rec (motive := fun _ => Pt R 1 d) 0 (fun _ a => F.add a (pt R d 0)) n

theorem mulSeries_zero {R : Type} [CommRing R] {d : ℕ} (F : FGLaw R d) : mulSeries F 0 = 0 := rfl

theorem mulSeries_succ {R : Type} [CommRing R] {d : ℕ} (F : FGLaw R d) (n : ℕ) :
    mulSeries F (n + 1) = F.add (mulSeries F n) (pt R d 0) := rfl

theorem mulSeries_one {R : Type} [CommRing R] {d : ℕ} (F : FGLaw R d) :
    mulSeries F 1 = pt R d 0 := by
  funext i
  exact F.unit i

theorem constantCoeff_mulSeries {R : Type} [CommRing R] {d : ℕ} (F : FGLaw R d) (n : ℕ)
    (i : Fin d) : MvPowerSeries.constantCoeff (mulSeries F n i) = 0 := by
  induction n generalizing i with
  | zero => simp [mulSeries_zero]
  | succ n ih =>
    have h : ∀ q : Fin 2 × Fin d, MvPowerSeries.constantCoeff
        ((![mulSeries F n, pt R d 0] : Fin 2 → Pt R 1 d) q.1 q.2) = 0 := by
      rintro ⟨a, j⟩
      fin_cases a
      · exact ih j
      · simp [pt]
    exact MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero h) h (F.const i)

def torsionIdeal {T O : Type} [CommRing T] [CommRing O] (f : T →+* O) {d : ℕ} (F : FGLaw T d)
    (n : ℕ) : Ideal (PS O 1 d) :=
  Ideal.span (Set.range fun i : Fin d => MvPowerSeries.map f (mulSeries F n i))

abbrev TorsionRing {T O : Type} [CommRing T] [CommRing O] (f : T →+* O) {d : ℕ} (F : FGLaw T d)
    (n : ℕ) : Type :=
  PS O 1 d ⧸ torsionIdeal f F n

def FiniteFreeReducedSeparated (O C Q : Type) [CommRing O] [Field C] [Algebra O C]
    [CommRing Q] [Algebra O Q] : Prop :=
  Module.Finite O Q ∧ Module.Free O Q ∧ IsReduced (C ⊗[O] Q) ∧
    ∀ a b : Q, (∀ φ : Q →ₐ[O] O, φ a = φ b) → a = b

def TorsionFiniteFreeAlongIdeal : Prop :=
  ∀ (p : ℕ), p.Prime →
  ∀ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [IsNoetherianRing T] [CharZero T]
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T], ¬ IsUnit (p : T) →
  ∀ (I : Ideal T), I ≠ ⊤ →
  ∀ (D : DegData T I) (A : PolAV (Spec (CommRingCat.of (FractionRing T))))
    (G : Over (Spec (CommRingCat.of T))) [GrpObj G] [IsCommMonObj G], Nonempty (UnifPre I D A G) →
  ∀ (d : ℕ) (x : ∀ m : ℕ, algOver T (JetR T (Fin d) m) ⟶ G) (F : FGLaw T d),
    IsOriginChart G x F →
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal)
    (O : Type) [CommRing O] [Algebra O C], v.Integers O →
    IsAdicComplete (Ideal.span {(p : O)}) O →
  ∀ (f : T →+* O), IsLocalHom f →
  ∀ m : ℕ, FiniteFreeReducedSeparated O C (TorsionRing f F (p ^ m))

def TorsionFiniteFree : Prop :=
  ∀ (p : ℕ), p.Prime →
  ∀ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [IsNoetherianRing T] [CharZero T]
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T], ¬ IsUnit (p : T) →
  ∀ (D : DegData T (IsLocalRing.maximalIdeal T))
    (A : PolAV (Spec (CommRingCat.of (FractionRing T))))
    (G : Over (Spec (CommRingCat.of T))) [GrpObj G] [IsCommMonObj G],
    Nonempty (UnifPre (IsLocalRing.maximalIdeal T) D A G) →
  ∀ (d : ℕ) (x : ∀ m : ℕ, algOver T (JetR T (Fin d) m) ⟶ G) (F : FGLaw T d),
    IsOriginChart G x F →
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal)
    (O : Type) [CommRing O] [Algebra O C], v.Integers O →
    IsAdicComplete (Ideal.span {(p : O)}) O →
  ∀ (f : T →+* O), IsLocalHom f →
  ∀ m : ℕ, FiniteFreeReducedSeparated O C (TorsionRing f F (p ^ m))

example {T O : Type} [CommRing T] [CommRing O] (f : T →+* O) {d : ℕ} (F : FGLaw T d) :
    torsionIdeal f F 1 = Ideal.span (Set.range (pt O d (0 : Fin 1))) := by
  unfold torsionIdeal
  rw [mulSeries_one]
  unfold pt
  simp

end GlobalTheory.IndefiniteRowSideFullHecke.OriginChartMultiplication
end
end

