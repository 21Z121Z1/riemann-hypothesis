import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.PolarizationCorrespondence
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.CoefficientFieldBaseChange

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.DbarSolveComplexTorusStatement
section
open Complex Matrix
open scoped ContDiff BigOperators Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_periodic_dbar_solution : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ w : Fin g → (Fin g → ℂ) → ℂ, (∀ a, ContDiff ℝ ∞ (w a) ∧ ∀ (l : Λ) z, w a (z + l) = w a z) → (∀ a b z, (fderiv ℝ (w b) z (Pi.single a 1 : Fin g → ℂ) + I * fderiv ℝ (w b) z (I • (Pi.single a 1 : Fin g → ℂ))) = (fderiv ℝ (w a) z (Pi.single b 1 : Fin g → ℂ) + I * fderiv ℝ (w a) z (I • (Pi.single b 1 : Fin g → ℂ)))) → ∃ (t : Fin g → ℂ) (f : (Fin g → ℂ) → ℂ), ContDiff ℝ ∞ f ∧ (∀ (l : Λ) z, f (z + l) = f z) ∧ ∀ a z, (fderiv ℝ f z (Pi.single a 1 : Fin g → ℂ) + I * fderiv ℝ f z (I • (Pi.single a 1 : Fin g → ℂ))) = w a z - t a := by
  first | exact @GlobalTheory.dbar_solve_complexTorus | exact GlobalTheory.dbar_solve_complexTorus | (intros; apply GlobalTheory.dbar_solve_complexTorus <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsBaseChangeIffKeyPB
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.IndefiniteRowSideFullHecke.PolarizationCorrespondence

namespace GlobalTheory.KeyInputCompare

section Dual

variable {R R' : Type} [CommRing R] [CommRing R']

theorem epsScaleR_eq (c : R) : epsScaleR c = epsHom (RingHom.id R) c := by
  refine RingHom.ext fun x => ?_
  ext <;> simp [epsScaleR]

theorem epsScale_left (c : R) : (epsScale c).left = spMap (epsScaleR c) := by
  rw [epsScaleR_eq]; rfl

end Dual

section Lie

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G]

theorem isTangent_iff (v : epsR R ⟶ G) : IsTangent v ↔ v ∈ lieSub G := by
  change _ ↔ epsZero R ≫ v = η[G]
  constructor
  · intro h; ext1; exact h
  · intro h; exact congrArg CommaMorphism.left h

theorem linComb_val {n : ℕ} (c : Fin n → R) (v : Fin n → Tan G) :
    (linComb c v).1 = (List.ofFn fun i => epsScale (c i) ≫ (v i).1).prod := by
  rw [linComb, Subgroup.val_list_prod, List.map_ofFn]
  rfl

theorem isLieComb_iff_prod {n : ℕ} (c : Fin n → R) (v : Fin n → (epsR R ⟶ G)) (w : epsR R ⟶ G) :
    IsLieComb c v w ↔ w = (List.ofFn fun i => epsScale (c i) ≫ v i).prod := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    have : u = fun i => epsScale (c i) ≫ v i := by
      funext i; ext1; rw [hu, Over.comp_left, epsScale_left]
    rw [this]
  · rintro rfl
    exact ⟨_, fun i => by rw [Over.comp_left, epsScale_left], rfl⟩

theorem isLieComb_iff {n : ℕ} (c : Fin n → R) (v : Fin n → Tan G) (w : epsR R ⟶ G) :
    IsLieComb c (fun i => (v i).1) w ↔ w = (linComb c v).1 := by
  rw [isLieComb_iff_prod, linComb_val]

theorem isLieBasis_val_iff {n : ℕ} (v : Fin n → Tan G) :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsLieBasis (fun i => (v i).1) ↔ GlobalTheory.IndefiniteRowSideFullHecke.PolarizationCorrespondence.IsLieBasis v := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.PolarizationCorrespondence.IsLieBasis, Function.bijective_iff_existsUnique]
  constructor
  · rintro ⟨-, h⟩ w
    have := h w.1 ((isTangent_iff _).2 w.2)
    simp only [isLieComb_iff] at this
    simpa only [Subtype.ext_iff, eq_comm (b := w.1)] using this
  · intro h
    refine ⟨fun i => (isTangent_iff _).2 (v i).2, fun w hw => ?_⟩
    have := h ⟨w, (isTangent_iff _).1 hw⟩
    simp only [isLieComb_iff]
    simpa only [Subtype.ext_iff, eq_comm (b := w)] using this

end Lie

section Input

variable {R R' : Type} [CommRing R] [CommRing R']

def keyInEquiv (R : Type) [CommRing R] : KeyIn R ≃ KeyInput R where
  toFun x :=
    { P := x.P, dim_pos := x.g_pos, rig := x.rig, rig_gen := x.rig_gen, th := x.th, th_ne := x.th_ne
      b := fun i => ⟨x.v i, (isTangent_iff _).1 (x.basis.1 i)⟩
      b_basis := (isLieBasis_val_iff _).1 x.basis }
  invFun y :=
    { P := y.P, g_pos := y.dim_pos, rig := y.rig, rig_gen := y.rig_gen, th := y.th, th_ne := y.th_ne
      v := fun i => (y.b i).1
      basis := (isLieBasis_val_iff _).2 y.b_basis }
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem keyInEquiv_P (x : KeyIn R) : (keyInEquiv R x).P = x.P := rfl
@[simp] theorem keyInEquiv_rig (x : KeyIn R) : (keyInEquiv R x).rig = x.rig := rfl
@[simp] theorem keyInEquiv_th (x : KeyIn R) : (keyInEquiv R x).th = x.th := rfl
@[simp] theorem keyInEquiv_b (x : KeyIn R) (i : Fin x.P.g) : ((keyInEquiv R x).b i).1 = x.v i := rfl
@[simp] theorem keyInEquiv_symm_P (y : KeyInput R) : ((keyInEquiv R).symm y).P = y.P := rfl
@[simp] theorem keyInEquiv_symm_rig (y : KeyInput R) : ((keyInEquiv R).symm y).rig = y.rig := rfl
@[simp] theorem keyInEquiv_symm_th (y : KeyInput R) : ((keyInEquiv R).symm y).th = y.th := rfl
@[simp] theorem keyInEquiv_symm_v (y : KeyInput R) (i : Fin y.P.g) :
    ((keyInEquiv R).symm y).v i = (y.b i).1 := rfl

end Input

end GlobalTheory.KeyInputCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsCoeffFieldOfCoeff
section
noncomputable section

namespace GlobalTheory.ModuliCompare

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Geo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Tor.Host E}

theorem dim_eq (D : Tor.Datum H) : D.dim = IndefiniteRowSideFullHecke.CoefficientFieldBaseChange.dimD D := by
  have h2 : Module.finrank (maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have h := Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E
  rw [h2] at h
  unfold Tor.Datum.dim IndefiniteRowSideFullHecke.CoefficientFieldBaseChange.dimD
  rw [← h, Nat.mul_div_cancel _ two_pos]

variable {D : Tor.Datum H} {l : Tor.Level H}

theorem isModuli_of_moduli (Xo : Tor.Moduli D l) : IndefiniteRowSideFullHecke.CoefficientFieldBaseChange.IsModuli D l Xo.s Xo.univ where
  smooth := dim_eq D ▸ Xo.smooth
  qproj := Xo.qproj
  repr S hS s o := Xo.rep S s hS o
  rigid := Xo.unram

def moduliOfIsModuli {X : Scheme.{0}} {str : X ⟶ Tor.Sp (IndefiniteRowSideFullHecke.CoefficientFieldBaseChange.KA l)}
    {univ : Tor.Obj D l (IndefiniteRowSideFullHecke.CoefficientFieldBaseChange.baseKA l) str} (h : IndefiniteRowSideFullHecke.CoefficientFieldBaseChange.IsModuli D l str univ) : Tor.Moduli D l where
  X := X
  s := str
  qproj := h.qproj
  smooth := (dim_eq D).symm ▸ h.smooth
  univ := univ
  rep S s hS o := @IndefiniteRowSideFullHecke.CoefficientFieldBaseChange.IsModuli.repr _ _ _ _ _ _ _ _ _ _ h S hS s o
  unram := h.rigid

def moduliEquiv (D : Tor.Datum H) (l : Tor.Level H) :
    Tor.Moduli D l ≃
      {p : Σ (X : Scheme.{0}) (str : X ⟶ Tor.Sp (IndefiniteRowSideFullHecke.CoefficientFieldBaseChange.KA l)), Tor.Obj D l (IndefiniteRowSideFullHecke.CoefficientFieldBaseChange.baseKA l) str //
        IndefiniteRowSideFullHecke.CoefficientFieldBaseChange.IsModuli D l p.2.1 p.2.2} where
  toFun Xo := ⟨⟨Xo.X, Xo.s, Xo.univ⟩, isModuli_of_moduli Xo⟩
  invFun p := moduliOfIsModuli p.2
  left_inv _ := rfl
  right_inv _ := rfl

theorem isCoeffField_of_coeff (c : Tor.Coeff l) : IndefiniteRowSideFullHecke.CoefficientFieldBaseChange.IsCoeffField l c.F where
  fin := c.fin
  conj := c.conj
  root := c.zeta_mem

def coeffOfIsCoeffField {F₀ : IntermediateField ℚ ℂ} (h : IndefiniteRowSideFullHecke.CoefficientFieldBaseChange.IsCoeffField l F₀) : Tor.Coeff l where
  F := F₀
  fin := h.fin
  conj := h.conj
  zeta_mem := h.root
  le := h.KA_le

def coeffEquiv (l : Tor.Level H) : Tor.Coeff l ≃ {F₀ : IntermediateField ℚ ℂ // IndefiniteRowSideFullHecke.CoefficientFieldBaseChange.IsCoeffField l F₀} where
  toFun c := ⟨c.F, isCoeffField_of_coeff c⟩
  invFun F := coeffOfIsCoeffField F.2
  left_inv _ := rfl
  right_inv _ := rfl

end GlobalTheory.ModuliCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsUnitDetPairingOfBicharacterOfDvdTraceStatement
section
open scoped TensorProduct
theorem _root_.GlobalTheory.T.isUnit_det_pairing_of_bicharacter_of_dvd_trace : ∀ (O H K Γ : Type) [CommRing O] [IsDomain O] [CommRing H] [Algebra O H] [Field K] [IsAlgClosed K] [Algebra O K] [CommGroup Γ] (r : ℕ) (b : Module.Basis (Fin r) O H) (D : Matrix (Fin r) (Fin r) O) (pt : Γ → (H →ₐ[O] K)) (X : Γ → Γ → K) (c : O), Function.Injective (algebraMap O K) → IsReduced (K ⊗[O] H) → Function.Bijective pt → (∀ a a', X a a' = ∑ i, ∑ j, algebraMap O K (D i j) * pt a (b i) * pt a' (b j)) → (∀ a b, X a b ≠ 0) → (∀ a a' b, X (a * a') b = X a b * X a' b) → (∀ a b b', X a (b * b') = X a b * X a b') → (∀ a, (∀ b, X a b = 1) → a = 1) → c ≠ 0 → (r : O) = c ^ 2 → (∀ h : H, c ∣ Algebra.trace O H h) → IsUnit D.det := by
  first | exact @GlobalTheory.isUnit_det_of_bicharacter_of_dvd_trace | exact GlobalTheory.isUnit_det_of_bicharacter_of_dvd_trace | (intros; apply GlobalTheory.isUnit_det_of_bicharacter_of_dvd_trace <;> assumption)
end

