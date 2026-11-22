import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilGramSignature
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1015
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1001
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020

-- bundled from Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ConjScalarThm
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjScalar

variable {D : D7}

def RelLab (V : HSp D) (P : Pl D.host.E) (d : List ℤ) : Prop :=
  (Formalism.DivisionValues.conjPl P ≠ P ∧ ∃ k, k ≤ V.rank ∧ d = splitLab V.rank k) ∨ (Formalism.DivisionValues.conjPl P = P ∧ GlobalTheory.Hk3.IsLab V P d)

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Eig

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

def EigF {W : Type} [AddCommGroup W] [Module ℂ W] (a : Pl D.host.E → List ℤ → ℂ) (Φ : Bridge.Gf (Vc D i) → W) : Prop :=
  ∀ P d, GlobalTheory.Hk3.Good R A.μ0 P → RelLab (Vc D i) P d → GlobalTheory.Hk3.hkF (Vc D i) P (Finsupp.single d 1) Φ = a P d • Φ

def EigK (a : Pl D.host.E → List ℤ → D.what₂.LL) (x : A.fam.amb.FL i A.μ0) : Prop :=
  EigF R i (fun P d => D.what₂.embLL (a P d)) ((R.HV i A.μ0).e (R.jV i A.μ0 x))

end Eig

def ConjScalarThm : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    R.Char F → IsStdChar D R.ψ (-1) → (∀ χ ∈ A.X, IsAbsIrrChar χ) →
    ∀ gramR c0R c0L, Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ)
        (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L →
    ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ →
    ∀ μ' η' c c₁ H j th, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsConjDatum R i σ (c0L i) μ' η' c c₁ H j th →
    ∀ ev : Pl D.host.E → List ℤ → ℂ, ∃ l : ℝ, ∀ u : H.H, th u ∈ GlobalTheory.LiftLower.partH R i σ ev →
      th (LinearMap.adjoint th (th u)) = (l : ℂ) • th u

def ConjRatLift : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
    (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : ℂ),
    R.Char F → IsStdChar D R.ψ (-1) → ∀ fw : FWTie T R κ v₀, BarTie fw → IoExt R → R.LUnif → (∀ i, OMPins T R κ v₀ O i) →
    ∀ i : Fin D.R.m, (O i).OneMapOf (κ i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) (O i).s0) ph →
    (∀ x, ∃! y, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsRatLift R i ph x y) ∧
    (∀ gramR c0R c0L,
      Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ)
        (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L →
      ∀ σ, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.ConjAt R i σ ph (c0L i)) ∧
    ∀ σ, ¬ GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK ((starRingEnd ℂ).comp σ) ∧
      ∀ y y', ⟪(R.FW i).j σ y, (R.FW i).j σ y'⟫_ℂ =
        starRingEnd ℂ ⟪(R.FW i).j ((starRingEnd ℂ).comp σ) y, (R.FW i).j ((starRingEnd ℂ).comp σ) y'⟫_ℂ

end GlobalTheory.ConjScalar

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MixedModelTargetHeisenbergAnisotropicPart
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MixModel.Check

open GlobalTheory.OrientedHeis HypDec

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem symplOH_add_self (S T : HSp D) (x y : WO S T) : symplOH S T x y + symplOH S T x y = symplO S T x y := by
  rw [symplOH, ← add_mul, ← map_add, add_halves, map_one, one_mul]

theorem smul_cancel {R : Type} [CommRing R] {n k l : ℕ} {a c : R} (h : a * c = 1) (P G : Matrix (Fin n) (Fin n) R)
    (hP : P * G = 1) (y : Matrix (Fin n) (Fin k) R) (b : Matrix (Fin k) (Fin l) R) :
    a • (P * (c • (G * y) * b)) = y * b := by
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, h, one_smul, Matrix.mul_assoc G, ← Matrix.mul_assoc, hP,
    Matrix.one_mul]

section Source

variable {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ))

theorem mixS_eq (f : WO S T → ℂ) (x : Mx D T.rank ρ) (w₀ : WO S₀ T) : d.mixS T ψ μ 𝓕 f x w₀ =
    ∫ a in 𝓕, ψ (symplOH S T (d.extY T a) (d.extX T x)) * f (d.extY T a + d.extX T x + d.ext0 T w₀) ∂μ := by
  simp only [mixS, integrandS_eq]

theorem mixS_heis_extX (f : WO S T → ℂ) (u x : Mx D T.rank ρ) :
    d.mixS T ψ μ 𝓕 (heisO ψ S T (d.extX T u) f) x = d.mixS T ψ μ 𝓕 f (x + u) := by
  funext w₀
  have h : symplOH S T (d.ext0 T w₀) (d.extX T u) = 0 := by rw [symplOH_skew, wittDecomp_sympl_extIsotropic_extAnisotropic, neg_zero]
  simp only [mixS_eq, heisO, map_add (d.extX T), symplOH_add_left, symplOH_add_right, symplOH_extX_extX, h, add_zero,
    AddChar.map_add_eq_mul, mul_assoc]
  congr 1; funext a; congr 3; abel

theorem mixedModelSource_heisenberg_anisotropic_part (f : WO S T → ℂ) (u : WO S₀ T) (x : Mx D T.rank ρ) :
    d.mixS T ψ μ 𝓕 (heisO ψ S T (d.ext0 T u) f) x = heisO ψ S₀ T u (d.mixS T ψ μ 𝓕 f x) := by
  funext w₀
  simp only [mixS_eq, heisO, map_add (d.ext0 T), symplOH_add_left, wittDecomp_sympl_extIsotropic_extAnisotropic, wittDecomp_sympl_extDual_extAnisotropic,
    wittDecomp_sympl_extAnisotropic_extAnisotropic, zero_add, ← integral_const_mul, add_assoc]
  congr 1; funext a; ring

variable {μ 𝓕}

theorem mixS_heis_extY (hμ : IsCovolOne (ratMx D T.rank ρ) μ 𝓕) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (y x : Mx D T.rank ρ) (w₀ : WO S₀ T) :
    d.mixS T ψ μ 𝓕 (heisO ψ S T (d.extY T y) f) x w₀ =
      ψ (symplO S T (d.extX T x) (d.extY T y)) * d.mixS T ψ μ 𝓕 f x w₀ := by
  have h : symplOH S T (d.ext0 T w₀) (d.extY T y) = 0 := by rw [symplOH_skew, wittDecomp_sympl_extDual_extAnisotropic, neg_zero]
  have h2 := covolOne_integral_add hμ
    (fun a => heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w₀) f)) 0)
    (d.integrandS_periodic hf x w₀) y
  rw [mixS, mixS, ← h2, ← integral_const_mul]
  congr 1; funext a
  simp only [integrandS_eq]
  simp only [heisO, map_add (d.extY T), symplOH_add_left, symplOH_extY_extY, h, add_zero, zero_add, ← mul_assoc,
    ← AddChar.map_add_eq_mul, ← symplOH_add_self, symplOH_skew S T (d.extX T x) (d.extY T y)]
  congr 2
  · abel
  · abel

theorem mixS_quasi (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (x : Mx D T.rank ρ) (γ : Matrix (Fin T.rank) (Fin S₀.rank) D.host.E) (w₀ : WO S₀ T) :
    d.mixS T ψ μ 𝓕 f x (ratW T S₀ γ + w₀) = ψ (-(symplOH S₀ T (ratW T S₀ γ) w₀)) * d.mixS T ψ μ 𝓕 f x w₀ := by
  obtain ⟨δ, hδ⟩ : d.ext0 T (ratW T S₀ γ) ∈ ratMx D _ _ := ratMx_mul (rat_mem γ) (rat_mem _)
  simp only [mixS_eq, ← integral_const_mul]
  congr 1; funext a
  have h := hf.quasi δ (d.extY T a + d.extX T x + d.ext0 T w₀)
  rw [show ratW T S δ = d.ext0 T (ratW T S₀ γ) from hδ] at h
  have h1 : symplOH S T (d.ext0 T (ratW T S₀ γ)) (d.extY T a) = 0 := by rw [symplOH_skew, wittDecomp_sympl_extDual_extAnisotropic, neg_zero]
  have h2 : symplOH S T (d.ext0 T (ratW T S₀ γ)) (d.extX T x) = 0 := by rw [symplOH_skew, wittDecomp_sympl_extIsotropic_extAnisotropic, neg_zero]
  rw [symplOH_add_right, symplOH_add_right, h1, h2, wittDecomp_sympl_extAnisotropic_extAnisotropic, zero_add, zero_add] at h
  rw [map_add (d.ext0 T), show d.extY T a + d.extX T x + (d.ext0 T (ratW T S₀ γ) + d.ext0 T w₀) =
    d.ext0 T (ratW T S₀ γ) + (d.extY T a + d.extX T x + d.ext0 T w₀) by abel, h]
  ring

theorem mixS_rank_zero (d : HypDec S S₀ 0) {μ : Measure (Mx D T.rank 0)} {𝓕 : Set (Mx D T.rank 0)}
    (hμ : IsCovolOne (ratMx D T.rank 0) μ 𝓕) (f : WO S T → ℂ) (x : Mx D T.rank 0) (w₀ : WO S₀ T) :
    d.mixS T ψ μ 𝓕 f x w₀ = f (d.ext0 T w₀) := by
  have : ∀ a : Mx D T.rank 0, a = 0 := fun a => Subsingleton.elim a 0
  have e : ∀ a : Mx D T.rank 0, ψ (symplOH S T (d.extY T a) (d.extX T x)) * f (d.extY T a + d.extX T x + d.ext0 T w₀) =
      f (d.ext0 T w₀) := fun a => by
    rw [this a, this x, map_zero, map_zero, symplOH_zero_left, AddChar.map_zero_eq_one, one_mul, zero_add, zero_add]
  simp only [mixS_eq, e]
  rw [setIntegral_const, Measure.real, hμ.2.2, ENNReal.toReal_one, one_smul]

end Source

section Target

variable {S T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (μ : Measure (Mx D ρ S.rank)) (𝓕 : Set (Mx D ρ S.rank))

theorem mixT_eq (f : WO S T → ℂ) (y : Mx D S.rank ρ) (w₀ : WO S T₀) : d.mixT S ψ μ 𝓕 f y w₀ =
    ∫ a in 𝓕, ψ (symplOH S T (d.incX S a) (d.incAdj S y)) * f (d.incX S a + d.incAdj S y + d.inc0 S w₀) ∂μ := by
  simp only [mixT, integrandT_eq]

theorem mixT_heis_incAdj (f : WO S T → ℂ) (u y : Mx D S.rank ρ) :
    d.mixT S ψ μ 𝓕 (heisO ψ S T (d.incAdj S u) f) y = d.mixT S ψ μ 𝓕 f (y + u) := by
  funext w₀
  have h : symplOH S T (d.inc0 S w₀) (d.incAdj S u) = 0 := by
    rw [symplOH_skew, incAdj_apply, wittDecomp_sympl_inclDual_inclAnisotropic, neg_zero]
  have h' : symplOH S T (d.incAdj S y) (d.incAdj S u) = 0 := d.symplOH_incY_incY S _ _
  simp only [mixT_eq, heisO, map_add (d.incAdj S), symplOH_add_left, symplOH_add_right, h, h', add_zero,
    AddChar.map_add_eq_mul, mul_assoc]
  congr 1; funext a; congr 3; abel

theorem mixedModelTarget_heisenberg_anisotropic_part (f : WO S T → ℂ) (u : WO S T₀) (y : Mx D S.rank ρ) :
    d.mixT S ψ μ 𝓕 (heisO ψ S T (d.inc0 S u) f) y = heisO ψ S T₀ u (d.mixT S ψ μ 𝓕 f y) := by
  funext w₀
  have h' : symplOH S T (d.incAdj S y) (d.inc0 S u) = 0 := d.wittDecomp_sympl_inclDual_inclAnisotropic S _ _
  simp only [mixT_eq, heisO, map_add (d.inc0 S), symplOH_add_left, wittDecomp_sympl_inclIsotropic_inclAnisotropic, h',
    wittDecomp_sympl_inclAnisotropic_inclAnisotropic, zero_add, ← integral_const_mul, add_assoc]
  congr 1; funext a; ring

variable {μ 𝓕}

theorem mixT_heis_incX (hμ : IsCovolOne (ratMx D ρ S.rank) μ 𝓕) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (ξ : Mx D ρ S.rank) (y : Mx D S.rank ρ) (w₀ : WO S T₀) :
    d.mixT S ψ μ 𝓕 (heisO ψ S T (d.incX S ξ) f) y w₀ =
      ψ (symplO S T (d.incAdj S y) (d.incX S ξ)) * d.mixT S ψ μ 𝓕 f y w₀ := by
  have h : symplOH S T (d.inc0 S w₀) (d.incX S ξ) = 0 := by rw [symplOH_skew, wittDecomp_sympl_inclIsotropic_inclAnisotropic, neg_zero]
  have h2 := covolOne_integral_add hμ
    (fun ξ => heisO ψ S T (d.incX S ξ) (heisO ψ S T (d.incAdj S y) (heisO ψ S T (d.inc0 S w₀) f)) 0)
    (d.integrandT_periodic hf y w₀) ξ
  rw [mixT, mixT, ← h2, ← integral_const_mul]
  congr 1; funext a
  simp only [integrandT_eq]
  simp only [heisO, map_add (d.incX S), symplOH_add_left, symplOH_incX_incX, h, add_zero, zero_add, ← mul_assoc,
    ← AddChar.map_add_eq_mul, ← symplOH_add_self, symplOH_skew S T (d.incAdj S y) (d.incX S ξ)]
  congr 2
  · abel
  · abel

theorem adjoint_nB_incAdj (b : Mx D ρ T₀.rank) (y : Mx D S.rank ρ) :
    incA D D.host.xi0 • (giA S ⬝ (adj (d.p0 ⬝ (mt T (d.nB b)⁻¹ ⬝ d.incAdj S y)) ⬝ gA T₀)) = y ⬝ b := by
  have h1 : d.p0 ⬝ (mt T (d.nB b)⁻¹ ⬝ d.incAdj S y) =
      plus T₀ b ⬝ (incA D (-D.host.xi0⁻¹) • (adj y ⬝ gA S)) := by
    rw [nB_inv, cancel₂ (d.wittDecomp_projAnisotropic_unipotentMixed _), incAdj_apply, incY_apply]
    generalize incA D (-D.host.xi0⁻¹) • (adj y ⬝ gA S) = z
    simp only [plus_neg, Matrix.sub_mul, Matrix.neg_mul, Matrix.mul_assoc, cancel₂ d.p0_jY, cancel₂ d.pY_jY,
      Matrix.zero_mul, Matrix.one_mul, zero_sub, neg_neg]
  have h2 : adj (incA D (-D.host.xi0⁻¹) • (adj y ⬝ gA S)) = cA D (incA D (-D.host.xi0⁻¹)) • (gA S ⬝ y) := by
    rw [adj_smul, adj_mul, adj_adj, adj_gA]
  rw [h1, adj_mul, h2, Matrix.mul_assoc _ (adj (plus T₀ b)), adj_plus_gA]
  exact smul_cancel (R := AE D) (wittDecomp_trace0Unit_mul_conj_neg_inv (D := D)) (giA S) (gA S) (giA_mul_gA S) y b

end Target

theorem nC_injective {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) : Function.Injective d.nC := fun c c' h => by
  have h1 : d.pX ⬝ (mt S (d.nC c) ⬝ d.jY) = d.pX ⬝ (mt S (d.nC c') ⬝ d.jY) := by rw [h]
  refine Subtype.ext ?_
  simpa only [nC_jY, Matrix.mul_add, pX_jY, zero_add, cancel₂ d.pX_jX, Matrix.one_mul] using h1

theorem levi_injective {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) : Function.Injective d.levi := fun c c' h => by
  have h1 : d.pX ⬝ (mt S (d.levi c) ⬝ d.jX) = d.pX ⬝ (mt S (d.levi c') ⬝ d.jX) := by rw [h]
  refine Units.ext ?_
  simpa only [levi_jX, cancel₂ d.pX_jX, Matrix.one_mul] using h1

def xiSkew (D : D7) (ρ : ℕ) : skewA D ρ :=
  ⟨incA D D.host.xi0 • (1 : Mx D ρ ρ), by
    rw [mem_skewA, adj_smul, adj_one, GlobalTheory.DualPairCheck.cA_incA, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, map_neg, neg_smul]⟩

theorem nC_xi_ne_one (D : D7) : (hypDecThree D).nC (xiSkew D 1) ≠ 1 := fun h => by
  have h1 := congrArg Subtype.val (nC_injective (hypDecThree D) (h.trans (hypDecThree D).nC_zero.symm))
  have h2 : incA D D.host.xi0 * 1 = 0 := congrFun (congrFun h1 0) 0
  rw [mul_one, ← map_zero (incA D)] at h2
  exact GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D (incA_injective h2)

end GlobalTheory.MixModel.Check

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar

namespace GlobalTheory.LiftRows

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev Eig (D : D7) : Type := HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

structure Given (F : Face D A) : Prop where
  core : GlobalTheory.Hk3.Core R F
  params : ∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)
  irr : ∀ χ ∈ A.X, IsAbsIrrChar χ
  types : GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators.GoodTypes R
  guard : FWT.QGuard R
  gapR : ∀ (τ : D.what₂.Tau) (n : ℕ), n + 1 < D.R.r →
    100 * (D.R.r : ℚ) ^ 4 ≤ Formalism.L2.NTheta.lamAt (D.hc τ) n - Formalism.L2.NTheta.lamAt (D.hc τ) (n + 1)

def IsLval (i : Fin D.R.m) (t : T) (c : Eig D) (z : ℝ) : Prop :=
  ∃ B, GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) D.R.r c B ∧ GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.IsLValue R t B ((i : ℕ) + 1) z

variable (SF : Finset (HeightOneSpectrum (𝓞 D.host.F)))

def AForm : Prop :=
  ∃ a : Fin D.R.m → ℝ, (∀ i, 0 < a i) ∧ ∀ i t c, GlobalTheory.Hk3.Wcc R SF i c ≠ ⊥ → ∃ z : ℝ, IsLval R i t c z ∧
    ∀ x ∈ GlobalTheory.Hk3.Wcc R SF i c, R.thG i t (LinearMap.adjoint (R.thG i t) x) = ((a i * z : ℝ) : ℂ) • x

def BForm : Prop :=
  ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ t c (z : Fin D.R.m → ℝ), (∀ i, IsLval R i t c (z i)) →
    ∀ x ∈ GlobalTheory.Hk3.EEc R SF c, R.Th t (LinearMap.adjoint (R.Th t) x) = ((κ₀ * ∏ i, z i : ℝ) : ℂ) • x

def Scal : Prop :=
  ∃ (lam : Fin D.R.m → T → Eig D → ℝ) (κ : ℝ), 0 < κ ∧ (∀ i t c, 0 < lam i t c) ∧
    (∀ i t c, ∀ x ∈ GlobalTheory.Hk3.Wcc R SF i c, R.thG i t (LinearMap.adjoint (R.thG i t) x) = ((lam i t c : ℝ) : ℂ) • x) ∧
    ∀ t c, ∀ x ∈ GlobalTheory.Hk3.EEc R SF c, R.Th t (LinearMap.adjoint (R.Th t) x) = ((κ * ∏ i, lam i t c : ℝ) : ℂ) • x

def Kept : Prop :=
  ∀ t c, ∀ x ∈ GlobalTheory.Hk3.EEc R (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) c,
    R.Th t (LinearMap.adjoint (R.Th t) x) ∈ GlobalTheory.Hk3.EEc R (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) c

def MatchUp : Prop := ∀ c, GlobalTheory.Hk3.EEc R SF c ≠ ⊥ → ∀ i, GlobalTheory.Hk3.Wcc R SF i c ≠ ⊥

def RowsNe (F : Face D A) : Prop := ∀ b, R.EEat (R.levR F b) ≠ ⊥

def UpInj : Prop := ∀ t, Function.Injective (LinearMap.adjoint (R.Th t))

def UpInjW : Prop :=
  ∀ i t x, GlobalTheory.Hk3.eH R i x = x → LinearMap.adjoint (R.thG i t) x = 0 → x = 0

def GoodV (i : Fin D.R.m) (y : (R.HV i A.μ0).H) : Prop :=
  ∀ ℓ : (R.cV i).W →ₗ[ℂ] ℂ,
    gaL (Vc D i) (R.βV i) (R.datVt i A.μ0) R.eG (RealDat.eC (A := A) (sg0 D A)) (fun h => ℓ (R.extV i A.μ0 y h)) =
      fun h => ℓ (R.extV i A.μ0 y h)

def LiftInj : Prop :=
  ∀ i h, GlobalTheory.Hk3.IsOpsV R i A.μ0 h → ∀ s : Eig D, ∀ x y : (R.HV i A.μ0).H,
    (∀ P d, GlobalTheory.Hk3.Good R A.μ0 P → GlobalTheory.Hk3.IsLab (Vc D i) P d → h P (Finsupp.single d 1) x = s P d • x) →
    (∀ P d, GlobalTheory.Hk3.Good R A.μ0 P → GlobalTheory.Hk3.IsLab (Vc D i) P d → h P (Finsupp.single d 1) y = s P d • y) →
    R.thG i A.μ0 x ≠ 0 → GoodV R i y → R.thG i A.μ0 y = 0 → y = 0

def IsLiftDataC (F : Face D A) (i : Fin D.R.m) (t : T) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ) (P : LevelP R.Pg D.R.r ℂ)
    (cμ cη : (AE D)ˣ →* Circle) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (Datum.WO (Vc D i) (Wc D i) → ℂ))
    (BW : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (f₀ f : Datum.WO (Vc D i) (Wc D i) → ℂ)
    (c : CoefA (Vc D i)) (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) : Prop :=
  GlobalTheory.Hk3.Core R F ∧ PrimeToHost R t ∧ IsEmbOverK D σ s ∧ IsLocalLevel P ∧ IsConjChars R i t s cμ cη m ∧
    Datum.IsWeilDatumO R.ψ (Vc D i) (Wc D i) cμ (cμ * cη⁻¹) ω ∧
    (∀ ρ, Datum.IsONBasis (gramAt D (Wc D i) ρ) (cart (R.MW i σ) ρ) (BW ρ) (pW D i ρ)) ∧
    IsLevelVec R.ψ R.θ (Vc D i) (Wc D i) (cart (R.MW i σ)) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i) (R.datWp i P) (R.Q t) m f₀ f ∧
    Lift.PtTheta R.ψ (Vc D i) (Wc D i) (ptAt R i σ BW f) ∧ c.Is ∧
    IsIoW R.θ (R.MW i σ) c ω (ptAt R i σ BW f) (deltaAtEmb D i σ) io

def ForLiftDataC (F : Face D A)
    (Φ : ∀ (i : Fin D.R.m) (_t : T) (σ : D.what₂.LL →+* ℂ) (_P : LevelP R.Pg D.R.r ℂ) (_m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
      (_ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (Datum.WO (Vc D i) (Wc D i) → ℂ))
      (_BW : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (_f : Datum.WO (Vc D i) (Wc D i) → ℂ)
      (c : CoefA (Vc D i)) (_io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank), Prop) : Prop :=
  ∀ i t σ s P cμ cη m ω BW f₀ f c io, IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → Φ i t σ P m ω BW f c io

def SourceLevelLawC (F : Face D A) : Prop :=
  ForLiftDataC R F fun i t σ P m ω BW f _ _ =>
    ∀ κ ∈ Lev.levA (Vc D i) (levV R i t P m), ∀ Q : PolF D (Wc D i).rank (Vc D i).rank,
      ω (κ, 1) (ptAt R i σ BW f Q) = (Lev.levChi (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) P m) κ)⁻¹ • ptAt R i σ BW f Q

open Datum in

def InnerProductFormulaC (F : Face D A) : Prop :=
  ForLiftDataC R F fun i t σ P m ω BW f _ _ =>
    ∀ (ν : Measure (GA D (Vc D i))) (𝓕 : Set (GA D (Vc D i))), IsMeasDef (Vc D i) (levV R i t P m) ν 𝓕 →
    ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓧 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧 →
    ∀ Fr : Frames (Wc D i), IsFrames (Wc D i) Fr → ∀ mR : ∀ ρ, Measure (Upq (Wc D i) ρ), (∀ ρ, Lev.IsMinf (mR ρ)) →
    ∀ U₁ ∈ R.Wall i σ, ∀ U₂ ∈ R.Wall i σ, ∀ (v₁ v₂ : ∀ ρ, lowT (R.MW i σ) ρ) (Q₁ Q₂ : PolF D (Wc D i).rank (Vc D i).rank),
      let φ₁ := ptAt R i σ BW f Q₁
      let φ₂ := ptAt R i σ BW f Q₂
      let F₁ := U₁ fun ρ => v₁ ρ
      let F₂ := U₂ fun ρ => v₂ ρ
      let Z : GA D (Wc D i) → ℂ := fun g => l2 μ 𝓧 (ω (1, g) φ₁) φ₂ * starRingEnd ℂ (petW R i (rTr (Wc D i) g F₁) F₂)
      let pt : FinCos (Wc D i) (levW R i) → (∀ ρ, Upq (Wc D i) ρ) → GA D (Wc D i) := fun x b =>
        x.rep * realElt R.θ (Wc D i) fun ρ => realMat (Wc D i) Fr ρ (b ρ)
      (∀ h, IntegrableOn (fun g => thetaKO ω h g φ₁ * starRingEnd ℂ (F₁ g)) (R.fdW i) (R.νW i)) ∧
      IntegrableOn (fun h => upLift R i ω φ₁ F₁ h * starRingEnd ℂ (upLift R i ω φ₂ F₂ h)) 𝓕 ν ∧
      ∫⁻ b, ∑' x, ‖Z (pt x b)‖ₑ ∂(Measure.pi mR) < ⊤ ∧
      l2 ν 𝓕 (upLift R i ω φ₁ F₁) (upLift R i ω φ₂ F₂) = ((ν 𝓕).toReal : ℂ) * ∫ b, ∑' x, Z (pt x b) ∂(Measure.pi mR)

open Datum in

def FockCoefficientC (F : Face D A) : Prop :=
  ForLiftDataC R F fun i _ σ _ _ ω BW f c io =>
    ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓧 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧 →
    ∀ x ∈ GfC (Wc D i), ∀ g : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ,
      (∀ ρ, g ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D (Wc D i) ρ)) → ∀ (e e' : ∀ ρ, lowT (R.MW i σ) ρ) (w w' : c.W),
      l2 μ 𝓧 (ω (1, x * realElt R.θ (Wc D i) g) (ptAt R i σ BW f (io (PiTensorProduct.tprod ℂ e) w)))
          (ptAt R i σ BW f (io (PiTensorProduct.tprod ℂ e') w')) =
        Formalism.E.fock (deltaAtEmb D i σ) (deltaAtEmb D i σ) *
          (∏ ρ, ⟪((e' ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ), (R.MW i σ).rep ρ (g ρ) ((e ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)⟫_ℂ) *
          ⟪w', w⟫_ℂ * l2 μ 𝓧 (ω (1, x) f) f

open Datum in

def FiniteZetaL (F : Face D A) : Prop :=
  ∀ i t σ s P cμ cη m ω BW f₀ f c io, IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io →
    ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓧 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧 →
    ∀ ev : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ, typePart R i σ t P ev ≠ ⊥ →
      ∃ B : GlobalTheory.LFun.Fam D.host.E, GlobalTheory.LFun.IsSysParamD D (finS R t) D.R.r ev B ∧
        (∀ w, OffS D (finS R t) w → ∀ β ∈ B w, ‖(β : ℂ)‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((D.R.r : ℝ) - 1) / 2)) ∧
        GlobalTheory.LFun.Converges (GlobalTheory.LFun.above D.host.E (finS R t : Set (HeightOneSpectrum (𝓞 D.host.F))))
          (GlobalTheory.LFun.twist B (GlobalTheory.LFun.val cμ)⁻¹) ((1 + (D.R.t : ℂ)) / 2) ∧
        ∀ U₁ ∈ partFull R.θ (R.MW i σ) (levS _ (R.βW i) (R.datWp i P)) (Lev.levChi _ (R.βW i) (R.datWp i P)) (finS R t) ev,
        ∀ U₂ ∈ R.Wall i σ, ∀ v₁ v₂ : (R.MW i σ).Vec,
          HasSum (fun y : FinCos (Wc D i) (levW R i) =>
              l2 μ 𝓧 (ω (1, y.rep) f) f * starRingEnd ℂ (petW R i (rTr (Wc D i) y.rep (U₁ v₁)) (U₂ v₂)))
            ((Nat.card P.H : ℂ) * (nrm2 μ 𝓧 f : ℂ) * (GlobalTheory.LFun.LSD D (finS R t) B cμ ((1 + (D.R.t : ℂ)) / 2) / (dOff D (finS R t) : ℂ)) *
              starRingEnd ℂ (petW R i (U₁ v₁) (U₂ v₂)))

open Datum in

def LevelIndexNormC (F : Face D A) : Prop :=
  ForLiftDataC R F fun i t _ P m _ _ f _ _ =>
    levV R i t P m ≤ GlobalTheory.Mass.Levels.latLev (Vc D i) ∧
    ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓧 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧 →
      (((levV R i t P m).relIndex (GlobalTheory.Mass.Levels.latLev (Vc D i)) : ℕ) : ℝ) * nrm2 μ 𝓧 f = ∏ v ∈ finS R t, (dLoc D v)⁻¹

def RealLowestKTypeCoeffSquareIntegrable : Prop :=
  ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau), ∃ δ : ℝ, 0 < δ ∧
    ∀ Fr : Frames (Wc D i), IsFrames (Wc D i) Fr → ∀ mR : Measure (Upq (Wc D i) ρ), Lev.IsMinf mR →
    ∀ e : lowT (R.MW i σ) ρ, ‖((e : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)‖ = 1 →
      let k : Upq (Wc D i) ρ → ℝ := fun b => ‖⟪((e : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ),
        (R.MW i σ).rep ρ (realMat (Wc D i) Fr ρ b) ((e : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)⟫_ℂ‖ ^ 2
      Integrable k mR ∧ ∫ b, k b ∂mR = δ

end GlobalTheory.LiftRows

end
end

