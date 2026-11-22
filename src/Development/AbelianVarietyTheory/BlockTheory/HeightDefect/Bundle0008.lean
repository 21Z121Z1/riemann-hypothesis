import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Formalism.LocalToGlobal.ProjectiveLattices.LiftCurveSt
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0039
import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0022
import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods

-- bundled from Development.AbelianVarietyTheory.BlockTheory.HeightDefect.DegreeIdentityCharacter
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CM

noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.DegreeIdentityCharacter

section Period

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def hostChar (H : Host E) : DirichletCharacter ℂ H.d :=
  haveI : Fact H.d.Prime := ⟨H.d_prime⟩
  (quadraticChar (ZMod H.d)).ringHomComp (Int.castRingHom ℂ)

def logOmega (H : Host E) : ℝ :=
  haveI : NeZero H.d := ⟨H.d_prime.ne_zero⟩
  (logOm E (hostChar H)).re

theorem hostChar_apply (H : Host E) (n : ℤ) : hostChar H (n : ZMod H.d) = (jacobiSym n H.d : ℂ) := by
  haveI : Fact H.d.Prime := ⟨H.d_prime⟩
  rw [← jacobiSym.legendreSym.to_jacobiSym]
  rfl

theorem hostChar_ne_one (H : Host E) : hostChar H ≠ 1 := by
  haveI : Fact H.d.Prime := ⟨H.d_prime⟩
  have h2 : ringChar (ZMod H.d) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    have := H.d_mod
    omega
  exact (MulChar.ringHomComp_ne_one_iff (f := Int.castRingHom ℂ) Int.cast_injective).2 (quadraticChar_ne_one h2)

theorem lFunction_one_ne_zero (H : Host E) :
    haveI : NeZero H.d := ⟨H.d_prime.ne_zero⟩
    (hostChar H).LFunction 1 ≠ 0 :=
  haveI : NeZero H.d := ⟨H.d_prime.ne_zero⟩
  DirichletCharacter.LFunction_apply_one_ne_zero (hostChar_ne_one H)

end Period

def EigenLineDegree : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] [NumberField K]
    (T : PAT H (Sp (𝓞 K))) (ρ : 𝓞 K) (τ : 𝓞 E →+* 𝓞 K), ρ ^ 2 = -(H.d : 𝓞 K) →
    (HasType H T.t.act ρ 1 0 ∧ τ H.rt = ρ) ∨ (HasType H T.t.act ρ 0 1 ∧ τ H.rt = -ρ) →
    ∀ (F : GenFib T.pol) (h : HermFam K (Fin F.P₀.g → K)), F.IsHerm h →
      deg h (F.eigLat T.t.act τ) = logOmega H / 2

def DiffLength : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] [NumberField K]
    (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ) (X : CMObj H K ρ σ₁ p q) (j : Fin p ⊕ Fin q)
    (FA : GenFib (X.A j.isLeft).pol) (FB : GenFib X.B.pol)
    (hA : HermFam K (Fin FA.P₀.g → K)) (hB : HermFam K (Fin FB.P₀.g → K))
    (M : (Fin FA.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K)),
    FA.IsHerm hA → FB.IsHerm hB → FA.IsDiffOf FB (X.φ j) M →
    ∀ (τ : 𝓞 E →+* 𝓞 K), ∀ c ∈ FA.eigLat (X.A j.isLeft).t.act τ, ∀ s : K →+* ℂ,
      hB.nrm s (M c) ^ 2 = ‖s (τ (X.hh j) : K)‖ * hA.nrm s c ^ 2

def EigenImagesSpan : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] [NumberField K]
    (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ) (X : CMObj H K ρ σ₁ p q)
    (FA : ∀ b : Bool, GenFib (X.A b).pol) (FB : GenFib X.B.pol)
    (M : ∀ j : Fin p ⊕ Fin q, (Fin (FA j.isLeft).P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K)),
    (∀ j, (FA j.isLeft).IsDiffOf FB (X.φ j) (M j)) →
    ∀ τ : 𝓞 E →+* 𝓞 K,
      (∀ j : Fin p ⊕ Fin q, ∀ c ∈ (FA j.isLeft).eigLat (X.A j.isLeft).t.act τ, M j c ∈ FB.eigLat X.B.t.act τ) ∧
      (FB.eigLat X.B.t.act τ : Set (Fin FB.P₀.g → K)) ⊆
        Submodule.span K {y | ∃ j : Fin p ⊕ Fin q, ∃ c ∈ (FA j.isLeft).eigLat (X.A j.isLeft).t.act τ, y = M j c}

def KeyDegreeIdentity : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (hg : 1 ≤ F.P₀.g)
    (rig : LB.Gen (F.P₀.L.pull (eSec F.P₀.A))) (hr : rig.IsGen) (th : F.P₀.L.Sec)
    (hth : ∀ s : Sp K, ∃ x : F.P₀.A.left, F.P₀.A.hom x = s ∧ x ∈ Out.nonzeroLocus th)
    (h : HermFam K (Fin F.P₀.g → K)) (δ : ℝ), F.IsHerm h → IsThetaDeg (F.key hg rig hr th hth) δ →
      δ = (1 / 2) * (-deg h F.lieLat) + (P.g : ℝ) / 4 * Real.log (2 * Real.pi)

def DegreeBounds : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] [NumberField K]
    (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ) (X : CMObj H K ρ σ₁ p q) (La : ℝ), 0 < La →
    (∀ (j : Fin p ⊕ Fin q) (τ : E →+* ℂ), ‖τ (X.hh j : E)‖ ≤ La ^ 2) →
    ∀ FB : GenFib X.B.pol,
      (∀ h : HermFam K (Fin FB.P₀.g → K), FB.IsHerm h →
        (Module.finrank ℚ E : ℝ) / 2 * (p + q) * (logOmega H / 2 - Real.log La) ≤ deg h FB.lieLat) ∧
      ∀ (hg : 1 ≤ FB.P₀.g) (rig : LB.Gen (FB.P₀.L.pull (eSec FB.P₀.A))) (hr : rig.IsGen) (th : FB.P₀.L.Sec)
        (hth : ∀ s : Sp K, ∃ x : FB.P₀.A.left, FB.P₀.A.hom x = s ∧ x ∈ Out.nonzeroLocus th) (δ : ℝ),
        IsThetaDeg (FB.key hg rig hr th hth) δ →
          δ ≤ -((Module.finrank ℚ E : ℝ) / 2 * (p + q) / 2) * (logOmega H / 2 - Real.log La) +
            (Module.finrank ℚ E : ℝ) / 2 * (p + q) / 4 * Real.log (2 * Real.pi)

def CMNumbers : Prop :=
  EigenLineDegree ∧ DiffLength ∧ EigenImagesSpan ∧ KeyDegreeIdentity ∧ DegreeBounds

end GlobalTheory.IndefiniteRowSideFullHecke.DegreeIdentityCharacter
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FullTranscendenceDegree
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FullTranscendenceDegree

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
  Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j)

abbrev CuspAt (u : WeightFamilies.Wt D j) : Type := (recB h.toLawsCore).Cusp j u

abbrev XP : WeightAlgebra.PJ D (recB h.toLawsCore) T.G.P j :=
  xplus (recPJ h j hj) (extAll h j hj) (intAtExt_extAll h j hj)

def GeneratesIn {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : WeightAlgebra.PJ D B P j) {wL : WeightFamilies.Wt D j} {N : ℕ}
    (s : 𝓞 B.KO) (w : Fin N → B.Cusp j wL) : Prop :=
  Submodule.span (𝓞 B.KO) (Set.range w) = X.WWc s wL

def Generates {wL : WeightFamilies.Wt D j} {N : ℕ} (s : 𝓞 T.Q.c.F) (w : Fin N → CuspAt h j wL) : Prop :=
  GeneratesIn (XP h j hj) s w

def ptNorm (σ : T.Q.c.F →+* ℂ) (u : WeightFamilies.Wt D j) (F : CuspAt h j u) (p : FPt (T.U j σ).X) : ℝ :=
  ((T.U j σ).X p.1).pnorm (laU (T.U j σ) (wtA u) u.n p.1) (rdU (T.U j σ) (F.1 : T.R j) p.1) p.2.1

def l2Norm (σ : T.Q.c.F →+* ℂ) {wL : WeightFamilies.Wt D j} {N : ℕ} (w : Fin N → CuspAt h j wL)
    (p : FPt (T.U j σ).X) : ℝ :=
  Real.sqrt (∑ i, ptNorm h j σ wL (w i) p ^ 2)

def NoCommonZero {wL : WeightFamilies.Wt D j} {N : ℕ} (w : Fin N → CuspAt h j wL) : Prop :=
  ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ p : FPt (T.U j σ).X,
    ∃ i, rdU (T.U j σ) ((w i).1 : T.R j) p.1 p.2.1 ≠ 0

def FullTrdeg (hg : GenFrEx (T.Q.Xo j) T.Q.c) {wL : WeightFamilies.Wt D j} {N : ℕ} (w : Fin N → CuspAt h j wL) : Prop :=
  ∀ Z : Comp (T.Q.Xo j) T.Q.c, ∃ i₀, evC hg Z ((w i₀).1 : T.R j) ≠ 0 ∧
    Algebra.trdeg T.Q.c.F (IntermediateField.adjoin T.Q.c.F
      (Set.range fun i => evC hg Z ((w i).1 : T.R j) / evC hg Z ((w i₀).1 : T.R j))) = (WeightFamilies.dimY D j : Cardinal)

def SmallForm {wL : WeightFamilies.Wt D j} {N : ℕ} (w : Fin N → CuspAt h j wL) : Prop :=
  ∃ (k m₀ : ℕ) (β : CuspAt h j (WeightAlgebra.wsmul k wL)), (XP h j hj).NonZeroComp (WeightAlgebra.wsmul k wL) β ∧
    ∃ C : ℝ, ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ p : FPt (T.U j σ).X,
      ptNorm h j σ (WeightAlgebra.wsmul k wL) β p ≤ C * l2Norm h j σ w p ^ k ∧
      ptNorm h j σ (WeightAlgebra.wsmul k wL) β p ^ m₀ ≤ C * l2Norm h j σ w p ^ (k * m₀ + 1)

def BigAt (hg : GenFrEx (T.Q.Xo j) T.Q.c) {wL : WeightFamilies.Wt D j} {N : ℕ} (w : Fin N → CuspAt h j wL) : Prop :=
  NoCommonZero h j w ∧ FullTrdeg h j hg w ∧ SmallForm h j hj w

def ExistsNonzeroCuspFormOfWeightPair (wL wF : WeightFamilies.Wt D j) : Prop :=
  ∃ w₂ : WeightFamilies.Wt D j, WeightAlgebra.IsG2 wL wF w₂ ∧ ∃ θ : CuspAt h j w₂, (XP h j hj).NonZeroComp w₂ θ

def CurveModelAt (hg : GenFrEx (T.Q.Xo j) T.Q.c) {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (XP h j hj) ka wL wF)
    (S : WeightAlgebra.Scal (recB h.toLawsCore)) : Prop :=
  Generates h j hj S.sW G.w → BigAt h j hj hg G.w → ExistsNonzeroCuspFormOfWeightPair h j hj wL wF →
    ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (g₀ : CuspAt h j wF), (XP h j hj).NonZeroComp wF g₀ →
      Nonempty (CurveModel (X := recPJ h j hj) (E := extAll h j hj) (hM := intAtExt_extAll h j hj) G la g₀)

def CurveModelExists : Prop :=
  ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hg : GenFrEx (T.Q.Xo j) T.Q.c)
    (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (XP h j hj) ka wL wF) (S : WeightAlgebra.Scal (recB h.toLawsCore)),
    CurveModelAt h j hj hg G S

example : XP h j hj = recPlus h j hj := rfl

example {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (XP h j hj) ka wL wF) (S : WeightAlgebra.Scal (recB h.toLawsCore)) (a b : ℝ)
    (hT : G.TiedW S a b) : Generates h j hj S.sW G.w := hT.1

theorem ptNorm_nonneg (σ : T.Q.c.F →+* ℂ) (u : WeightFamilies.Wt D j) (F : CuspAt h j u) (p : FPt (T.U j σ).X) :
    0 ≤ ptNorm h j σ u F p :=
  mul_nonneg (norm_nonneg _) (pnorm_fac_nonneg _ _ _)

theorem ptNorm_le_l2Norm (σ : T.Q.c.F →+* ℂ) {wL : WeightFamilies.Wt D j} {N : ℕ} (w : Fin N → CuspAt h j wL)
    (p : FPt (T.U j σ).X) (i : Fin N) : ptNorm h j σ wL (w i) p ≤ l2Norm h j σ w p :=
  Real.le_sqrt_of_sq_le
    (Finset.single_le_sum (f := fun i => ptNorm h j σ wL (w i) p ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i))

example (σ : T.Q.c.F →+* ℂ) (u : WeightFamilies.Wt D j) (F : CuspAt h j u) :
    supE (T.U j σ).X (laU (T.U j σ) (wtA u) u.n) (rdU (T.U j σ) (F.1 : T.R j)) =
      ⨆ p, ENNReal.ofReal (ptNorm h j σ u F p) := rfl

end GlobalTheory.IndefiniteRowSideFullHecke.FullTranscendenceDegree
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.HeightDefect.TensorObjectExistence
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CM
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.TensorObjectExistence

def TensorExists : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (M : Type) [Field M] [NumberField M] (ω : 𝓞 M)
    (C : Ell H (𝓞 M) ω) (D : Datum H) (ε : ℤˣ) (h : D.La → D.La → OK H), IsKForm D ε h →
    (∀ x : D.La, x ≠ 0 → 0 < (ε : ℤ) * D.EF (H.w0 • x) x) →
    ∃ T : PAT H (Sp (𝓞 M)), Nonempty (IsTen C D h T)

def TensorIsObject : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (M : Type) [Field M] [NumberField M] (ω : 𝓞 M)
    (C : Ell H (𝓞 M) ω) (D : Datum H) (ε : ℤˣ) (h : D.La → D.La → OK H) (T : PAT H (Sp (𝓞 M))), IsKForm D ε h →
    Nonempty (IsTen C D h T) →
    ∀ (l : Level H) (K' : Type) [Field K'] [NumberField K'] (β : 𝓞 M →+* K') (κ : KA l →+* K'),
      (D.q = 0 ∧ κ (baseKA l).ρ = β (2 * ω - 1)) ∨ (D.p = 0 ∧ κ (baseKA l).ρ = -β (2 * ω - 1)) →
      ∃ (K₁ : Type) (_ : Field K₁) (_ : NumberField K₁) (j : K' →+* K₁)
        (o : Obj D l (baseKA l) (spMap (j.comp κ))), Nonempty (SABMap o.t T.t (spMap (j.comp β)))

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def IsExpAt {S : Scheme.{0}} (t : SAB H S) (x : Sp ℂ ⟶ S) (D : Datum H) {g : ℕ} (ty : Fin g → (E →+* ℂ))
    (Pe : D.La →+ (Fin g → ℂ)) (e : (Fin g → ℂ) → (Over.mk x ⟶ t.G)) : Prop :=
  IsPeriod D ty Pe ∧ IsHolTo Set.univ (fun z => (e z).left) ∧ (∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective e ∧
    (∀ z, e z = 1 ↔ z ∈ Pe.range) ∧ (∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ t.act.act a) ∧
    ∀ (k : ℕ) (a b : D.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D.EF a b : ℂ) / k) →
      Out.WeilIs t.G t.PP.L k (e ((k : ℂ)⁻¹ • Pe a)) (e ((k : ℂ)⁻¹ • Pe b)) (unitOn c)

def TiedToLattices {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)} {hP : IsPeriod D ty Pe}
    {p q : ℕ} (Z : CMLat hP p q) {K : Type} [Field K] [NumberField K] {ρ : 𝓞 K} {σ₁ : K →+* ℂ} (X : CMObj H K ρ σ₁ p q)
    (eB : (Fin g → ℂ) → (Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ X.B.t.G)) : Prop :=
  IsExp X.B (σ₁.comp (algebraMap (𝓞 K) K)) D ty Pe eB ∧ X.hh = Z.hh ∧
    ∃ (g₁ : Bool → ℕ) (ty₁ : ∀ b, Fin (g₁ b) → (E →+* ℂ)) (P₁ : ∀ b, (Z.D₁ b).La →+ (Fin (g₁ b) → ℂ))
      (e₁ : ∀ b, (Fin (g₁ b) → ℂ) → (Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ (X.A b).t.G)),
      (∀ b, IsTypeFn H (Z.D₁ b).p (Z.D₁ b).q (ty₁ b) ∧
        IsExp (X.A b) (σ₁.comp (algebraMap (𝓞 K) K)) (Z.D₁ b) (ty₁ b) (P₁ b) (e₁ b)) ∧
      ∀ j : Fin p ⊕ Fin q, ∃ F : (Fin (g₁ j.isLeft) → ℂ) →ₗ[ℂ] (Fin g → ℂ),
        (∀ a, F (P₁ j.isLeft a) = Pe (Z.f j a)) ∧ ∀ z, e₁ j.isLeft z ≫ X.φ j = eB (F z)

def PointCarriesObject : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (K' : Type) [Field K'] [NumberField K'] (κ : KA l →+* K') (σ' : K' →+* ℂ) (x : Sp ℂ ⟶ Xo.X)
    (D' : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Pe : D'.La →+ (Fin g → ℂ)) (hP : IsPeriod D' ty Pe)
    (e : (Fin g → ℂ) → (Over.mk x ⟶ Xo.univ.t.G)) (Z : CMLat hP D.p D.q),
    1 ≤ D.p + D.q → σ' (κ (baseKA l).ρ) = H.rt0 → x ≫ Xo.s = spMap (σ'.comp κ) → D'.p = D.p → D'.q = D.q → IsTypeFn H D.p D.q ty →
    IsExpAt Xo.univ.t x D' ty Pe e →
    ∃ (K₁ : Type) (_ : Field K₁) (_ : NumberField K₁) (j : K' →+* K₁) (σ₁ : K₁ →+* ℂ) (ρ : 𝓞 K₁)
      (X : CMObj H K₁ ρ σ₁ D.p D.q) (y : Sp K₁ ⟶ Xo.X) (o : Obj D l (baseKA l) (spMap (j.comp κ)))
      (mU : ObjMap o Xo.univ y) (mB : SABMap o.t X.B.t (spMap (algebraMap (𝓞 K₁) K₁)))
      (eB : (Fin g → ℂ) → (Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K₁) K₁))) ⟶ X.B.t.G)),
      σ₁.comp j = σ' ∧ (ρ : K₁) = j (κ (baseKA l).ρ) ∧ y ≫ Xo.s = spMap (j.comp κ) ∧ spMap σ₁ ≫ y = x ∧
      (∀ z, ∃ w : Over.mk (spMap σ₁) ⟶ o.t.G,
        w.left ≫ mU.toSABMap.φ = (e z).left ∧ w.left ≫ mB.φ = (eB z).left) ∧
      TiedToLattices Z X eB

def CMExists : Prop := (TensorExists ∧ TensorIsObject) ∧ PointCarriesObject

theorem isExpAt_of_familyUnif {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (U : FamilyUnif Xo σ ty) (i : Fin U.n) (Pe : (U.Di i).La →+ (Fin g → ℂ))
    (hP : IsPeriod (U.Di i) ty Pe) : IsExpAt Xo.univ.t (U.u i Pe) (U.Di i) ty Pe (U.ex i Pe) := by
  refine ⟨hP, fun V f => ?_, U.ex_add i Pe hP, U.ex_onto i Pe hP, U.ex_ker i Pe hP, U.ex_lin i Pe hP,
    U.ex_weil i Pe hP⟩
  obtain ⟨h₁, h₂⟩ := (U.hol i 0 Set.univ (fun _ => Pe) isOpen_univ
    ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2 V f
  have hd : Differentiable ℂ fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z) := by fun_prop
  refine ⟨?_, ?_⟩
  · simpa using h₁.preimage hd.continuous
  · have h₃ := DifferentiableOn.comp (s := {z ∈ Set.univ | ⊤ ≤ (U.ex i Pe z).left ⁻¹ᵁ V}) h₂ hd.differentiableOn
      fun z hz => Set.mem_sep (Set.mk_mem_prod (Set.mem_univ _) (Set.mem_univ _)) hz.2
    simpa only [Function.comp_def] using h₃

example (D : Datum H) (ε : ℤˣ) : ∃ h : D.La → D.La → OK H, IsKForm D ε h :=
  ⟨fun x y => (((ε : ℤ) * (D.EF (H.w0 • x) y - D.EF x y) : ℤ) : OK H) + (((ε : ℤ) * D.EF x y : ℤ) : OK H) * wK H,
    fun x y => by simp [wK]⟩

end GlobalTheory.IndefiniteRowSideFullHecke.TensorObjectExistence
end
end

