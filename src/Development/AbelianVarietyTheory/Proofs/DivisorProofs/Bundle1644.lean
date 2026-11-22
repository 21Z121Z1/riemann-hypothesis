import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1129
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1592
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1593
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0019
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousThetaTransformAdelicSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1617
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1326
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1618
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1619
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1097
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtActIffEqGtSmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1614

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreNotInClosure
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ChTor GlobalTheory.HTLat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WeilIntegral

section Open

variable {S : Scheme.{0}} {X T : Over S}

def InOpen (U : X.left.Opens) (w : T ⟶ X) : Prop := w.left ⁻¹ᵁ U = ⊤

theorem inOpen_top (w : T ⟶ X) : InOpen ⊤ w := rfl

theorem InOpen.comp {U : X.left.Opens} {w : T ⟶ X} (h : InOpen U w) {T' : Over S} (u : T' ⟶ T) :
    InOpen U (u ≫ w) := by
  unfold InOpen at h ⊢
  rw [Over.comp_left, Scheme.Hom.comp_preimage, h]
  rfl

def CubeIn [GrpObj X] (U : X.left.Opens) (z a b c : T ⟶ X) : Prop :=
  ∀ i j k : ℕ, i ≤ 1 → j ≤ 1 → k ≤ 1 → InOpen U (z * a ^ i * b ^ j * c ^ k)

end Open

section Field

variable {C : Type} [Field C]

def CubeFn (A : Over (Sp C)) : Type 1 :=
  ∀ (S : Type) [CommRing S] (t : Sp S ⟶ Sp C),
    (Over.mk t ⟶ A) → (Over.mk t ⟶ A) → (Over.mk t ⟶ A) → (Over.mk t ⟶ A) → Sˣ

def CubeFn.IsNatural {A : Over (Sp C)} [GrpObj A] (Θ : CubeFn A) (V : A.left.Opens) : Prop :=
  ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S') (t : Sp S ⟶ Sp C) (t' : Sp S' ⟶ Sp C)
    (z a b c : Over.mk t ⟶ A) (z' a' b' c' : Over.mk t' ⟶ A),
    z'.left = spMap φ ≫ z.left → a'.left = spMap φ ≫ a.left → b'.left = spMap φ ≫ b.left →
    c'.left = spMap φ ≫ c.left → CubeIn V z a b c →
    (Θ S' t' z' a' b' c' : S') = φ (Θ S t z a b c : S)

def CubeFn.GivesWeil [IsAlgClosed C] [CharZero C] (A : Out.PolAV (Sp C)) (Θ : CubeFn A.A) (V : A.A.left.Opens) :
    Prop :=
  ∀ (N : ℕ), 1 ≤ N → ∀ x y z : Pts A.A, x ^ N = 1 → y ^ N = 1 →
    (∀ i j : ℕ, InOpen V (z * x ^ i * y ^ j)) →
    weil A N x y = (∏ i ∈ Finset.range N, Θ C (𝟙 _) z (y ^ i) y x) /
      ∏ i ∈ Finset.range N, Θ C (𝟙 _) z (x ^ i) x y

def HasCubeFn [IsAlgClosed C] [CharZero C] (A : Out.PolAV (Sp C)) : Prop :=
  ∀ V : A.A.left.Opens, (∃ g : LB.Gen (A.L.pull V.ι), g.IsGen) →
    ∃ Θ : CubeFn A.A, Θ.IsNatural V ∧ Θ.GivesWeil A V

example {A : Over (Sp C)} [GrpObj A] (V : A.left.Opens) :
    CubeFn.IsNatural (A := A) (fun _ _ _ _ _ _ _ => 1) V := by
  intro S S' _ _ φ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  simp

end Field

section Ring

variable (p : ℕ) (O : Type) [CommRing O]

def LocalUnits : Prop :=
  ∀ (R : Type) [CommRing R] [Algebra O R] [Algebra.Smooth O R] (B : Type) [CommRing B] [Algebra O B] [IsLocalRing B]
    [Module.Finite O B] [Module.Flat O B] (θ : R →ₐ[O] B) (ψ : B →ₐ[O] O) (f g : R) (c : O), c ≠ 0 →
    f * g = algebraMap O R c → ∃ u : Bˣ, θ f = algebraMap O B (ψ (θ f)) * u

def SpecialFibreNotInClosure : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra O R] [Algebra.Smooth O R] (f : R), f ≠ 0 →
    (∃ q : PrimeSpectrum R, (p : R) ∈ q.asIdeal) →
    ∃ (q : PrimeSpectrum R) (g : R) (c : O), (p : R) ∈ q.asIdeal ∧ g ∉ q.asIdeal ∧ c ≠ 0 ∧
      f ∣ algebraMap O R c * g

end Ring

section AtPoint

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
  [Algebra O C] {Λ : Type} [CommRing Λ] [StarRing Λ] (P : Point p v O Λ)

def MeetsSpecial (U : P.G.left.Opens) : Prop :=
  ∃ x : P.G.left, x ∈ U ∧ (p : O) ∈ PrimeSpectrum.asIdeal (R := O) (P.G.hom x)

def HasTrivialisingOpen : Prop :=
  ∃ U : P.G.left.Opens, MeetsSpecial P U ∧ ∃ g : LB.Gen (P.A.L.pull (P.gen ⁻¹ᵁ U).ι), g.IsGen

def TranslatesInto : Prop :=
  ∀ U : P.G.left.Opens, MeetsSpecial P U → ∀ (J : Type) [Finite J] (a : J → (specO O O ⟶ P.G)),
    ∃ z : specO O O ⟶ P.G, ∀ i, InOpen U (z * a i)

def IsGeneric (z : specO O O ⟶ P.G) (z' : Pts P.A.A) : Prop :=
  z'.left ≫ P.gen = spMap (algebraMap O C) ≫ z.left

def CubeValuesIntegral : Prop :=
  ∀ (U : P.G.left.Opens) (Θ : CubeFn P.A.A), Θ.IsNatural (P.gen ⁻¹ᵁ U) →
    ∀ (B : Type) [CommRing B] [Algebra O B] [IsLocalRing B] [Module.Finite O B] [Module.Flat O B],
    Nonempty (B →ₐ[O] O) → ∀ z a b c : specO O B ⟶ P.G, CubeIn U z a b c →
    ∃ (d : Cˣ) (u : Bˣ), ∀ (ψ : B →ₐ[O] O) (z' a' b' c' : Pts P.A.A),
      IsGeneric P (ptMap ψ ≫ z) z' → IsGeneric P (ptMap ψ ≫ a) a' → IsGeneric P (ptMap ψ ≫ b) b' →
      IsGeneric P (ptMap ψ ≫ c) c' →
      (Θ C (𝟙 _) z' a' b' c' : C) = d * algebraMap O C (ψ u)

variable [IsAlgClosed C] [CharZero C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]

def WeilIntegralOn (B : Type) [CommRing B] [Algebra O B] : Prop :=
  ∀ (N : ℕ), 1 ≤ N → ∀ x y : specO O B ⟶ P.Gt, x ^ N = 1 → y ^ N = 1 →
    ∃ u : B, ∀ ψ : B →ₐ[O] O,
      algebraMap O C (ψ u) = (weil P.A N (P.toA (ptMap ψ ≫ x)) (P.toA (ptMap ψ ≫ y)) : C)

def WeilIntegralLocal : Prop :=
  ∀ (B : Type) [CommRing B] [Algebra O B] [IsLocalRing B] [Module.Finite O B] [Module.Flat O B],
    WeilIntegralOn P B

def WeilIntegralFinite : Prop :=
  ∀ (B : Type) [CommRing B] [Algebra O B] [Module.Finite O B] [Module.Flat O B], WeilIntegralOn P B

theorem toA_isGeneric (x : specO O O ⟶ P.Gt) : IsGeneric P (P.toG x) (P.toA x) :=
  (P.eq_toA_iff x _).1 rfl

end AtPoint

end GlobalTheory.WeilIntegral
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StdCharHalfSymplecticFormRealCoordinates
section
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

noncomputable section

namespace GlobalTheory.RealCharF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem infPartF_cAF (σ : E →ₐ[F] E) (z : AEF F E) :
    infPartF F E (cAF σ z) = sigR (Ainf F) σ (infPartF F E z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add a b ha hb => simp only [map_add, ha, hb]

theorem conj_theta_tmul_one [IsTotallyReal F] {τ : E →+* ℂ} {w : InfinitePlace F}
    (hw : w.embedding = τ.comp (algebraMap F E)) {θ : Ainf F ⊗[F] E →+* ℂ} (h : IsInfEmbF τ θ) (a : Ainf F) :
    starRingEnd ℂ (θ (a ⊗ₜ[F] (1 : E))) = θ (a ⊗ₜ[F] (1 : E)) := by
  have hv : w.IsReal := IsTotallyReal.isReal w
  rw [GlobalTheory.DualPairCompare.gen_inf_val τ w hw θ h a, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hv]
  exact Complex.conj_ofReal _

theorem theta_sigR {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {τ : E →+* ℂ} {w : InfinitePlace F}
    (hw : w.embedding = τ.comp (algebraMap F E)) {θ : Ainf F ⊗[F] E →+* ℂ} (h : IsInfEmbF τ θ)
    (y : Ainf F ⊗[F] E) : θ (sigR (Ainf F) σ y) = starRingEnd ℂ (θ y) := by
  haveI : IsTotallyReal F := hσ.1
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a e =>
    have e1 : ∀ e' : E, a ⊗ₜ[F] e' = (a ⊗ₜ[F] (1 : E)) * ((1 : Ainf F) ⊗ₜ[F] e') := by
      intro e'; rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    show θ (a ⊗ₜ[F] σ e) = _
    rw [e1 (σ e), e1 e, map_mul, map_mul, map_mul, h.1, h.1, hσ.2.2.2, conj_theta_tmul_one hw h a]
    rfl

theorem theta_infPartF_incAF {τ : E →+* ℂ} {θ : Ainf F ⊗[F] E →+* ℂ} (h : IsInfEmbF τ θ) (e : E) :
    θ (infPartF F E (incAF F E e)) = τ e := by
  have : infPartF F E (incAF F E e) = (1 : Ainf F) ⊗ₜ[F] e := by
    show (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) ((1 : AF F) ⊗ₜ[F] e) = _
    rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
  rw [this, h.1]

theorem theta_fstA_symplOHF {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {τ : E →+* ℂ} {w : InfinitePlace F}
    (hw : w.embedding = τ.comp (algebraMap F E)) {θ : Ainf F ⊗[F] E →+* ℂ} (h : IsInfEmbF τ θ)
    {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (x y : WOF F E nS nT) :
    θ (fstA F (symplOHF σ JS JT ξ₀ x y) ⊗ₜ[F] (1 : E)) =
      ((τ ξ₀ * θ (infPartF F E (hOF σ JS JT x y))).re : ℂ) := by
  set z := incAF F E ξ₀ * hOF σ JS JT x y with hz
  have h1 : fstA F (symplOHF σ JS JT ξ₀ x y) =
      algebraMap F (Ainf F) (1 / 2) * Algebra.trace (Ainf F) (Ainf F ⊗[F] E) (infPartF F E z) := by
    unfold symplOHF symplOF
    rw [map_mul, AlgHom.commutes, GlobalTheory.HeisLineDiffF.map_trace_tens]
    rfl
  have h2 : ∀ c : Ainf F, c ⊗ₜ[F] (1 : E) = algebraMap (Ainf F) (Ainf F ⊗[F] E) c := by
    intro c
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  have h3 : θ (algebraMap (Ainf F) (Ainf F ⊗[F] E) (algebraMap F (Ainf F) (1 / 2))) = 1 / 2 := by
    rw [← IsScalarTower.algebraMap_apply]
    have : (θ.comp (algebraMap F (Ainf F ⊗[F] E))) (1 / 2) = 1 / 2 := by
      rw [map_div₀, map_one, map_ofNat]
    exact this
  have h4 : θ (infPartF F E z) = τ ξ₀ * θ (infPartF F E (hOF σ JS JT x y)) := by
    rw [hz, map_mul, map_mul, theta_infPartF_incAF h]
  rw [h1, h2, map_mul, map_mul, GlobalTheory.SelfDualLatticeCompare.trace_tensor (Ainf F) hσ, map_add,
    theta_sigR hσ hw h, h3, h4, Complex.add_conj]
  push_cast
  ring

theorem theta_hOF {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {tau : InfinitePlace F → (E →+* ℂ)}
    (hw : ∀ w, w.embedding = (tau w).comp (algebraMap F E)) {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)}
    (hθ : IsInfFamF tau θ) {ι : (InfinitePlace F → ℂ) →+ AEF F E} (hι : IsChartF θ ι)
    {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} (JT : Matrix (Fin nT) (Fin nT) E) (hJS : JS.det ≠ 0)
    (u v : IxF F nS nT → ℂ) (w : InfinitePlace F) :
    θ w (infPartF F E (hOF σ JS JT (iotaVF ι u) (iotaVF ι v))) =
      ((JS.map (tau w))⁻¹ * (cpt v w)ᴴ * JT.map (tau w) * cpt u w).trace := by
  rw [GlobalTheory.OrientedChar.map_inv_field _ _ hJS, GlobalTheory.OrientedChar.trace_four]
  unfold hOF
  simp only [map_sum, map_mul, infPartF_cAF, theta_sigR hσ (hw w) (hθ w), theta_infPartF_incAF (hθ w),
    iotaVF, Matrix.of_apply, hι.comp, cpt, Matrix.map_apply]

theorem trace_HMF {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E)
    (tau : InfinitePlace F → (E →+* ℂ)) (u v : IxF F nS nT → ℂ) :
    star v ⬝ᵥ HMF JS JT ξ₀ tau *ᵥ u = ∑ w, ((2 * (tau w ξ₀).im : ℝ) : ℂ) *
      ((JS.map (tau w))⁻¹ * (cpt v w)ᴴ * JT.map (tau w) * cpt u w).trace := by
  rw [star_dotProduct_eq]
  refine Finset.sum_congr rfl fun w _ => ?_
  unfold HMF
  rw [cpt_blk, ← Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul,
    Matrix.trace_smul, smul_eq_mul]
  simp only [Matrix.mul_assoc]

theorem psi_symplOHF_iotaVF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → ∀ ι : (InfinitePlace F → ℂ) →+ AEF F E, IsChartF θ ι →
      ∀ u v : IxF F nS nT → ℂ, B.ψ (symplOHF σ JS JT ξ₀ (iotaVF ι u) (iotaVF ι v)) =
        Complex.exp (Real.pi * Complex.I * ((star v ⬝ᵥ HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1) *ᵥ u).im : ℂ)) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hJS hJT ξ₀ hξ hσξ θ hθ ι hι u v
  have hσ := hB.cm
  haveI : IsTotallyReal F := hσ.1
  have hψ := GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood F E σ B hB
  have hw : ∀ w : InfinitePlace F, w.embedding = (B.emb w).1.comp (algebraMap F E) := fun w => (B.emb w).2.symm
  set s := symplOHF σ JS JT ξ₀ (iotaVF ι u) (iotaVF ι v) with hs
  have hsnd : sndA F s = 0 :=
    GlobalTheory.HeisDerivCM.map_symplOHF_eq_zero (sndA F) σ JS JT ξ₀ _ _ (Or.inr (real_iotaVF hι v))
  have e1 : B.ψ s = psiInf F B.ψ (fstA F s) := by
    have hsplit : s = pairA F (fstA F s) 0 := Prod.ext rfl hsnd
    conv_lhs => rw [hsplit]
    rfl
  have hre : ∀ w : InfinitePlace F, ((B.emb w).1 ξ₀).re = 0 := by
    intro w
    have h1 := hσ.2.2.2 (B.emb w).1 ξ₀
    rw [hσξ, map_neg] at h1
    have h2 := congrArg Complex.re h1
    rw [Complex.neg_re, Complex.star_def, Complex.conj_re] at h2
    linarith
  rw [e1, hψ.2.2 θ hθ, trace_HMF]
  have e2 : ∑ w, θ w (fstA F s ⊗ₜ[F] (1 : E)) = ∑ w, ((((B.emb w).1 ξ₀) *
      ((JS.map (B.emb w).1)⁻¹ * (cpt v w)ᴴ * JT.map (B.emb w).1 * cpt u w).trace).re : ℂ) :=
    Finset.sum_congr rfl fun w _ => by
      rw [hs, theta_fstA_symplOHF hσ (hw w) (hθ w) JS JT ξ₀ (iotaVF ι u) (iotaVF ι v),
        theta_hOF hσ hw hθ hι JT hJS.2 u v]
  rw [e2]
  congr 1
  rw [Complex.im_sum]
  simp only [Complex.mul_re, hre, Complex.im_ofReal_mul, zero_mul, zero_sub]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  ring

end GlobalTheory.RealCharF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableRationalSchwartzBruhatMulPolynomialDecay
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.LatSumSB

open GlobalTheory.WeilM GlobalTheory.ThetaTrCont

theorem summable_sb_mul_decay : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ), g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) →
    ∀ (a : κ → FiniteAdeleRing (𝓞 F) F), ∃ M : ℕ, ∀ c : κ → mixedEmbedding.mixedSpace F,
      Summable fun ξ : κ → F => ‖g (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i) + a i)‖ *
        ((1 + ‖((fun i => mixedEmbedding F (ξ i)) + c : κ → mixedEmbedding.mixedSpace F)‖) ^ M)⁻¹ := by
  intro F _ _ κ _ g hg a
  obtain ⟨B, hB⟩ := hg.1.continuous.bounded_above_of_compact_support hg.2
  have hK : IsCompact ((fun z => z - a) '' tsupport g) :=
    hg.2.isCompact.image (continuous_id.sub continuous_const)
  obtain ⟨N, hN, hKN⟩ := exists_nat_mul_integral_of_isCompact F hK
  haveI := discreteTopology_denomLattice F κ hN
  refine ⟨Module.finrank ℤ (denomLattice F κ N) + 1, fun c => ?_⟩
  set M := Module.finrank ℤ (denomLattice F κ N) + 1
  let S : Set (κ → F) := {ξ | (fun i => mixedEmbedding F (ξ i)) ∈ denomLattice F κ N}
  refine ((Subtype.val_injective (p := fun ξ => ξ ∈ S)).summable_iff ?_).1 ?_
  · intro ξ hξ
    refine mul_eq_zero_of_left ?_ _
    rw [norm_eq_zero]
    by_contra h0
    apply hξ
    have hy : (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ (fun z => z - a) '' tsupport g :=
      ⟨_, subset_tsupport _ h0, by funext i; simp⟩
    refine ⟨⟨ξ, fun i => ?_⟩, rfl⟩
    obtain ⟨y, hy'⟩ := (IntegralFinAdele.integral_finiteAdele_properties F).2.2.2.1 ((N : F) * ξ i) fun v => by
      rw [map_mul, map_natCast]
      exact hKN _ hy i v
    refine ⟨y, ?_⟩
    have h2 := congrArg (mixedEmbedding F) hy'
    rw [← nsmul_eq_mul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ] at h2
    exact h2.symm
  · let j : S → denomLattice F κ N := fun ξ => ⟨_, ξ.2⟩
    have hj : Function.Injective j := fun a b h => Subtype.ext (funext fun i =>
      mixedEmbedding_injective F (congrFun (congrArg Subtype.val h) i))
    refine Summable.of_norm_bounded
      ((((summable_one_add_norm_inv (denomLattice F κ N) (Nat.lt_succ_self _)).comp_injective hj).mul_left
        ((1 + ‖c‖) ^ M)).mul_left B) fun ξ => ?_
    set z : κ → mixedEmbedding.mixedSpace F := fun i => mixedEmbedding F (ξ.1 i)
    have hz : ‖(j ξ : denomLattice F κ N)‖ = ‖z‖ := rfl
    simp only [Function.comp_apply, hz]
    have hpos1 : 0 < (1 + ‖z + c‖) ^ M := pow_pos (add_pos_of_pos_of_nonneg one_pos (norm_nonneg _)) M
    have hpos2 : 0 < (1 + ‖z‖) ^ M := pow_pos (add_pos_of_pos_of_nonneg one_pos (norm_nonneg _)) M
    have hw : ((1 + ‖z + c‖) ^ M)⁻¹ ≤ (1 + ‖c‖) ^ M * ((1 + ‖z‖) ^ M)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hpos2, ← div_eq_inv_mul, div_le_iff₀ hpos1, ← mul_pow, mul_comm (1 + ‖c‖)]
      exact pow_le_pow_left₀ (add_pos_of_pos_of_nonneg one_pos (norm_nonneg _)).le (one_add_norm_le z c) M
    rw [norm_mul, norm_norm, Real.norm_of_nonneg (inv_nonneg.2 hpos1.le)]
    calc ‖g (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ.1 i) + a i)‖ * ((1 + ‖z + c‖) ^ M)⁻¹
        ≤ B * ((1 + ‖c‖) ^ M * ((1 + ‖z‖) ^ M)⁻¹) :=
          mul_le_mul (hB _) hw (inv_nonneg.2 hpos1.le) ((norm_nonneg _).trans (hB 0))
      _ = _ := rfl

end GlobalTheory.LatSumSB
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaReadingLinearInjectiveAtOrthonormalFrameStatement
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaReading_linear_injective_at_orthonormal_frame : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∀ x : Frame X.Ψ r, IsONFr X x → ∀ (f f' : WO V W → ℂ) (φ φ' : TF V.rank g), Reads θ V W hr X bas idx f φ x → Reads θ V W hr X bas idx f' φ' x → (∀ a b : ℂ, Reads θ V W hr X bas idx (a • f + b • f') (a • φ + b • φ') x) ∧ (f = f' → φ = φ') ∧ (IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' → φ = φ' → f = f') := by
  first | exact @GlobalTheory.AdTh.reads_linear_injective | exact GlobalTheory.AdTh.reads_linear_injective | (intros; apply GlobalTheory.AdTh.reads_linear_injective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSectionSqMultiplierAlongIsometryMoveStatement
section
open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GeoLevel GlobalTheory.LevelCusp GlobalTheory.FrameUnif
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSection_sq_multiplier_along_isometry_move : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k), ∀ b ∈ T.co ⁻¹' (M.X k).dom, ∀ b' ∈ T.co ⁻¹' (M.X k).dom, ∀ (κ κ' : ℂ) (y z y' : FrPt Xo c (CAt σ)) (gam : (F.Di k).La ≃ₗ[𝓞 E] (F.Di k).La) (A : Matrix (Fin r) (Fin r) E) (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (t : Ix Dw → (CAt σ)ˣ), κ ≠ 0 → κ' ≠ 0 → IsThetaPt T b κ y → IsThetaPt T b' κ' z → (∀ a a', (F.Di k).EF (gam a) (gam a') = (F.Di k).EF a a') → (∀ a, (M.φ k (gam a) : Fin r → E) = A *ᵥ (M.φ k a : Fin r → E)) → (A.det = 1 ∨ ((∃ m : ℕ, 0 < m ∧ A.det ^ m = 1) ∧ 4 ∣ Module.finrank ℚ E)) → (∀ a, T.Pf (T.co b') (gam a) = T.Pf (T.co b) a) → (∀ w, (F.ex k (T.Pf (T.co b')) w).left = (F.ex k (T.Pf (T.co b)) w).left ≫ ν.φ) → FrMove ρ ν y y' → FrBor t z y' → Formalism.L2.PjFree.toC (t none : CAt σ) ^ 2 * (κ' ^ 2 * (T.h b).det) = κ ^ 2 * (T.h b').det := by
  first | exact @GlobalTheory.GeoLevel.theta_move_sq | exact GlobalTheory.GeoLevel.theta_move_sq | (intros; apply GlobalTheory.GeoLevel.theta_move_sq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformRationalTranslateQuasiInvariantStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaTransform_rational_translate_quasiInvariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
      (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
      ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
      ∀ (κ : Type) [Fintype κ]
        (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
        (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
          co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
        ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (w : Formalism.IndefR.Datum.WO S T),
          GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ (ratW T S γ + w) = ψ (-(Formalism.IndefR.Datum.symplOH S T (ratW T S γ) w)) * GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ w := by
  first | exact @GlobalTheory.ThetaQuasiRat.thetaTr_ratW_add | exact GlobalTheory.ThetaQuasiRat.thetaTr_ratW_add | (intros; apply GlobalTheory.ThetaQuasiRat.thetaTr_ratW_add <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDegreeDensityPullbackEqNormSqDetMulStatement
section
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topDegreeDensity_pullback_eq_normSq_det_mul : ∀ {n : ℕ} (L : V n →L[ℂ] V n) (ω : GlobalTheory.CxForm.Alt n), GlobalTheory.CxForm.dens (GlobalTheory.CxForm.pull L ω) = ((‖L.det‖ ^ 2 : ℝ) : ℂ) * GlobalTheory.CxForm.dens ω := by
  first | exact @GlobalTheory.CxForm.dens_pull | exact GlobalTheory.CxForm.dens_pull | (intros; apply GlobalTheory.CxForm.dens_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionUnramifiedImpTateModuleAndInfiniteStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionUnramified_imp_tateModule_and_infinite : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [Field Ω] [Algebra K Ω] (V : ValuationSubring Ω) (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], (∀ m : ℕ, (m : ResidueField R) ≠ 0 → TorsionUnramified A V m) → (∃ (l : ℕ) (_ : Fact l.Prime), (l : ResidueField R) ≠ 0 ∧ TateUnramified A V l) ∧ {m : ℕ | (m : ResidueField R) ≠ 0 ∧ TorsionUnramified A V m}.Infinite := by
  first | exact @GlobalTheory.Proof.torsionUnramified_imp_tate_and_infinite | exact GlobalTheory.Proof.torsionUnramified_imp_tate_and_infinite | (intros; apply GlobalTheory.Proof.torsionUnramified_imp_tate_and_infinite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionUnramifiedOfHasGoodReductionStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionUnramified_of_hasGoodReduction_alt : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], HasGoodReduction R K A → ∀ m : ℕ, (m : ResidueField R) ≠ 0 → TorsionUnramified A V m := by
  first | exact @GlobalTheory.Published.AbVarRed.torsionUnramified_of_hasGoodReduction | exact GlobalTheory.Published.AbVarRed.torsionUnramified_of_hasGoodReduction | (intros; apply GlobalTheory.Published.AbVarRed.torsionUnramified_of_hasGoodReduction <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionPointLiesOverAfterFieldExtensionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusExtension_point_liesOver_after_field_extension : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif I D A G) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (g : GtPtF D.toPre (FractionRing R)) (w : Frm D.toPre (FractionRing R) 1 g.b) (x : TFK (R := R) (FractionRing R) ⟶ A.A) (fr : FrAt x), w.IsGen → fr.IsGen → GlobalTheory.Poinc.Tors.LiesOver U.toUnifPre w₀ g w x fr → ∀ (x' : TFK (R := R) F ⟶ A.A), x'.left = spMap (algebraMap (FractionRing R) F) ≫ x.left → ∃ (w' : Frm D.toPre F 1 (GlobalTheory.TorusExt.gtExt D.toPre (algebraMap (FractionRing R) F) (RingHom.comp_id _) g).b) (fr' : FrAt x'), w'.IsGen ∧ fr'.IsGen ∧ GlobalTheory.Poinc.Tors.LiesOver U.toUnifPre w₀ (GlobalTheory.TorusExt.gtExt D.toPre (algebraMap (FractionRing R) F) (RingHom.comp_id _) g) w' x' fr' := by
  first | exact @GlobalTheory.Poinc.Tors.LiesOverExt.liesOver_ext | exact GlobalTheory.Poinc.Tors.LiesOverExt.liesOver_ext | (intros; apply GlobalTheory.Poinc.Tors.LiesOverExt.liesOver_ext <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrdegFunctionFieldEq
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FunctionFieldTrdeg

theorem trdeg_functionField_eq : ∀ (F : Type) [Field F] (G : Scheme.{0}) [IsIntegral G] (s : G ⟶ Sp F) (d : ℕ), IsProjOver s → topologicalKrullDim G = d → ∀ (φ : F →+* G.functionField), G.fromSpecStalk (genericPoint G) ≫ s = spMap φ → (letI := φ.toAlgebra; Algebra.trdeg F G.functionField = d) := by
  intro F _ G _ s d hs hd φ hφ
  obtain ⟨N, i, hi, hcomp⟩ := hs
  haveI : IsProper (PSpace.str F N) := isProper_str F N
  haveI : LocallyOfFiniteType s := by rw [← hcomp]; infer_instance
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := G.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (genericPoint G)) isOpen_univ
  have hU : IsAffineOpen U := hU
  haveI : Nonempty U := ⟨⟨_, hxU⟩⟩
  let ψ := Spec.preimage (hU.fromSpec ≫ s)
  have hψ : Spec.map ψ = hU.fromSpec ≫ s := Spec.map_preimage _
  letI : Algebra F Γ(G, U) := ψ.hom.toAlgebra
  haveI hft : Algebra.FiniteType F Γ(G, U) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := ψ)).mp (hψ ▸ inferInstance)
  have hA : Algebra.trdeg F Γ(G, U) = d :=
    GlobalTheory.GenFinite.trdeg_affineOpen_eq F s hU ⟨_, hxU⟩ d hd
  letI : Algebra F G.functionField := φ.toAlgebra
  have key : CommRingCat.ofHom φ = ψ ≫ G.germToFunctionField U := by
    apply Spec.map_injective
    rw [Spec.map_comp]
    change spMap φ = _
    rw [← hφ, hψ, ← hU.fromSpecStalk_eq_fromSpecStalk hxU, IsAffineOpen.fromSpecStalk, Category.assoc]
  haveI : IsScalarTower F Γ(G, U) G.functionField :=
    IsScalarTower.of_algebraMap_eq' congr($(key).hom)
  haveI := functionField_isFractionRing_of_isAffineOpen G U hU
  haveI : FaithfulSMul F Γ(G, U) := (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap F Γ(G, U)).injective
  haveI : FaithfulSMul Γ(G, U) G.functionField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsFractionRing.injective Γ(G, U) G.functionField)
  haveI : Algebra.IsAlgebraic Γ(G, U) G.functionField := IsLocalization.isAlgebraic _ (nonZeroDivisors Γ(G, U))
  show Algebra.trdeg F G.functionField = d
  rw [GlobalTheory.trdeg_eq_of_isAlgebraic_top F Γ(G, U) G.functionField, hA]

end GlobalTheory.FunctionFieldTrdeg
end
end

