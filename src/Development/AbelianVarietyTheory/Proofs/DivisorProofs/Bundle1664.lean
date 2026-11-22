import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0173
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0130
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1642
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1621
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1636
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1613
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1623
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1129
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1622
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HarishChandraModulesIndefiniteUnitaryGroup
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.Bundle0001
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Smooth
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.MeasurePreservingMulRight
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsIrrKSubOfIsKTypeOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1637
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperSmoothConnGroupOfManyTorsionCharP
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SerreTateProperness

theorem main : ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (G : Over (Sp k)) [GrpObj G], GlobalTheory.SS.SmConn G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ m : ℕ, (m : k) ≠ 0 → ∀ s : Finset (𝟙_ (Over (Sp k)) ⟶ G), (∀ x ∈ s, x ^ m = 1) → m ^ (2 * g) < m * s.card → IsProper G.hom := by
  intro k _ _ p _ _ G _ hG g hg m hm s hs hcard
  classical
  obtain ⟨N, _, ν, hN, hνmon, hνci, hpdiv, hlift, -, hdim⟩ :=
    GlobalTheory.DivisiblePart.exists_divisiblePart k p G hG
  obtain ⟨g', hg', hiso⟩ := hdim g hg
  obtain ⟨X, _, _, _, B, _, i, q, hq, hB, hdimB⟩ :=
    GlobalTheory.SS.DivSemi.exists_torus_abelian_quotient k p N hN hpdiv
  obtain ⟨a, ha, hga⟩ := hdimB g' hg'

  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (by simp)
  have hcop : m.Coprime p := by
    have hnd : ¬ p ∣ m := fun h => hm ((CharP.cast_eq_zero_iff k p m).mpr h)
    exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (Fact.out)).mpr hnd)

  have hmono : Mono ν.left := inferInstance
  have hinj : ∀ y y' : 𝟙_ (Over (Sp k)) ⟶ N, y ≫ ν = y' ≫ ν → y = y' := by
    intro y y' h
    ext1
    exact (cancel_mono ν.left).mp (by simpa using congrArg CommaMorphism.left h)

  have hlift' : ∀ x ∈ s, ∃ y : 𝟙_ (Over (Sp k)) ⟶ N, y ≫ ν = x ∧ y ^ m = 1 := by
    intro x hx
    obtain ⟨y, hy⟩ := hlift x m hcop hm0 (hs x hx)
    refine ⟨y, hy, hinj _ _ ?_⟩
    rw [MonObj.pow_comp, hy, hs x hx, MonObj.one_comp]
  choose! f hf1 hf2 using hlift'
  have hfinj : Set.InjOn f s := by
    intro x hx x' hx' h
    rw [← hf1 x hx, ← hf1 x' hx', h]
  have hcardN : (s.image f).card ≤ m ^ (Module.finrank ℤ X + 2 * a) := by
    refine GlobalTheory.T.card_torsion_torusExtension_abelianVariety_le k N hN.1 X B i q hq hB a ha m hm (s.image f) ?_
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact hf2 x hx
  rw [Finset.card_image_of_injOn hfinj] at hcardN

  have hpt : Nonempty (𝟙_ (Over (Sp k))).left := by
    change Nonempty (Sp k)
    first
    | infer_instance
    | exact ⟨IsLocalRing.closedPoint k⟩
  have hne : Nonempty N.left := ⟨(1 : 𝟙_ (Over (Sp k)) ⟶ N).left hpt.some⟩
  have hgle : g' ≤ g := GlobalTheory.T.relDim_le_of_smooth_of_isClosedImmersion k N G ν hνci hne g g' hg hg'

  have hm1 : 1 < m := by
    rcases Nat.lt_or_ge 1 m with h | h
    · exact h
    · exfalso
      have : m = 1 := by omega
      subst this
      simp at hcard hcardN
      omega
  have hlt : m ^ (2 * g) < m ^ (Module.finrank ℤ X + 2 * a + 1) := by
    calc m ^ (2 * g) < m * s.card := hcard
      _ ≤ m * m ^ (Module.finrank ℤ X + 2 * a) := Nat.mul_le_mul_left m hcardN
      _ = m ^ (Module.finrank ℤ X + 2 * a + 1) := by ring
  have hexp := (Nat.pow_lt_pow_iff_right (by omega)).mp hlt
  have ht : Module.finrank ℤ X = 0 := by omega
  have hgg : g ≤ g' := by omega
  haveI hP : IsProper N.hom := GlobalTheory.T.isProper_of_isQuot_abelian_of_finrank_eq_zero k N X B i q hq hB ht
  haveI : IsIso ν.left := by
    haveI := hiso hgg
    exact Functor.map_isIso (Over.forget (Sp k)) ν
  have hw : G.hom = inv ν.left ≫ N.hom := by
    rw [← Over.w ν]
    simp
  rw [hw]
  infer_instance

end GlobalTheory.SerreTateProperness
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaFunctionDoublingThetaTensorCM
section
open scoped TensorProduct Matrix ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.DblTargetThetaF

open GlobalTheory.DblTargetDelta GlobalTheory.WeilSchrodinger.DblTargetF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def topH (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (nS nT : ℕ) :
    WOF F E nS (nT + nT) →+ WOF F E nS nT where
  toFun := topR
  map_zero' := rfl
  map_add' _ _ := rfl

def sndH (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (nS nT : ℕ) :
    WOF F E nS (nT + nT) →+ WOF F E nS nT where
  toFun x := -botR x
  map_zero' := by ext; simp [botR]
  map_add' x y := by ext; simp [botR]; ring

theorem continuous_topH (nS nT : ℕ) : Continuous (topH F E nS nT) :=
  continuous_matrix fun i j => continuous_id.matrix_elem _ j

theorem continuous_sndH (nS nT : ℕ) : Continuous (sndH F E nS nT) := by
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  exact (continuous_matrix fun i j => continuous_id.matrix_elem (finSumFinEquiv (Sum.inr i)) j).neg

theorem map_topH {R : Type} [CommRing R] (φ : AEF F E →+* R) {nS nT : ℕ} {u : WOF F E nS (nT + nT)}
    (h : u.map φ = 0) : (topH F E nS nT u).map φ = 0 :=
  Matrix.ext fun i j => congrFun (congrFun h (finSumFinEquiv (Sum.inl i))) j

theorem map_sndH {R : Type} [CommRing R] (φ : AEF F E →+* R) {nS nT : ℕ} {u : WOF F E nS (nT + nT)}
    (h : u.map φ = 0) : (sndH F E nS nT u).map φ = 0 :=
  Matrix.ext fun i j => by
    have e : φ (u (finSumFinEquiv (Sum.inr i)) j) = 0 := congrFun (congrFun h (finSumFinEquiv (Sum.inr i))) j
    change φ (-(u (finSumFinEquiv (Sum.inr i)) j)) = 0
    rw [map_neg, e, neg_zero]

theorem hOF_neg (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
    (x y : WOF F E nS nT) : hOF σ JS JT (-x) (-y) = hOF σ JS JT x y := by
  simp [hOF]

theorem hOF_dbl (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
    (x y : WOF F E nS (nT + nT)) :
    hOF σ JS (dblG JT) x y = hOF σ JS JT (topH F E nS nT x) (topH F E nS nT y) -
      hOF σ JS JT (sndH F E nS nT x) (sndH F E nS nT y) := by
  change _ = hOF σ JS JT (topR x) (topR y) - hOF σ JS JT (-botR x) (-botR y)
  rw [hOF_neg]
  unfold hOF
  have hs : ∀ g : Fin (nT + nT) → AEF F E, ∑ a, g a =
      ∑ a, g (finSumFinEquiv (Sum.inl a)) + ∑ a, g (finSumFinEquiv (Sum.inr a)) := fun g => by
    rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [hs]
  simp [-finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right, dblG, GlobalTheory.WeilM.dbl, topH, topR, botR,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, sub_eq_add_neg]

theorem symplOHF_dbl (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
    (ξ₀ : E) (x y : WOF F E nS (nT + nT)) :
    symplOHF σ JS (dblG JT) ξ₀ x y = symplOHF σ JS JT ξ₀ (topH F E nS nT x) (topH F E nS nT y) -
      symplOHF σ JS JT ξ₀ (sndH F E nS nT x) (sndH F E nS nT y) := by
  unfold symplOHF symplOF
  rw [hOF_dbl, mul_sub, map_sub, mul_sub]

theorem conj_char {G : Type} [AddCommGroup G] (ψ : AddChar G ℂ) (h : ∀ x, ‖ψ x‖ = 1) (x : G) :
    conj (ψ x) = ψ (-x) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (h x)]

theorem deltaT_eq {nS nT : ℕ} (f₁ f₂ : WOF F E nS nT → ℂ) :
    deltaT f₁ f₂ = fun w => f₁ (topH F E nS nT w) * conj (f₂ (sndH F E nS nT w)) := rfl

theorem topH_ratWF {nS nT : ℕ} (γ : Matrix (Fin (nT + nT)) (Fin nS) E) :
    topH F E nS nT (ratWF γ) = ratWF (γ.submatrix (finSumFinEquiv ∘ Sum.inl) id) := rfl

theorem sndH_ratWF {nS nT : ℕ} (γ : Matrix (Fin (nT + nT)) (Fin nS) E) :
    sndH F E nS nT (ratWF γ) = ratWF (-γ.submatrix (finSumFinEquiv ∘ Sum.inr) id) := by
  ext i j
  change -((incAF F E) (γ _ j)) = (incAF F E) (-(γ _ j))
  rw [map_neg]

theorem isThetaFunOF_deltaT (σ : E →ₐ[F] E) {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E}
    {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E} {ψ : AddChar (AF F) ℂ} (hn : ∀ x, ‖ψ x‖ = 1)
    {f₁ f₂ : WOF F E nS nT → ℂ} (h₁ : IsThetaFunOF σ JS JT ξ₀ ψ f₁) (h₂ : IsThetaFunOF σ JS JT ξ₀ ψ f₂) :
    IsThetaFunOF σ JS (dblG JT) ξ₀ ψ (deltaT f₁ f₂) := by
  rw [deltaT_eq]
  refine ⟨fun γ w => ?_, ?_, ?_, fun k L hL h0 w => ?_⟩
  · rw [map_add, map_add, symplOHF_dbl, topH_ratWF, sndH_ratWF, h₁.quasi, h₂.quasi, map_mul, conj_char ψ hn,
      neg_neg, neg_sub, sub_eq_add_neg, AddChar.map_add_eq_mul]
    ring
  · obtain ⟨U₁, hU₁, k₁⟩ := h₁.level
    obtain ⟨U₂, hU₂, k₂⟩ := h₂.level
    refine ⟨U₁.comap (topH F E nS nT) ⊓ U₂.comap (sndH F E nS nT),
      (hU₁.preimage (continuous_topH nS nT)).inter (hU₂.preimage (continuous_sndH nS nT)), fun u hu h0 => ?_⟩
    funext w
    have e₁ := congrFun (k₁ _ hu.1 (map_topH _ h0)) (topH F E nS nT w)
    have e₂ := congrFun (k₂ _ hu.2 (map_sndH _ h0)) (sndH F E nS nT w)
    simp only [heisOF] at e₁ e₂ ⊢
    rw [← e₁, ← e₂, symplOHF_dbl, sub_eq_add_neg, AddChar.map_add_eq_mul, map_add, map_add, map_mul, conj_char ψ hn]
    ring
  · exact (h₁.cont.comp (continuous_topH nS nT)).mul
      (Complex.continuous_conj.comp (h₂.cont.comp (continuous_sndH nS nT)))
  · simp only [map_add]
    exact (h₁.smooth k ((topH F E nS nT).comp L) ((continuous_topH nS nT).comp hL) (fun t => map_topH _ (h0 t)) _).mul
      (Complex.conjCLE.contDiff.comp (h₂.smooth k ((sndH F E nS nT).comp L) ((continuous_sndH nS nT).comp hL)
        (fun t => map_sndH _ (h0 t)) _))

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ f₁ f₂ : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ,
        Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₁ → Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₂ →
        Formalism.IndefR.DatumF.IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ
          (GlobalTheory.DblTargetDelta.deltaT f₁ f₂) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT _ _ ξ₀ _ _ f₁ f₂ h₁ h₂
  exact isThetaFunOF_deltaT σ (GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood F E σ B hB).1.2.1 h₁ h₂

end GlobalTheory.DblTargetThetaF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JointlyEpiSectionsGenerate
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LineQuot

open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)
open GlobalTheory.LB (resG_resG)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LineQuot

theorem bijective_of_basis_unit {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (B' : Module.Basis (Fin 1) R M) (B : Module.Basis (Fin 1) R N)
    (f : M →ₗ[R] N) (u : Rˣ) (h : f (B' 0) = (u : R) • B 0) : Function.Bijective f := by
  have hsum (P : Type) [AddCommGroup P] [Module R P] (C : Module.Basis (Fin 1) R P) (m : P) :
      m = C.repr m 0 • C 0 := by
    conv_lhs => rw [← C.sum_repr m]
    simp
  constructor
  · refine (injective_iff_map_eq_zero f).2 fun m hm => ?_
    rw [hsum M B' m, map_smul, h, smul_smul] at hm
    have h1 : B'.repr m 0 * u = 0 := by
      simpa using congrArg (fun n => B.repr n 0) hm
    have h2 : B'.repr m 0 = 0 := (Units.mul_left_eq_zero u).1 h1
    rw [hsum M B' m, h2, zero_smul]
  · intro n
    refine ⟨(B.repr n 0 * ((u⁻¹ : Rˣ) : R)) • B' 0, ?_⟩
    rw [map_smul, h, smul_smul, mul_assoc, Units.inv_mul, mul_one, ← hsum N B n]

theorem gen_of_jointEpi : ∀ (T : Scheme.{0}) (L Q : T.Modules) (N : ℕ) (s : Fin (N + 1) → (L ⟶ Q)),
    IsVB L 1 → IsVB Q 1 → JointEpi s → Gen s := by
  intro T L Q N s hL hQ hs x
  have := Abelian.hasFiniteBiproducts (C := T.Modules)
  let p : (⨁ fun _ : Fin (N + 1) => L) ⟶ Q := biproduct.desc s
  have hp : Epi p := (Preadditive.epi_iff_cancel_zero p).2 fun Z a ha => hs Z a fun j => by
    have := congrArg (biproduct.ι (fun _ : Fin (N + 1) => L) j ≫ ·) ha
    simpa [p] using this
  obtain ⟨U₁, e', -, hx₁, -, he'⟩ := hL.exists_affine (V := ⊤) (x := x) trivial
  obtain ⟨U₂, e, -, hx₂, h₂, he⟩ := hQ.exists_affine hx₁
  obtain ⟨W, hW, hxW, t, ht⟩ := exists_app_eq_of_epi p (e 0) hx₂
  have hW' : W ≤ U₁ := hW.trans h₂
  let u : Fin (N + 1) → Γ(L, W) := fun j => (biproduct.π (fun _ : Fin (N + 1) => L) j).app W t
  have hsum : ∑ j, (s j).app W (u j) = resM Q hW (e 0) := by
    rw [← ht]
    have hpd : p = ∑ j, biproduct.π (fun _ : Fin (N + 1) => L) j ≫ s j := biproduct.desc_eq
    let ev : ((⨁ fun _ : Fin (N + 1) => L) ⟶ Q) →+ Γ(Q, W) :=
      AddMonoidHom.mk' (fun φ => φ.app W t) fun _ _ => rfl
    have := map_sum ev (fun j => biproduct.π (fun _ : Fin (N + 1) => L) j ≫ s j) Finset.univ
    rw [← hpd] at this
    exact this.symm
  let B' := he'.basis hW'
  let B := he.basis hW
  let a : Fin (N + 1) → Γ(T, W) := fun j => B'.repr (u j) 0
  let c : Fin (N + 1) → Γ(T, W) := fun j => B.repr ((s j).app W (resM L hW' (e' 0))) 0
  have hone (P : Type) [AddCommGroup P] [Module Γ(T, W) P] (C : Module.Basis (Fin 1) Γ(T, W) P)
      (m : P) : m = C.repr m 0 • C 0 := by
    conv_lhs => rw [← C.sum_repr m]
    simp
  have hu (j : Fin (N + 1)) : u j = a j • resM L hW' (e' 0) := by
    rw [← IsFrame.basis_apply he' hW']; exact hone _ B' (u j)
  have hc (j : Fin (N + 1)) : (s j).app W (resM L hW' (e' 0)) = c j • resM Q hW (e 0) := by
    rw [← IsFrame.basis_apply he hW]; exact hone _ B _
  have hac : ∑ j, a j * c j = 1 := by
    have h1 : (∑ j, a j * c j) • B 0 = (1 : Γ(T, W)) • B 0 := by
      rw [one_smul, Finset.sum_smul]
      calc ∑ j, (a j * c j) • B 0 = ∑ j, (s j).app W (u j) :=
            Finset.sum_congr rfl fun j _ => by
              rw [hu, Scheme.Modules.Hom.app_smul, hc, smul_smul, IsFrame.basis_apply]
        _ = B 0 := by rw [hsum, IsFrame.basis_apply]
    simpa using congrArg (fun n => B.repr n 0) h1
  obtain ⟨j, hj⟩ : ∃ j, x ∈ T.basicOpen (c j) := by
    by_contra hno
    push_neg at hno
    have hmem (j : Fin (N + 1)) : T.presheaf.germ W x hxW (c j) ∈ IsLocalRing.maximalIdeal _ :=
      fun hu' => hno j ((T.mem_basicOpen (c j) x hxW).2 hu')
    have : T.presheaf.germ W x hxW (∑ j, a j * c j) ∈ IsLocalRing.maximalIdeal _ := by
      rw [map_sum]
      exact Ideal.sum_mem _ fun j _ => by
        rw [map_mul]; exact Ideal.mul_mem_left _ _ (hmem j)
    rw [hac, map_one] at this
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 this)
  refine ⟨j, T.basicOpen (c j), hj, fun V hV => ?_⟩
  have hVW : V ≤ W := hV.trans (T.basicOpen_le (c j))
  have hunit : IsUnit (resG T hVW (c j)) := by
    have h0 := (T.toRingedSpace.isUnit_res_basicOpen (c j)).map (resG T hV)
    have : resG T hV (resG T (T.basicOpen_le (c j)) (c j)) = resG T hVW (c j) := resG_resG _ _ _
    rw [← this]; exact h0
  have key : GlobalTheory.QCoh.appLinear (s j) V ((he'.basis (hVW.trans hW')) 0) =
      ((hunit.unit : Γ(T, V)ˣ) : Γ(T, V)) • (he.basis (hVW.trans hW)) 0 := by
    rw [IsUnit.unit_spec, GlobalTheory.QCoh.appLinear_apply, IsFrame.basis_apply, IsFrame.basis_apply,
      ← resM_resM hW' hVW, app_resM, hc, resM_smul, resM_resM]
  have hb := bijective_of_basis_unit (R := Γ(T, V)) _ _ _ _ key
  exact hb

end GlobalTheory.LineQuot

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFiniteModuleIrreducibleOfIrreducibleUnitaryRep
section
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.KFinIrr

theorem smE_eq {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hK : IsKMod ε σ D E) (v : D) (hv : (v : H) ∈ ReciprocityTheory.ChartRestriction.DS.smD ε σ)
    (a b : Fin n) :
    ((ReciprocityTheory.ChartRestriction.DS.smE ε σ a b ⟨v, hv⟩ : ReciprocityTheory.ChartRestriction.DS.smD ε σ) : H) = ((E a b v : D) : H) := by
  have hσ' : ReciprocityTheory.ChartRestriction.DS.IsURepOn (ReciprocityTheory.ChartRestriction.DS.UJset ε) σ := hσ
  have key : ∀ X, ReciprocityTheory.ChartRestriction.DS.inG ε X →
      ReciprocityTheory.ChartRestriction.DS.dS σ X (v : H) = ∑ c, ∑ d, X c d • ((E c d v : D) : H) := fun X hX =>
    (hK.real X hX v).deriv
  rw [ReciprocityTheory.ChartRestriction.DS.smE_apply hσ']
  change ReciprocityTheory.ChartRestriction.DS.dS σ _ (v : H) + Complex.I • ReciprocityTheory.ChartRestriction.DS.dS σ _ (v : H) = _
  rw [key _ (ReciprocityTheory.ChartRestriction.DS.SmDerA.inG_cpart1 ε _), key _ (ReciprocityTheory.ChartRestriction.DS.SmDerA.inG_cpart2 ε _)]
  have hz : ∀ c d, ReciprocityTheory.ChartRestriction.DS.S7.cpart1 ε (Matrix.single a b 1) c d +
      Complex.I * ReciprocityTheory.ChartRestriction.DS.S7.cpart2 ε (Matrix.single a b 1) c d = Matrix.single a b (1 : ℂ) c d := by
    intro c d
    have := congrFun (congrFun (ReciprocityTheory.ChartRestriction.DS.SmDerA.cpart_decomp ε (Matrix.single a b 1)) c) d
    rw [this]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  calc _ = ∑ c, ∑ d, (ReciprocityTheory.ChartRestriction.DS.S7.cpart1 ε (Matrix.single a b 1) c d +
        Complex.I * ReciprocityTheory.ChartRestriction.DS.S7.cpart2 ε (Matrix.single a b 1) c d) • ((E c d v : D) : H) := by
          simp only [Finset.smul_sum, add_smul, Finset.sum_add_distrib, smul_smul]
    _ = ∑ c, ∑ d, Matrix.single a b (1 : ℂ) c d • ((E c d v : D) : H) := by simp only [hz]
    _ = ((E a b v : D) : H) := by
          simp [Matrix.single_apply, ite_smul, ite_and]

theorem kMod_irred : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D), CompleteSpace H → IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → IsKMod ε σ D E → ∀ N : Submodule ℂ D, (∀ a b, ∀ x ∈ N, E a b x ∈ N) → N = ⊥ ∨ N = ⊤ := by
  intro n ε H _ _ σ D E hc hσ hirr hK N hN
  haveI := hc
  have hle : D ≤ ReciprocityTheory.ChartRestriction.DS.smD ε σ := fun v hv =>
    (CompanionTheory.D.gk.HC.K_finite_smooth_vectors n ε H σ hσ hirr).1 v ((hK.mem v).1 hv)
  let ι : D →ₗ[ℂ] ReciprocityTheory.ChartRestriction.DS.smD ε σ := Submodule.inclusion hle
  have hι : Function.Injective ι := Submodule.inclusion_injective hle
  have hcomm : ∀ a b (x : D), ReciprocityTheory.ChartRestriction.DS.smE ε σ a b (ι x) = ι (E a b x) := fun a b x =>
    Subtype.ext (smE_eq hσ hK x (hle x.2) a b)
  let N' : Submodule ℂ (ReciprocityTheory.ChartRestriction.DS.smD ε σ) := N.map ι
  have hN'K : (N' : Set (ReciprocityTheory.ChartRestriction.DS.smD ε σ)) ⊆ CompanionTheory.D.gk.HC.KF ε σ := by
    rintro _ ⟨x, -, rfl⟩
    exact (hK.mem x).1 x.2
  have hN'st : ∀ a b, ∀ v ∈ N', ReciprocityTheory.ChartRestriction.DS.smE ε σ a b v ∈ N' := by
    rintro a b _ ⟨x, hx, rfl⟩
    rw [hcomm]
    exact ⟨_, hN a b x hx, rfl⟩
  rcases GlobalTheory.HcPort.uIrr n ε H σ hσ hirr N' hN'K hN'st with h | h
  · left
    rw [eq_bot_iff]
    intro x hx
    have hx' : ι x ∈ N' := ⟨x, hx, rfl⟩
    rw [h, Submodule.mem_bot] at hx'
    rw [Submodule.mem_bot]
    exact hι (by rw [hx', map_zero])
  · right
    rw [eq_top_iff]
    intro x _
    have hx' : ι x ∈ (N' : Set (ReciprocityTheory.ChartRestriction.DS.smD ε σ)) := by
      rw [h]
      exact (hK.mem x).1 x.2
    obtain ⟨y, hy, hyx⟩ := hx'
    rw [hι hyx] at hy
    exact hy

end GlobalTheory.KFinIrr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFiniteVectorsIrreducibleUnitaryUnitaryGroupPQ
section
open Matrix

noncomputable section

namespace GlobalTheory.KFinLinkPort

open GlobalTheory.KFinVec
open ReciprocityTheory.ChartRestriction.DS (smD smE smE_apply isDerivedOn_smE dS dS_eq_actM actM)
open CompanionTheory.D.gk.HC (KF)

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem dRep_eq_dS (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (X : Matrix (Fin n) (Fin n) ℂ) (w : H) :
    Formalism.L2.Theta.dRep σ X w = dS σ X w := by
  unfold Formalism.L2.Theta.dRep dS
  congr 1

theorem isAdmissible_of [CompleteSpace H] (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ)
    (hirr : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ) : IsAdmissible ε σ := by
  rintro S ⟨hf, -, hK, -⟩
  have hfin : FiniteDimensional ℂ (Formalism.MainNotions.BridgeCPX.eqImg (fun k : Formalism.REAL.KG ε => σ (Formalism.REAL.toMK k)) S) :=
    (CompanionTheory.HCMult.harish_chandra_multiplicity : Formalism.MainNotions.BridgeCPX.HCMult) n ε H σ hσ hirr S hf hK
  have hle : kIsotypic ε σ S ≤ Formalism.MainNotions.BridgeCPX.eqImg (fun k : Formalism.REAL.KG ε => σ (Formalism.REAL.toMK k)) S :=
    iSup_le fun T => le_sSup ⟨T.1, fun a v w h => T.2 _ a.2 v w h, rfl⟩
  exact Submodule.finiteDimensional_of_le hle

theorem isLieStable_of [CompleteSpace H] (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ)
    (hirr : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ) : IsLieStable ε σ (kFinSub ε σ) := by
  intro X hX v hv
  obtain ⟨h1, h2⟩ := CompanionTheory.D.gk.HC.K_finite_smooth_vectors n ε H σ hσ hirr
  have hvS : v ∈ smD ε σ := h1 v hv
  rw [dRep_eq_dS]
  have e := dS_eq_actM (isDerivedOn_smE hσ) hX ⟨v, hvS⟩
  simp only [] at e
  rw [e]
  simp only [actM, LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul]
  exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ =>
    Submodule.smul_mem _ _ (h2 a b ⟨v, hvS⟩ hv)

theorem lieIrr_of [CompleteSpace H] (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ)
    (hirr : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ) (S : Submodule ℂ H) (hS : S ≤ kFinSub ε σ)
    (hL : IsLieStable ε σ S) : S = ⊥ ∨ S = kFinSub ε σ := by
  obtain ⟨h1, -⟩ := CompanionTheory.D.gk.HC.K_finite_smooth_vectors n ε H σ hσ hirr
  let N : Submodule ℂ (smD ε σ) := S.comap (smD ε σ).subtype
  have hNK : (N : Set (smD ε σ)) ⊆ KF ε σ := fun v hv => hS hv
  have hst : ∀ a b, ∀ v ∈ N, smE ε σ a b v ∈ N := by
    intro a b v hv
    show ((smE ε σ a b v : smD ε σ) : H) ∈ S
    rw [smE_apply hσ]
    have e1 := hL _ (ReciprocityTheory.ChartRestriction.DS.SmDerA.inG_cpart1 ε (Matrix.single a b 1)) (v : H) hv
    have e2 := hL _ (ReciprocityTheory.ChartRestriction.DS.SmDerA.inG_cpart2 ε (Matrix.single a b 1)) (v : H) hv
    rw [dRep_eq_dS] at e1 e2
    exact S.add_mem e1 (S.smul_mem _ e2)
  rcases GlobalTheory.HcPort.uIrr n ε H σ hσ hirr N hNK hst with h | h
  · left
    refine eq_bot_iff.2 fun v hv => ?_
    have hvN : (⟨v, h1 v (hS hv)⟩ : smD ε σ) ∈ N := hv
    rw [h] at hvN
    have := (Submodule.mem_bot ℂ).1 hvN
    exact (Submodule.mem_bot ℂ).2 (congrArg Subtype.val this)
  · right
    refine le_antisymm hS fun v hv => ?_
    have hvK : (⟨v, h1 v hv⟩ : smD ε σ) ∈ KF ε σ := hv
    rw [← h] at hvK
    exact hvK

end GlobalTheory.KFinLinkPort

namespace GlobalTheory.KFinLinkPort

theorem kFiniteVectors_irreducibleUnitary_unitaryGroupPQ : GlobalTheory.Published.KFiniteVectorsUnitary := by
  intro n ε H _ _ _ _ σ hσ hirr
  exact ⟨GlobalTheory.KFinLinkPort.isAdmissible_of hσ hirr,
    GlobalTheory.HcPort.kFiniteVectors_analytic_indefiniteUnitary n ε H σ hσ hirr,
    GlobalTheory.T.dense_kFinite_vectors_unitaryGroupRep n ε H σ hσ,
    GlobalTheory.KFinLinkPort.isLieStable_of hσ hirr,
    fun S hS hL => GlobalTheory.KFinLinkPort.lieIrr_of hσ hirr S hS hL⟩

end GlobalTheory.KFinLinkPort

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevMoveCommLevelMapOfTrivialModStatement
section
open CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LevPull
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levMove_comp_r_eq_of_trivial_mod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), 1 ≤ Dw.p + Dw.q → d.IsLev → d.l₂.A = 1 → (∀ h : KA l ≤ KA d.l₂, d.r ≫ Xo.s = d.Xo₂.s ≫ ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (IntermediateField.inclusion h).toRingHom) → ∀ (ρ₂ : d.Xo₂.X ⟶ d.Xo₂.X) (ν₂ : SABMap d.Xo₂.univ.t d.Xo₂.univ.t ρ₂) (g gA : Dw.La →ₗ[𝓞 E] Dw.La), IsIso ρ₂ → IsLevMove ρ₂ ν₂ g gA → (∀ a, g a - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) → ρ₂ ≫ d.r = d.r ∧ ν₂.φ ≫ d.m.φ = d.m.φ := by
  first | exact @GlobalTheory.levMove_comm_levelMap_of_trivial_mod | exact GlobalTheory.levMove_comm_levelMap_of_trivial_mod | (intros; apply GlobalTheory.levMove_comm_levelMap_of_trivial_mod <;> assumption)
end

