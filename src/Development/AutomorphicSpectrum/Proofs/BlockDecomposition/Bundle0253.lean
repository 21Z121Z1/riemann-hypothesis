import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConnectionOnDividedPowerBasis
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0749
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0249
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ContinuousCompOfIsOpenKer
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0250
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0205
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0251
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0204
import Development.WeilBound.CoreStatements.PadicHodgeComparison.KatzMessingTheorem.BaseChange
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NegOnePowBoundaryTermsCancel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConnectionOnDividedPowerBasisStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.connection_on_divided_power_basis : ∀ {B M : Type} [CommRing B] [AddCommGroup M] [Module B M] (e : Module.Basis ℕ B M) (I : ℕ → Ideal B) (p : ℕ) (q : B) (ν : ℕ → B) (D : M →ₗ[B] M), p ≠ 0 → IsNilpotent (p : B) → IsNilpotent (q - 1) → (∀ a c, I a * I c ≤ I (a + c)) → (∀ a c, a ≤ c → I c ≤ I a) → ν 1 = 1 → (∀ m, ν (m + 1) ∈ I m) → (∀ m, 2 ≤ m → IsNilpotent (ν m)) → (∃ N, ∀ m, N ≤ m → ν m = 0) → (∀ k, D (e k) = (∑ i ∈ Finset.range k, q ^ i) • e k + ∑ m ∈ Finset.range k, (ν (m + 1) * q ^ (k - (m + 1))) • e (k - (m + 1))) → (∀ z, D z = 0 → ∃ c : B, z = c • e 0) ∧ ∀ (r : ℕ) (z : M), (∀ k, e.repr z k ∈ I (r - k)) → ∃ y, (∀ k, e.repr y k ∈ I (r + 1 - k)) ∧ D y = z := by
  first | exact @GlobalTheory.CompanionTheory.QDerivative.ker_and_surjective | exact GlobalTheory.CompanionTheory.QDerivative.ker_and_surjective | (intros; apply GlobalTheory.CompanionTheory.QDerivative.ker_and_surjective <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOfIsAutFormTotallyComplex
section
open NumberField

namespace GlobalTheory.CompanionTheory.ContAutForm

open GlobalTheory.CuspRep

theorem continuous_of_isAutForm_totallyComplex (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ)
    (φ : Sm E N) (h : IsAutForm φ) : Continuous φ.1 :=
  h.continuous

end GlobalTheory.CompanionTheory.ContAutForm
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CyclotomicDividedPowerExpansionStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomic_divided_power_expansion : ∀ {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (p : ℕ), p.Prime → IsNilpotent (p : B) → ∀ x : B, (∑ i ∈ Finset.range p, x ^ i) ∈ J → IsNilpotent (x ^ p - 1) ∧ ∃ ν : ℕ → B, ν 1 = 1 ∧ (∀ m, δ.dpow (m + 1) (x ^ p - 1) = (x ^ p - 1) * ν (m + 1)) ∧ (∀ m, ν (m + 1) ∈ fil δ m) ∧ (∀ m, 2 ≤ m → IsNilpotent (ν m)) ∧ ∃ M, ∀ m, M ≤ m → ν m = 0 := by
  first | exact @GlobalTheory.CompanionTheory.QPd.dpow_pow_sub_one | exact GlobalTheory.CompanionTheory.QPd.dpow_pow_sub_one | (intros; apply GlobalTheory.CompanionTheory.QPd.dpow_pow_sub_one <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DecompositionGroupFrobeniusFactorStatement
section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.decomposition_group_frobenius_factor : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ∀ φ : Dec (F := F) A, IsFrob (F := F) A (normV v) (φ : G F Ω) → ∀ N : ℕ, 0 < N → ∀ g : Dec (F := F) A, ∃ a < N, ∃ t i : Dec (F := F) A, (i : G F Ω) ∈ Ine (F := F) A ∧ g = φ ^ a * t ^ N * i := by
  first | exact @GlobalTheory.CompanionTheory.TameDecomp.exists_frob_pow_mul_pow_mul_inertia | exact GlobalTheory.CompanionTheory.TameDecomp.exists_frob_pow_mul_pow_mul_inertia | (intros; apply GlobalTheory.CompanionTheory.TameDecomp.exists_frob_pow_mul_pow_mul_inertia <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerPolynomialFiltrationStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divided_power_polynomial_filtration : ∀ {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (Q : PDPoly B) (η : DividedPowers (Q.ext J)), Q.IsStd δ η → (∀ a c, fil δ a * fil δ c ≤ fil δ (a + c)) ∧ (∀ a c, a ≤ c → fil δ c ≤ fil δ a) ∧ fil δ 0 = ⊤ ∧ ∀ (r : ℕ) (z : Q.P), z ∈ fil η r ↔ ∀ k, Q.e.repr z k ∈ fil δ (r - k) := by
  first | exact @GlobalTheory.CompanionTheory.PDFil.fil_pdPoly | exact GlobalTheory.CompanionTheory.PDFil.fil_pdPoly | (intros; apply GlobalTheory.CompanionTheory.PDFil.fil_pdPoly <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleAnnihilatorEqSelf
section
namespace GlobalTheory.CompanionTheory.FiniteDuality

private theorem card_dual_zmod_le_card' (n : ℕ) [NeZero n] (M : Type) [AddCommGroup M]
    [Module (ZMod n) M] [Finite M] :
    Nat.card (M →ₗ[ZMod n] ZMod n) ≤ Nat.card M := by
  classical
  have := Fintype.ofFinite M
  let φ : (M →ₗ[ZMod n] ZMod n) → AddChar M ℂ := fun f =>
    Circle.coeHom.compAddChar ((ZMod.toCircle (N := n)).compAddMonoidHom f.toAddMonoidHom)
  have hφ : Function.Injective φ := by
    intro f g h
    ext x
    have hx := congrArg (fun ψ : AddChar M ℂ => ψ x) h
    have hx' : Circle.coeHom (ZMod.toCircle (f x)) = Circle.coeHom (ZMod.toCircle (g x)) := hx
    exact ZMod.injective_toCircle (Circle.ext hx')
  calc Nat.card (M →ₗ[ZMod n] ZMod n) ≤ Nat.card (AddChar M ℂ) :=
        Nat.card_le_card_of_injective φ hφ
    _ = Nat.card M := by
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, AddChar.card_eq]

private theorem card_le_of_injective_pairing_zmod (n : ℕ) [NeZero n] (Z W : Type) [AddCommGroup Z]
    [Module (ZMod n) Z] [AddCommGroup W] [Module (ZMod n) W] [Finite W]
    (g : Z →ₗ[ZMod n] W →ₗ[ZMod n] ZMod n) (hg : Function.Injective g) :
    Nat.card Z ≤ Nat.card W := by
  have : Finite (W →ₗ[ZMod n] ZMod n) :=
    Finite.of_injective (fun f : W →ₗ[ZMod n] ZMod n => (f : W → ZMod n)) DFunLike.coe_injective
  exact (Nat.card_le_card_of_injective g hg).trans (card_dual_zmod_le_card' n W)

theorem double_annihilator (n : ℕ) [NeZero n] (X Y : Type) [AddCommGroup X] [Module (ZMod n) X]
    [Finite X] [AddCommGroup Y] [Module (ZMod n) Y] [Finite Y]
    (B : Y →ₗ[ZMod n] X →ₗ[ZMod n] ZMod n) (hB : Function.Injective B)
    (hB' : Function.Injective B.flip) (U : Submodule (ZMod n) X) :
    (⨅ y ∈ (⨅ x ∈ U, LinearMap.ker (B.flip x)), LinearMap.ker (B y)) = U := by
  set A : Submodule (ZMod n) Y := ⨅ x ∈ U, LinearMap.ker (B.flip x) with hAdef
  set W : Submodule (ZMod n) X := ⨅ y ∈ A, LinearMap.ker (B y) with hWdef
  have memA : ∀ y, y ∈ A ↔ ∀ x ∈ U, B y x = 0 := by
    intro y
    simp [hAdef, Submodule.mem_iInf]
  have memW : ∀ x, x ∈ W ↔ ∀ y ∈ A, B y x = 0 := by
    intro x
    simp only [hWdef, Submodule.mem_iInf, LinearMap.mem_ker]
  have hUW : U ≤ W := by
    intro x hx
    rw [memW]
    intro y hy
    exact (memA y).1 hy x hx
  let f1 : Y →ₗ[ZMod n] U →ₗ[ZMod n] ZMod n := B.compl₂ U.subtype
  have hA1 : A ≤ LinearMap.ker f1 := by
    intro y hy
    rw [LinearMap.mem_ker]
    ext u
    simp [f1, (memA y).1 hy u u.2]
  have hA1' : LinearMap.ker f1 ≤ A := by
    intro y hy
    rw [LinearMap.mem_ker] at hy
    rw [memA]
    intro x hx
    have := LinearMap.congr_fun hy ⟨x, hx⟩
    simpa [f1] using this
  let P1 : (Y ⧸ A) →ₗ[ZMod n] U →ₗ[ZMod n] ZMod n := A.liftQ f1 hA1
  have hP1 : Function.Injective P1 :=
    LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot A f1 hA1 hA1')
  let f2 : Y →ₗ[ZMod n] W →ₗ[ZMod n] ZMod n := B.compl₂ W.subtype
  have hA2 : A ≤ LinearMap.ker f2 := by
    intro y hy
    rw [LinearMap.mem_ker]
    ext w
    simp [f2, (memW w).1 w.2 y hy]
  let P2 : (Y ⧸ A) →ₗ[ZMod n] W →ₗ[ZMod n] ZMod n := A.liftQ f2 hA2
  have hP2 : Function.Injective P2.flip := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    have hz : B.flip (w : X) = 0 := by
      ext y
      have := LinearMap.congr_fun hw (Submodule.Quotient.mk y)
      simpa [P2, f2] using this
    have : (w : X) = 0 := hB' (by rw [hz, map_zero])
    exact Subtype.ext this
  have : Finite (Y ⧸ A) := Finite.of_surjective _ (Submodule.mkQ_surjective A)
  have c1 : Nat.card (Y ⧸ A) ≤ Nat.card U := card_le_of_injective_pairing_zmod n _ _ P1 hP1
  have c2 : Nat.card W ≤ Nat.card (Y ⧸ A) := card_le_of_injective_pairing_zmod n _ _ P2.flip hP2
  have hle : Nat.card (W.toAddSubgroup) ≤ Nat.card (U.toAddSubgroup) := c2.trans c1
  exact (Submodule.toAddSubgroup_injective
    (AddSubgroup.eq_of_le_of_card_ge (show U.toAddSubgroup ≤ W.toAddSubgroup from hUW) hle)).symm

end GlobalTheory.CompanionTheory.FiniteDuality
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EnergyIdentityOfLengthFunctionStatement
section
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.energy_identity_of_length_function : ∀ {n : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (ℓ : Mat n → ℝ), ContDiffOn ℝ ∞ ℓ (GLs n) → (∀ R : ℝ, IsCompact {y : G n | ℓ y.val ≤ R}) → ∀ (C₁ : ℝ), 0 ≤ C₁ → (∀ y ∈ GLs n, ∀ p : Ix n, |fderiv ℝ ℓ y (y * hm p)| ≤ C₁) → (∀ Ψ : Mat n → ℝ, ContDiffOn ℝ ∞ Ψ (GLs n) → (∃ R : ℝ, ∀ y ∈ GLs n, R < ℓ y → Ψ y = 0) → ∀ X : Mat n, ∫ y : G n, Rr X Ψ y.val ∂μ = 0) → ∀ (χ : ℝ → ℝ), ContDiff ℝ ∞ χ → (∀ x, deriv χ x ≤ 0) → (∀ x, 0 ≤ χ x) → (∀ x, 1 ≤ x → χ x = 0) → ∀ (u : ℝ → Mat n → W), Sm u → ∀ (A : W →L[ℝ] W), (∀ s, ∀ y ∈ GLs n, dt (dt u) s y = (1 / 4 : ℝ) • ∑ p : Ix n, Rr (hm p) (Rt (hm p) u s) y + A (u s y)) → ∀ (C : ℝ), C₁ * (1 + Fintype.card (Ix n)) ≤ C → ∀ (r : ℝ), (∀ x, x ≤ 0 → χ x = 1) → (∀ y ∈ GLs n, ℓ y < r + 1 → u 0 y = 0) → (∀ y ∈ GLs n, dt u 0 y = 0) → ∀ t : ℝ, 0 ≤ t → ∀ y ∈ GLs n, ℓ y + C * t ≤ r → u t y = 0 := by
  first | exact @GlobalTheory.CompanionTheory.WaveSpd.Vanish.energy_vanish | exact GlobalTheory.CompanionTheory.WaveSpd.Vanish.energy_vanish | (intros; apply GlobalTheory.CompanionTheory.WaveSpd.Vanish.energy_vanish <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EtaleLiftingOfNilIdealStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_lifting_of_nil_ideal : ∀ {B : Type} [CommRing B] (J : Ideal B), (∀ x ∈ J, IsNilpotent x) → EtLift J := by
  first | exact @GlobalTheory.CompanionTheory.EtNil.etLift_of_nil | exact GlobalTheory.CompanionTheory.EtNil.etLift_of_nil | (intros; apply GlobalTheory.CompanionTheory.EtNil.etLift_of_nil <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLiftToThickening
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.ThickHom

theorem isNilpotent_of_mem {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {p : ℕ} (h0 : p ≠ 0)
    (hp : IsNilpotent (p : B)) {x : B} (hx : x ∈ J) : IsNilpotent x := by
  obtain ⟨N, hN⟩ := hp
  have key : ∀ M : ℕ, p ^ M ∣ (M * p).factorial := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [Nat.succ_mul, pow_succ]
      exact (mul_dvd_mul ih (Nat.dvd_factorial (Nat.pos_of_ne_zero h0) le_rfl)).trans
        (Nat.factorial_mul_factorial_dvd_factorial_add _ _)
  obtain ⟨c, hc⟩ := key N
  refine ⟨N * p, ?_⟩
  rw [← δ.factorial_mul_dpow_eq_pow hx, hc]
  push_cast
  rw [hN]
  simp

variable {O : Type} [CommRing O] {F : Fn O} {d : ℕ} (s : F.Small d) {b : Base} (ht : b.t = 1)
  {κ : O →+* b.R ⧸ b.I}

theorem comp_eq (T : Thick (F.cr b ht κ)) {g : s.R →+* T.B ⧸ T.J}
    (hg : F.Pt.map (CommRingCat.ofHom g) s.y₀ = T.y.1.2) (o : O) (x : b.R)
    (hx : Ideal.Quotient.mk b.I x = κ o) : g (s.a o) = Ideal.Quotient.mk T.J (T.i x) := by
  have h1 : F.Ov T.y.1.2 (g.comp s.a) := by
    have := F.ov_map (CommRingCat.ofHom g) s.ov
    rw [hg] at this
    exact this
  have h2 := F.ov_uniq h1 T.y.2
  have h3 := congrArg (fun f : O →+* _ => f o) h2
  have h4 : T.y.1.1 (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk T.J (T.i x) := T.w x
  rw [← h4, hx]
  exact h3

variable (𝓛 : Lift s.a (fun k => (s.T k : s.R)) b.R b.I κ) (δ : DividedPowers (b.I.map 𝓛.i))
  (hδ : IsDPMorphism b.γ δ 𝓛.i) (hp : b.p ≠ 0) (hn : IsNilpotent (b.p : b.R))

theorem s_eq_one (T : Thick (F.cr b ht κ)) : T.s = 1 := by
  have h : (1 : T.B) = T.s * T.i b.t := (Finset.prod_of_isEmpty (ι := Empty) _).symm.trans T.hs
  rw [ht, map_one, mul_one] at h
  exact Units.ext h.symm

def homOf (T : Thick (F.cr b ht κ)) {g : s.R →+* T.B ⧸ T.J}
    (hg : F.Pt.map (CommRingCat.ofHom g) s.y₀ = T.y.1.2) (f : 𝓛.D →+* T.B) (hf : f.comp 𝓛.i = T.i)
    (hfg : ∀ r z, Ideal.Quotient.mk _ z = 𝓛.j r → Ideal.Quotient.mk T.J (f z) = g r) :
    liftObj s ht 𝓛 δ hδ hp hn ⟶ T :=
  have hdp : IsDPMorphism δ T.δ f :=
    (GlobalTheory.CompanionTheory.PDMap.extended_dividedPowers b.γ 𝓛.i δ hδ).2 T.δ f (by rw [hf]; exact T.compat)
  have hle : b.I.map 𝓛.i ≤ T.J.comap f := Ideal.map_le_iff_le_comap.1 hdp.1
  { φ := f
    u := fun j => j.elim
    comm := fun r => congrArg (fun e : b.R →+* T.B => e r) hf
    dp := hdp
    hle := hle
    pt := by
      have hq : (Ideal.quotientMap T.J f hle).comp 𝓛.j = g := by
        ext r
        obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (𝓛.j r)
        rw [RingHom.comp_apply, ← hz]
        exact hfg r z hz
      refine Subtype.ext (Prod.ext ?_ ?_)
      · refine Ideal.Quotient.ringHom_ext (RingHom.ext fun r => ?_)
        have h1 : T.y.1.1 (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk T.J (T.i r) := T.w r
        refine Eq.trans ?_ h1.symm
        change Ideal.Quotient.mk T.J (f (𝓛.i r)) = _
        rw [← hf]
        rfl
      · refine Eq.trans ?_ hg
        rw [← hq]
        exact (congrFun (congrArg (fun t => (ConcreteCategory.hom t : _ → _))
          (F.Pt.map_comp (CommRingCat.ofHom 𝓛.j) (CommRingCat.ofHom (Ideal.quotientMap T.J f hle)))) s.y₀).symm
    hx := fun j => j.elim
    hs := by
      have : IsEmpty (F.cr b ht κ).ι := inferInstanceAs (IsEmpty Empty)
      have h1 : (liftObj s ht 𝓛 δ hδ hp hn).s = 1 := rfl
      rw [s_eq_one ht T, h1, map_one, Finset.prod_of_isEmpty, one_mul]
    hv := fun j => j.elim }

theorem main (T : Thick (F.cr b ht κ)) :
    ∃ g : s.R →+* T.B ⧸ T.J,
      (∀ (c : liftObj s ht 𝓛 δ hδ hp hn ⟶ T) (r : s.R) (z : 𝓛.D),
        Ideal.Quotient.mk _ z = 𝓛.j r → Ideal.Quotient.mk T.J (c.φ z) = g r) ∧
      F.Pt.map (CommRingCat.ofHom g) s.y₀ = T.y.1.2 ∧
      ∀ u : Fin d → T.B, (∀ k, Ideal.Quotient.mk T.J (u k) = g (s.T k)) →
        ∃! c : liftObj s ht 𝓛 δ hδ hp hn ⟶ T, ∀ k, c.φ (𝓛.t k) = u k := by
  obtain ⟨g, hg, hgu⟩ := s.univ (CommRingCat.of (T.B ⧸ T.J)) T.y.1.2 (T.y.1.1.comp κ) T.y.2
  have hc : ∀ (c : liftObj s ht 𝓛 δ hδ hp hn ⟶ T) (r : s.R) (z : 𝓛.D),
      Ideal.Quotient.mk _ z = 𝓛.j r → Ideal.Quotient.mk T.J (c.φ z) = g r := by
    intro c r z hz
    have hpt : F.Pt.map (CommRingCat.ofHom (Ideal.quotientMap T.J c.φ c.hle))
        (F.Pt.map (CommRingCat.ofHom 𝓛.j) s.y₀) = T.y.1.2 := congrArg (fun y => y.1.2) c.pt
    have e := congrFun (congrArg (fun t => (ConcreteCategory.hom t : _ → _))
      (F.Pt.map_comp (CommRingCat.ofHom 𝓛.j) (CommRingCat.ofHom (Ideal.quotientMap T.J c.φ c.hle)))) s.y₀
    have hq : (Ideal.quotientMap T.J c.φ c.hle).comp 𝓛.j = g := hgu _ (e.trans hpt)
    have := congrArg (fun e : s.R →+* T.B ⧸ T.J => e r) hq
    refine Eq.trans ?_ this
    exact congrArg (Ideal.quotientMap T.J c.φ c.hle) hz
  refine ⟨g, hc, hg, fun u hu => ?_⟩
  have hJ : EtLift T.J := GlobalTheory.CompanionTheory.EtNil.etLift_of_nil T.J fun x hx =>
    isNilpotent_of_mem T.δ hp (T.adm.1 hp) hx
  obtain ⟨f, ⟨hf1, hf2, hf3⟩, hfu⟩ := GlobalTheory.CompanionTheory.EtaleLift.lift_hom_existsUnique s.a (fun k => (s.T k : s.R)) b.I κ 𝓛
    T.J hJ T.i g u (fun x hx => T.i_mem hx) (comp_eq s ht T hg) hu
  refine ⟨homOf s ht 𝓛 δ hδ hp hn T hg f hf1 hf3, hf2, fun c hck => ?_⟩
  have hcf : c.φ = f := hfu c.φ ⟨RingHom.ext c.comm, hck, hc c⟩
  exact Thick.Hom.ext hcf (funext fun j => j.elim)

end GlobalTheory.CompanionTheory.ThickHom
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrobeniusPowerFixesRootUniqueStatement
section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_power_fixes_root_unique : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ∀ φ : Dec (F := F) A, IsFrob (F := F) A (normV v) (φ : G F Ω) → ∀ N : ℕ, 0 < N → ∀ ξ : Ω, IsPrimitiveRoot ξ (normV v ^ N - 1) → ∀ (a : ℕ) (t i : Dec (F := F) A), a < N → (i : G F Ω) ∈ Ine (F := F) A → ((φ ^ a * t ^ N * i : Dec (F := F) A) : G F Ω) ξ = ξ → a = 0 := by
  first | exact @GlobalTheory.CompanionTheory.TameAction.eq_zero_of_fixes_primitiveRoot | exact GlobalTheory.CompanionTheory.TameAction.eq_zero_of_fixes_primitiveRoot | (intros; apply GlobalTheory.CompanionTheory.TameAction.eq_zero_of_fixes_primitiveRoot <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandOperatorPairingAdjointStatement
section
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gelfand_operator_pairing_adjoint : ∀ (n : ℕ) (w : List (Bool × ℕ)), ∃ (N : ℕ) (c : Fin N → ℂ) (w₁ : Fin N → List (Bool × ℕ)), (∀ χ : Inf n, IsHerm χ → conj (zVal w χ) = ∑ i, c i * zVal (w₁ i) χ) ∧ (LgFacts → RCalc → ∀ [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (f h : Mat n → V), ContDiffOn ℝ ∞ f (GLs n) → ContDiffOn ℝ ∞ h (GLs n) → Cpt f → Cpt h → ∫ y : G n, ⟪zOp w f y.val, h y.val⟫_ℂ ∂μ = ∑ i, c i * ∫ y : G n, ⟪f y.val, zOp (w₁ i) h y.val⟫_ℂ ∂μ) := by
  first | exact @GlobalTheory.CompanionTheory.WaveMult.WordAdj.word_adjoint | exact GlobalTheory.CompanionTheory.WaveMult.WordAdj.word_adjoint | (intros; apply GlobalTheory.CompanionTheory.WaveMult.WordAdj.word_adjoint <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsFirstChernClassOnThickenings
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.B DividedPowers CompanionTheory.KM.G4

namespace GlobalTheory.CompanionTheory.KMGys

variable {k : Type} [Field k] (b : Base) (ht : b.t = 1) (κ : k →+* b.R ⧸ b.I)

def covFun (Y : SmV k) {ι : Type} (U : ι → Y.X.Opens) : b.Fun where
  ι := Empty
  A := ι
  Pt := (schFn Y.q).ptK κ
  str y := y.1.1
  str_map _ _ := rfl
  In i _ y := ⊤ ≤ y.1.2 ⁻¹ᵁ U i
  in_map := @fun _ _ _ φ y h => le_preimage_map φ y.1.2 h
  f _ i := i.elim
  f_map i := i.elim
  g _ _ i := i.elim
  g_map i := i.elim
  f_eq i := i.elim
  g_self i := i.elim
  g_comp i := i.elim
  prod_f {_ _ y} _ := by simp [ht]
  prod_g _ _ := by simp

def toCov (Y : SmV k) {ι : Type} (U : ι → Y.X.Opens) :
    GlobalTheory.LogCris.Mor ((schFn Y.q).cr b ht κ) (covFun b ht κ Y U) (RingHom.id b.R) where
  hp := rfl
  hI := ⟨by rw [Ideal.map_id], fun _ _ => rfl⟩
  a := 1
  ha := by simp
  m := 1
  ht := by simp [ht]
  e i := i.elim
  he j := j.elim
  c _ := ()
  pt := 𝟙 _
  str y r := rfl
  inc _ := trivial
  w _ i := i.elim
  w_map i := i.elim
  hf i := i.elim
  hg i := i.elim
  hw _ := Finset.prod_of_isEmpty (ι := Empty) _

open ReciprocityTheory.ChartRestriction.G.Semi in
open Classical in

def lbOn (Y : SmV k) (L : LB Y.X) (hL : L.IsLB) : GlobalTheory.LogCris.LB (covFun b ht κ Y L.U) where
  g i j B y := if h : ⊤ ≤ y.1.2 ⁻¹ᵁ (L.U i ⊓ L.U j) then
      Units.map (GlobalTheory.Cris.evalAt (B := B) y.1.2 (L.U i ⊓ L.U j) h : Γ(Y.X, L.U i ⊓ L.U j) →* B) (L.g i j) else 1
  g_map := @fun i j B B' φ y hi hj => by
    have h := le_preimage_inf y.1.2 hi hj
    rw [dif_pos h, dif_pos (show ⊤ ≤ (((covFun b ht κ Y L.U).Pt.map φ y)).1.2 ⁻¹ᵁ (L.U i ⊓ L.U j) from le_preimage_map φ y.1.2 h)]
    ext
    exact evalAt_map φ y.1.2 h _ _
  g_self := @fun i B y hi => by
    have h := le_preimage_inf y.1.2 hi hi
    rw [dif_pos h]
    ext
    have e := congrArg (fun u : Γ(Y.X, L.U i)ˣ => (u : Γ(Y.X, L.U i))) (hL.g_self i)
    simp only [Units.coe_map, MonoidHom.coe_coe, Units.val_one]
    rw [← evalAt_res y.1.2 (le_inf le_rfl le_rfl) h hi]
    exact (congrArg _ e).trans (map_one _)
  g_comp := @fun i j l B y hi hj hl => by
    have h12 := le_preimage_inf y.1.2 hi hj
    have h23 := le_preimage_inf y.1.2 hj hl
    have h13 := le_preimage_inf y.1.2 hi hl
    have h123 := le_preimage_inf y.1.2 h12 hl
    rw [dif_pos h12, dif_pos h23, dif_pos h13]
    ext
    have e := congrArg (fun u : Γ(Y.X, L.U i ⊓ L.U j ⊓ L.U l)ˣ => (u : Γ(Y.X, L.U i ⊓ L.U j ⊓ L.U l))) (hL.cocycle i j l)
    simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe] at e ⊢
    rw [← evalAt_res y.1.2 inf_le_left h12 h123, ← evalAt_res y.1.2 (le_inf (inf_le_left.trans inf_le_right) inf_le_right) h23 h123,
      ← evalAt_res y.1.2 (le_inf (inf_le_left.trans inf_le_left) inf_le_right) h13 h123, ← map_mul]
    exact congrArg _ e

def IsFirstChernClassOnThickenings (Y : SmV k) (L : ReciprocityTheory.ChartRestriction.G.Semi.LB Y.X) (hL : L.IsLB) (z : Hc b ht κ Y 2) : Prop :=
  GlobalTheory.LogCris.IsFirstChernClassOfLineBundle (lbOn b ht κ Y L hL) ((toCov b ht κ Y L.U).pull 2 z)

def powH {Y : SmV k} (x : Hc b ht κ Y 2) (j : ℕ) : Hc b ht κ Y (2 * j) :=
  Nat.rec (motive := fun j => Hc b ht κ Y (2 * j)) (one b ht κ Y) (fun _ y => cup b ht κ y x) j

end GlobalTheory.CompanionTheory.KMGys
end
end

