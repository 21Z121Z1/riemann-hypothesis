import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.XiMulNu
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import Formalism.PairingDivisors.StatementN

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
section
noncomputable section

open WittVector Ideal Matrix GlobalTheory.Sandwich

namespace GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

section Eigen

variable {O : Type} [CommRing O] (C : Type) [Field C] [Algebra O C]
  {Λ : Type} [CommRing Λ] {h : ℕ}

def eig (ρ : Λ → Matrix (Fin h) (Fin h) O) (σ : Λ →+* O) : Submodule C (Fin h → C) :=
  ⨅ a : Λ, Module.End.eigenspace (Matrix.toLin' ((ρ a).map (algebraMap O C)))
    (algebraMap O C (σ a))

def quotLattice (ρ : Λ → Matrix (Fin h) (Fin h) O) (τ : Λ →+* O) : Set (eig C ρ τ) :=
  {x | ∃ t : Fin h → O, (fun i => algebraMap O C (t i)) - (x : Fin h → C) ∈
    ⨆ σ : {σ : Λ →+* O // σ ≠ τ}, eig C ρ σ.1}

abbrev detLine (ρ : Λ → Matrix (Fin h) (Fin h) O) (τ : Λ →+* O) (N : ℕ) : Type :=
  ⋀[C]^N (eig C ρ τ)

def detLattice (ρ : Λ → Matrix (Fin h) (Fin h) O) (τ : Λ →+* O) (N : ℕ) :
    Submodule O (detLine C ρ τ N) :=
  Submodule.span O
    {w | ∃ x : Fin N → eig C ρ τ, (∀ i, x i ∈ quotLattice C ρ τ) ∧ w = exteriorPower.ιMulti C N x}

example (ρ : Λ → Matrix (Fin h) (Fin h) O) (τ : Λ →+* O) (N : ℕ) (a : O) (w : detLine C ρ τ N) :
    a • w = algebraMap O C a • w := (algebraMap_smul C a w).symm

end Eigen

section Datum

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O] (C : Type) [Field C] [Algebra O C]
  {ε : PreTilt O p} {h h' : ℕ} {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ]

def actT (D : Datum ε h Λ) (a : Λ) : Matrix (Fin h) (Fin h) O := (D.ρT a).map (padicToO p O)

def actH (D : Datum ε h Λ) (a : Λ) : Matrix (Fin h) (Fin h) O := (D.ρM a).map (fontaineTheta O p)

def redC {m n : ℕ} (X : Matrix (Fin m) (Fin n) (Ainf p O)) : (Fin n → C) →ₗ[C] (Fin m → C) :=
  Matrix.toLin' (X.map ((algebraMap O C).comp (fontaineTheta O p)))

def alC (D : Datum ε h Λ) : (Fin h → C) →ₗ[C] (Fin h → C) := redC C D.F

def bC (D : Datum ε h Λ) : (Fin h → C) →ₗ[C] (Fin h → C) := redC C D.G

def IsIota (D : Datum ε h Λ) (τ : Λ →+* O) (N : ℕ)
    (ι : detLine C (actT D) τ N →ₗ[C] detLine C (actH D) τ N) : Prop :=
  ∀ (x : Fin N → eig C (actT D) τ) (y : Fin N → eig C (actH D) τ),
    (∀ i : Fin N, (i : ℕ) < D.lieRank τ → (x i : Fin h → C) = bC C D (y i)) →
    (∀ i : Fin N, D.lieRank τ ≤ (i : ℕ) → (y i : Fin h → C) = alC C D (x i)) →
    ι (exteriorPower.ιMulti C N x) = exteriorPower.ιMulti C N y

def IsIsogeny (D : Datum ε h Λ) (D' : Datum ε h' Λ) (fT : Matrix (Fin h') (Fin h) ℤ_[p])
    (fM : Matrix (Fin h') (Fin h) (Ainf p O)) : Prop :=
  D'.F * fT.map (ofPadic p O) = fM * D.F ∧
  (∀ a, fT * D.ρT a = D'.ρT a * fT) ∧ (∀ a, fM * D.ρM a = D'.ρM a * fM) ∧
  ∃ (n : ℕ) (gT : Matrix (Fin h) (Fin h') ℤ_[p]) (gM : Matrix (Fin h) (Fin h') (Ainf p O)),
    D.F * gT.map (ofPadic p O) = gM * D'.F ∧
    gT * fT = ((p : ℤ_[p]) ^ n) • (1 : Matrix (Fin h) (Fin h) ℤ_[p]) ∧
    fT * gT = ((p : ℤ_[p]) ^ n) • (1 : Matrix (Fin h') (Fin h') ℤ_[p]) ∧
    gM * fM = ((p : Ainf p O) ^ n) • (1 : Matrix (Fin h) (Fin h) (Ainf p O)) ∧
    fM * gM = ((p : Ainf p O) ^ n) • (1 : Matrix (Fin h') (Fin h') (Ainf p O))

end Datum

def DetOver (p : ℕ) [Fact p.Prime] (C : Type) [Field C] (v : Valuation C NNReal)
    (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (span {(p : O)}) O] : Prop :=
  ∀ (ε : PreTilt O p), IsPrimitiveRoot (GlobalTheory.Sandwich.root ε).untilt p →
  ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ]
    [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ],
    (∃ c_vp : ℕ → ((Λ →+* O) → ℕ) → (Λ →+* O) → ℝ,
      ∀ (N h : ℕ), h = Module.finrank ℤ_[p] Λ * N → ∀ (D : Datum ε h Λ) (τ : Λ →+* O),
        (∃! ι, IsIota C D τ N ι) ∧
        ∀ ι, IsIota C D τ N ι → Function.Bijective ι ∧
          ∃ lam : C, v lam = v (p : C) ^ (c_vp N D.lieRank τ) ∧
            ι '' (detLattice C (actT D) τ N : Set (detLine C (actT D) τ N)) =
              (fun w => lam • w) '' (detLattice C (actH D) τ N : Set (detLine C (actH D) τ N))) ∧
    (∀ (N h : ℕ), h = Module.finrank ℤ_[p] Λ * N → ∀ (D D' : Datum ε h Λ)
      (fT : Matrix (Fin h) (Fin h) ℤ_[p]) (fM : Matrix (Fin h) (Fin h) (Ainf p O)),
      IsIsogeny D D' fT fM → ∀ (τ : Λ →+* O),
        ∃ (u : eig C (actT D) τ →ₗ[C] eig C (actT D') τ)
          (w : eig C (actH D) τ →ₗ[C] eig C (actH D') τ),
          (∀ x, (u x : Fin h → C) = redC C (fT.map (ofPadic p O)) x) ∧
          (∀ y, (w y : Fin h → C) = redC C fM y) ∧
          ∀ ι ι', IsIota C D τ N ι → IsIota C D' τ N ι' →
            ι' ∘ₗ exteriorPower.map N u = exteriorPower.map N w ∘ₗ ι)

def LemmaDet : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (span {(p : O)}) O], v.Integers O → DetOver p C v O

end GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SpecialFibreUnits
section
namespace GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi

def lbPow {Z : Scheme.{0}} (D : LB Z) (M : ℕ) : LB Z where
  ι := D.ι
  U := D.U
  g := fun i j => D.g i j ^ M

def constUnit {A : Type} [CommRing A] {T : Scheme.{0}} (p : T ⟶ Spec (.of A)) (a : Aˣ) :
    Γ(T, ⊤)ˣ :=
  Units.map p.appTop.hom.toMonoidHom
    (Units.map (Scheme.ΓSpecIso (.of A)).inv.hom.toMonoidHom a)

section Fibres

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {Z : Scheme.{0}} (f : Z ⟶ Spec (.of O))

def specialFibre : Scheme.{0} :=
  pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))

def specialι : specialFibre f ⟶ Z := pullback.fst _ _

def reducedSpecialFibre : Scheme.{0} := (specialFibre f).nilradical.subscheme

def reducedSpecialι : reducedSpecialFibre f ⟶ Z :=
  (specialFibre f).nilradical.subschemeι ≫ specialι f

def genericFibre : Scheme.{0} :=
  pullback f (Spec.map (CommRingCat.ofHom (algebraMap O (FractionRing O))))

def genericι : genericFibre f ⟶ Z := pullback.fst _ _

def genericStr : genericFibre f ⟶ Spec (.of (FractionRing O)) := pullback.snd _ _

def unifUnit (ϖ : O) (hϖ : Irreducible ϖ) : (FractionRing O)ˣ :=
  Units.mk0 (algebraMap O (FractionRing O) ϖ)
    ((map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).2 hϖ.ne_zero)

def Hyp (D : LB Z) : Prop :=
  IsIntegral Z ∧ (∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z)) ∧ IsProper f ∧ Flat f ∧
    ConnectedSpace (specialFibre f) ∧ D.IsLB ∧
    ∃ t : (D.pull (reducedSpecialι f)).Gen, t.IsGen

def PowEq (ϖ : O) (hϖ : Irreducible ϖ) (D : LB Z) (sig : (D.pull (genericι f)).Gen)
    (M : ℕ) (n : ℤ) (gen : (lbPow D M).Gen) : Prop :=
  ∀ j : PUnit → D.ι,
    sig.s j ^ M =
      res le_top (constUnit (genericStr f) (unifUnit ϖ hϖ)) ^ n *
        res (LB.wchart_le D (fun _ : PUnit => genericι f) j PUnit.unit)
          (pullU (genericι f) (D.U (j PUnit.unit)) (gen.s (j PUnit.unit)))

def IsCoord {R C : Type} [CommRing R] [Field C] [Algebra R C] (D : LB Z)
    (sig : (D.pull (genericι f)).Gen) (ybar : Spec (.of R) ⟶ Z)
    (y : Spec (.of C) ⟶ genericFibre f) (e : (D.pull ybar).Gen) (c : Cˣ) : Prop :=
  ∀ (j : PUnit → D.ι) (W : (Spec (.of C)).Opens)
    (h₁ : W ≤ y ⁻¹ᵁ (D.pull (genericι f)).U j)
    (h₂ : W ≤ Spec.map (CommRingCat.ofHom (algebraMap R C)) ⁻¹ᵁ (D.pull ybar).U j),
    res h₁ (pullU y _ (sig.s j)) =
      res le_top (constUnit (𝟙 (Spec (.of C))) c) *
        res h₂ (pullU (Spec.map (CommRingCat.ofHom (algebraMap R C))) _ (e.s j))

def ValConst (ϖ : O) (D : LB Z) (sig : (D.pull (genericι f)).Gen) (M : ℕ) (n : ℤ) : Prop :=
  ∀ (R C Γ₀ : Type) [CommRing R] [Field C] [Algebra R C] [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation C Γ₀), v.Integers R →
    ∀ (φ : O →+* R), Function.Injective φ → IsLocalHom φ →
    ∀ (ybar : Spec (.of R) ⟶ Z), ybar ≫ f = Spec.map (CommRingCat.ofHom φ) →
    ∀ (y : Spec (.of C) ⟶ genericFibre f),
      y ≫ genericι f = Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ ybar →
      (∃ (e : (D.pull ybar).Gen) (c : Cˣ), e.IsGen ∧ IsCoord f D sig ybar y e c) ∧
      ∀ (e : (D.pull ybar).Gen) (c : Cˣ), e.IsGen → IsCoord f D sig ybar y e c →
        v (c : C) ^ M = v (algebraMap R C (φ ϖ)) ^ n

end Fibres

def PropZ : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O) (hϖ : Irreducible ϖ)
    (Z : Scheme.{0}) (f : Z ⟶ Spec (.of O)) (D : LB Z), Hyp f D →
    ∀ sig : (D.pull (genericι f)).Gen, sig.IsGen →
      ∃ (M : ℕ) (n : ℤ), 1 ≤ M ∧
        (∃ gen : (lbPow D M).Gen, gen.IsGen ∧ PowEq f ϖ hϖ D sig M n gen) ∧
        ValConst f ϖ D sig M n

def PropZSlope : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O) (hϖ : Irreducible ϖ)
    (Z : Scheme.{0}) (f : Z ⟶ Spec (.of O)) (D : LB Z), Hyp f D →
    ∀ sig : (D.pull (genericι f)).Gen, sig.IsGen →
      ∃ ρ : ℚ, ∀ (M : ℕ) (n : ℤ), 1 ≤ M → (n : ℚ) = M * ρ →
        (∃ gen : (lbPow D M).Gen, gen.IsGen ∧ PowEq f ϖ hϖ D sig M n gen) ∧
        ValConst f ϖ D sig M n

theorem PropZSlope.propZ (h : PropZSlope) : PropZ := by
  intro O _ _ _ ϖ hϖ Z f D hD sig hs
  obtain ⟨ρ, hρ⟩ := h O ϖ hϖ Z f D hD sig hs
  refine ⟨ρ.den, ρ.num, ρ.den_pos, hρ _ _ ρ.den_pos ?_⟩
  rw [mul_comm]
  exact (Rat.mul_den_eq_num ρ).symm

def trivLB (Z : Scheme.{0}) : LB Z where
  ι := PUnit
  U := fun _ => ⊤
  g := fun _ _ => 1

theorem linComb_g_one {Y Z : Scheme.{0}} (D : LB Z) (h1 : ∀ a b, D.g a b = 1) {K : Type}
    [Fintype K] (φ : K → (Y ⟶ Z)) (ε : K → ℤ) (i j : K → D.ι) :
    (LB.LinComb D φ ε).g i j = 1 := by
  have key : ∀ (W : Y.Opens) (k : K) (hh : W ≤ φ k ⁻¹ᵁ (D.U (i k) ⊓ D.U (j k))),
      res hh (pullU (φ k) _ (D.g (i k) (j k))) ^ (ε k) = 1 := by
    intro W k hh
    rw [h1, map_one, map_one, one_zpow]
  exact @Finset.prod_eq_one K (Γ(Y, D.wchart φ i ⊓ D.wchart φ j)ˣ) _ _ _ (fun k _ => key _ k _)

theorem normal_stalk (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    (z : PrimeSpectrum A) : IsIntegrallyClosed ((Spec.structureSheaf A).presheaf.stalk z) :=
  isIntegrallyClosed_of_isLocalization _ z.asIdeal.primeCompl
    z.asIdeal.primeCompl_le_nonZeroDivisors

theorem hyp_spec (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] :
    Hyp (𝟙 (Spec (.of O))) (trivLB _) := by
  refine ⟨inferInstance, fun z => ?_, inferInstance, inferInstance, ?_, ⟨?_, ?_, ?_⟩,
    ⟨⟨fun _ => 1⟩, ?_⟩⟩
  · exact normal_stalk O z
  · have : ConnectedSpace (Spec (CommRingCat.of (IsLocalRing.ResidueField O))) := inferInstance
    let e := pullback.snd (𝟙 (Spec (.of O))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))
    exact (Scheme.homeoOfIso (asIso e)).symm.surjective.connectedSpace
      (Scheme.homeoOfIso (asIso e)).symm.continuous
  · simp [trivLB]
  · intro i; exact map_one _
  · intro i j k
    change res _ 1 * res _ 1 = res _ 1
    simp
  · intro i j
    refine (map_one _).trans (Eq.symm ?_)
    exact (congrArg₂ (· * ·) (linComb_g_one (trivLB _) (fun _ _ => rfl) _ _ i j) (map_one _)).trans (one_mul _)

end

end GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZetaValueIdeals
section
noncomputable section

open NumberField Module
open scoped nonZeroDivisors

namespace GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals

variable {F : Type} [Field F] [NumberField F]

abbrev IdealsIn (C : ClassGroup (𝓞 F)) : Type := {I : (Ideal (𝓞 F))⁰ // ClassGroup.mk0 I = C}

def IsClassZeta (C : ClassGroup (𝓞 F)) (Z : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ Z {1}ᶜ ∧ ∀ s : ℂ, 1 < s.re →
    HasSum (fun I : IdealsIn C => ((Ideal.absNorm (I.1 : Ideal (𝓞 F)) : ℕ) : ℂ) ^ (-s)) (Z s)

def IsZetaValues (k : ℕ) (z : ClassGroup (𝓞 F) → ℚ) : Prop :=
  ∀ C, ∃ Z : ℂ → ℂ, IsClassZeta C Z ∧ Z (1 - (k : ℂ)) = (z C : ℂ)

def denomExp (l : ℕ) (r : ℚ) : ℕ := (-padicValRat l r).toNat

def cE (z : ClassGroup (𝓞 F) → ℚ) (l : ℕ) : ℕ :=
  Finset.univ.sup fun C => denomExp l (z C / 2 ^ finrank ℚ F)

def mMin (l n : ℕ) : ℕ := sInf {m | ∃ a : ℕ, 2 ≤ a ∧ a.Coprime l ∧ m = padicValNat l (a ^ n - 1)}

def LocalBound (k : ℕ) (z : ClassGroup (𝓞 F) → ℚ) (l : ℕ) : Prop :=
  cE z l ≤ finrank ℚ F * padicValNat l 2 + mMin l (finrank ℚ F * k) ∧
  (l ≠ 2 → ¬ (l - 1) ∣ finrank ℚ F * k → mMin l (finrank ℚ F * k) = 0) ∧
  (l ≠ 2 → (l - 1) ∣ finrank ℚ F * k → mMin l (finrank ℚ F * k) = 1 + padicValNat l (finrank ℚ F * k)) ∧
  (l = 2 → mMin l (finrank ℚ F * k) = 2 + padicValNat 2 (finrank ℚ F * k))

def SumBound (k : ℕ) (z : ClassGroup (𝓞 F) → ℚ) : Prop :=
  (Function.support fun l : Nat.Primes => (cE z l : ℝ) * Real.log (l : ℕ)).Finite ∧
  ∑ᶠ l : Nat.Primes, (cE z l : ℝ) * Real.log (l : ℕ) ≤
    ((finrank ℚ F * k : ℕ) : ℝ) * Real.log (((finrank ℚ F * k : ℕ) : ℝ) + 1)

def DenomAt (F : Type) [Field F] [NumberField F] (k : ℕ) : Prop :=
  (∃ z : ClassGroup (𝓞 F) → ℚ, IsZetaValues k z) ∧
  ∀ z : ClassGroup (𝓞 F) → ℚ, IsZetaValues k z →
    (∀ l : ℕ, l.Prime → LocalBound k z l) ∧ (16 ≤ finrank ℚ F * k → SumBound k z)

def ZetaDenominators : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (s : ℕ), 1 ≤ s → DenomAt (maximalRealSubfield E) (2 * s)

def ZetaDenominatorsReal : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (s : ℕ), 1 ≤ s → DenomAt F (2 * s)

theorem ZetaDenominatorsReal.cm (h : ZetaDenominatorsReal) : ZetaDenominators :=
  fun E _ _ _ s hs => h (maximalRealSubfield E) s hs

theorem IsClassZeta.eqOn {C : ClassGroup (𝓞 F)} {Z Z' : ℂ → ℂ} (h : IsClassZeta C Z) (h' : IsClassZeta C Z') :
    Set.EqOn Z Z' {1}ᶜ := by
  have ho : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
  have hc : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num) 1).isPreconnected
  refine (h.1.analyticOnNhd ho).eqOn_of_preconnected_of_eventuallyEq (h'.1.analyticOnNhd ho) hc (z₀ := 2) (by norm_num) ?_
  have ho' : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [ho'.mem_nhds (show (2 : ℂ) ∈ {s : ℂ | 1 < s.re} by simp)] with s hs
  exact (h.2 s hs).unique (h'.2 s hs)

theorem IsZetaValues.unique {k : ℕ} (hk : 1 ≤ k) {z z' : ClassGroup (𝓞 F) → ℚ} (h : IsZetaValues k z)
    (h' : IsZetaValues k z') : z = z' := by
  funext C
  obtain ⟨Z, hZ, e⟩ := h C
  obtain ⟨Z', hZ', e'⟩ := h' C
  have hne : (1 - (k : ℂ)) ∈ ({1}ᶜ : Set ℂ) := by
    have : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    simpa using this
  have := hZ.eqOn hZ' hne
  rw [e, e'] at this
  exact_mod_cast this

theorem mMin_mem {l : ℕ} (hl : 1 ≤ l) (n : ℕ) : ∃ a : ℕ, 2 ≤ a ∧ a.Coprime l ∧ mMin l n = padicValNat l (a ^ n - 1) :=
  Nat.sInf_mem (s := {m | ∃ a : ℕ, 2 ≤ a ∧ a.Coprime l ∧ m = padicValNat l (a ^ n - 1)})
    ⟨_, l + 1, by omega, by simp, rfl⟩

theorem LocalBound.mMin_eq {k : ℕ} {z : ClassGroup (𝓞 F) → ℚ} {l : ℕ} (h : LocalBound k z l) :
    mMin l (finrank ℚ F * k) = Formalism.PairingDivisionLocalBalance.mE l (finrank ℚ F * k) := by
  unfold Formalism.PairingDivisionLocalBalance.mE
  split_ifs with h1 h2
  · exact h.2.2.2 h1
  · exact h.2.2.1 h1 h2
  · exact h.2.1 h1 h2

example : denomExp 2 (-1 / 24) = 3 ∧ denomExp 3 (-1 / 24) = 1 ∧ denomExp 2 0 = 0 := by
  have h2 : padicValNat 2 24 = 3 := by
    rw [show 24 = 2 ^ 3 * 3 by norm_num, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by norm_num)]
  have h3 : padicValNat 3 24 = 1 := by
    rw [show 24 = 3 ^ 1 * 8 by norm_num, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by norm_num)]
  have hn : (-1 / 24 : ℚ).num = -1 := by norm_num
  have hd : (-1 / 24 : ℚ).den = 24 := by norm_num
  refine ⟨?_, ?_, by simp [denomExp]⟩
  · simp only [denomExp, padicValRat, hn, hd, h2]; simp [padicValInt]
  · simp only [denomExp, padicValRat, hn, hd, h3]; simp [padicValInt]

theorem pir_rat : IsPrincipalIdealRing (𝓞 ℚ) :=
  IsPrincipalIdealRing.of_surjective Rat.ringOfIntegersEquiv.symm.toRingHom Rat.ringOfIntegersEquiv.symm.surjective

theorem absNorm_span_rat (n : ℕ) : Ideal.absNorm (Ideal.span {(n : 𝓞 ℚ)}) = n := by
  rw [Ideal.absNorm_span_singleton, show (n : 𝓞 ℚ) = algebraMap ℤ (𝓞 ℚ) (n : ℤ) by simp, Algebra.norm_algebraMap,
    RingOfIntegers.rank]
  simp

theorem exists_span_rat (I : Ideal (𝓞 ℚ)) : ∃ n : ℕ, I = Ideal.span {(n : 𝓞 ℚ)} := by
  haveI := pir_rat
  obtain ⟨a, rfl⟩ : ∃ a, I = Ideal.span {a} := ⟨_, (IsPrincipalIdealRing.principal I).span_singleton_generator.symm⟩
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, a = (m : 𝓞 ℚ) := ⟨Rat.ringOfIntegersEquiv a, by
    apply Rat.ringOfIntegersEquiv.injective; simp⟩
  refine ⟨m.natAbs, ?_⟩
  rcases Int.natAbs_eq m with h | h
  · rw [h]; simp
  · conv_lhs => rw [h]
    rw [Int.cast_neg, Ideal.span_singleton_neg, Int.cast_natCast]

theorem isClassZeta_rat (C : ClassGroup (𝓞 ℚ)) : IsClassZeta C riemannZeta := by
  refine ⟨fun s hs => (differentiableAt_riemannZeta hs).differentiableWithinAt, fun s hs => ?_⟩
  have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
  haveI := pir_rat
  haveI : Subsingleton (ClassGroup (𝓞 ℚ)) :=
    (@Fintype.card_le_one_iff_subsingleton _ instFintypeClassGroupOfIsPrincipalIdealRing).1
      (card_classGroup_eq_one (R := 𝓞 ℚ)).le
  let g : IdealsIn C → ℕ := fun I => Ideal.absNorm (I.1 : Ideal (𝓞 ℚ))
  have hg : Function.Injective g := fun I J h => by
    obtain ⟨n, hn⟩ := exists_span_rat (I.1 : Ideal (𝓞 ℚ))
    obtain ⟨m, hm⟩ := exists_span_rat (J.1 : Ideal (𝓞 ℚ))
    simp only [g, hn, hm, absNorm_span_rat] at h
    exact Subtype.ext (Subtype.ext (by rw [hn, hm, h]))
  have hr : ∀ n ∉ Set.range g, (n : ℂ) ^ (-s) = 0 := fun n hn => by
    by_cases h0 : n = 0
    · simp [h0, hs0]
    · refine (hn ⟨⟨⟨Ideal.span {(n : 𝓞 ℚ)}, mem_nonZeroDivisors_of_ne_zero ?_⟩, Subsingleton.elim _ _⟩,
        absNorm_span_rat n⟩).elim
      simpa using h0
  refine (hg.hasSum_iff (f := fun n : ℕ => (n : ℂ) ^ (-s)) hr).2 ?_
  rw [zeta_eq_tsum_one_div_nat_cpow hs]
  simpa only [Complex.cpow_neg, one_div] using (Complex.summable_one_div_nat_cpow.2 hs).hasSum

example : IsZetaValues (F := ℚ) 2 (fun _ => -1 / 12) := fun C => ⟨_, isClassZeta_rat C, by
  have h := riemannZeta_neg_nat_eq_bernoulli 1
  have hb : bernoulli 2 = 1 / 6 := by rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_two]
  rw [show (1 + 1 : ℕ) = 2 from rfl, hb] at h
  rw [show (1 - ((2 : ℕ) : ℂ)) = -((1 : ℕ) : ℂ) by norm_num, h]
  norm_num⟩

end GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals
end
end

