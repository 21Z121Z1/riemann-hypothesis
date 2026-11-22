import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0011

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FracFieldPositiveRowsOmega
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

abbrev PolyRingPositiveRowsBase : Type := MvPolynomial {v : TVar d.D d.N // v.1 ≠ 0} K

abbrev PolyRingPositiveRowsOmega (c : ι) : Type := MvPolynomial ({i : Fin (d.D + 1) // i ≠ 0} × Fin d.N) (Ω c)

abbrev FracFieldPositiveRowsBase : Type := FractionRing d.PolyRingPositiveRowsBase

abbrev FracFieldPositiveRowsOmega (c : ι) : Type := FractionRing (d.PolyRingPositiveRowsOmega c)

noncomputable def eLX4 : KTf K d.D d.N ≃+* FractionRing (MvPolynomial (Fin (d.N + 1)) d.FracFieldPositiveRowsBase) :=
  letI := (FractionFieldVariableLift.toFracY d.PolyRingPositiveRowsBase (Fin (d.N + 1))).toAlgebra
  haveI := FractionFieldVariableLift.isFractionRing_toFracY (A := d.PolyRingPositiveRowsBase) (σ := Fin (d.N + 1))
  IsFractionRing.ringEquivOfRingEquiv (FractionFieldVariableLift.hL K d.D d.N)

noncomputable def eEX4 (c : ι) : OmS (Ω c) d.D d.N ≃+* FractionRing (MvPolynomial (Fin (d.N + 1)) (d.FracFieldPositiveRowsOmega c)) :=
  letI := (FractionFieldVariableLift.toFracY (d.PolyRingPositiveRowsOmega c) (Fin (d.N + 1))).toAlgebra
  haveI := FractionFieldVariableLift.isFractionRing_toFracY (A := d.PolyRingPositiveRowsOmega c) (σ := Fin (d.N + 1))
  IsFractionRing.ringEquivOfRingEquiv (FractionFieldVariableLift.hE (Ω c) d.D d.N (d.jc c))

theorem eLX4_algebraMap (P : KTp K d.D d.N) :
    d.eLX4 (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) P) =
      FractionFieldVariableLift.toFracY d.PolyRingPositiveRowsBase (Fin (d.N + 1)) (FractionFieldVariableLift.hL K d.D d.N P) := by
  letI := (FractionFieldVariableLift.toFracY d.PolyRingPositiveRowsBase (Fin (d.N + 1))).toAlgebra
  haveI := FractionFieldVariableLift.isFractionRing_toFracY (A := d.PolyRingPositiveRowsBase) (σ := Fin (d.N + 1))
  exact IsFractionRing.ringEquivOfRingEquiv_algebraMap (FractionFieldVariableLift.hL K d.D d.N) P

theorem eEX4_algebraMap (c : ι) (P : MvPolynomial (SVar d.D d.N) (Ω c)) :
    d.eEX4 c (algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N) P) =
      FractionFieldVariableLift.toFracY (d.PolyRingPositiveRowsOmega c) (Fin (d.N + 1)) (FractionFieldVariableLift.hE (Ω c) d.D d.N (d.jc c) P) := by
  letI := (FractionFieldVariableLift.toFracY (d.PolyRingPositiveRowsOmega c) (Fin (d.N + 1))).toAlgebra
  haveI := FractionFieldVariableLift.isFractionRing_toFracY (A := d.PolyRingPositiveRowsOmega c) (σ := Fin (d.N + 1))
  exact IsFractionRing.ringEquivOfRingEquiv_algebraMap (FractionFieldVariableLift.hE (Ω c) d.D d.N (d.jc c)) P

noncomputable def psiE (c : ι) : d.PolyRingPositiveRowsBase →+* d.FracFieldPositiveRowsOmega c :=
  (algebraMap (d.PolyRingPositiveRowsOmega c) (d.FracFieldPositiveRowsOmega c)).comp (d.offBaseSubstitution c).toRingHom

theorem psiE_apply (c : ι) (p : d.PolyRingPositiveRowsBase) : d.psiE c p = algebraMap (d.PolyRingPositiveRowsOmega c) (d.FracFieldPositiveRowsOmega c) (d.offBaseSubstitution c p) := rfl

private theorem sumRingEquiv_X_inl' (R S₁ S₂ : Type) [CommSemiring R] (b : S₁) :
    MvPolynomial.sumRingEquiv R S₁ S₂ (MvPolynomial.X (Sum.inl b)) = MvPolynomial.X b := by
  first
  | exact MvPolynomial.sumToIter_Xl R S₁ S₂ b
  | simp [MvPolynomial.sumRingEquiv, MvPolynomial.X, MvPolynomial.monomial, AddMonoidAlgebra.one_def]

private theorem sumRingEquiv_X_inr' (R S₁ S₂ : Type) [CommSemiring R] (q : S₂) :
    MvPolynomial.sumRingEquiv R S₁ S₂ (MvPolynomial.X (Sum.inr q)) =
      MvPolynomial.C (MvPolynomial.X q) := by
  first
  | exact MvPolynomial.sumToIter_Xr R S₁ S₂ q
  | simp [MvPolynomial.sumRingEquiv, MvPolynomial.X, MvPolynomial.monomial, MvPolynomial.C, AddMonoidAlgebra.one_def]

private theorem sumRingEquiv_C' (R S₁ S₂ : Type) [CommSemiring R] (a : R) :
    MvPolynomial.sumRingEquiv R S₁ S₂ (MvPolynomial.C a) = MvPolynomial.C (MvPolynomial.C a) := by
  first
  | exact MvPolynomial.sumToIter_C R S₁ S₂ a
  | simp [MvPolynomial.sumRingEquiv, MvPolynomial.monomial, MvPolynomial.C, AddMonoidAlgebra.one_def]

theorem compat0 (c : ι) (P : KTp K d.D d.N) :
    d.eEX4 c (d.sH c P) = algebraMap (MvPolynomial (Fin (d.N + 1)) (d.FracFieldPositiveRowsOmega c)) _
      (MvPolynomial.map (d.psiE c) (FractionFieldVariableLift.hL K d.D d.N P)) := by
  have hXlE : ∀ b, MvPolynomial.sumRingEquiv (Ω c) (Fin (d.N + 1)) ({i : Fin (d.D + 1) // i ≠ 0} × Fin d.N) (MvPolynomial.X (Sum.inl b)) = MvPolynomial.X b :=
    fun b => sumRingEquiv_X_inl' _ _ _ b
  have hXrE : ∀ q, MvPolynomial.sumRingEquiv (Ω c) (Fin (d.N + 1)) ({i : Fin (d.D + 1) // i ≠ 0} × Fin d.N) (MvPolynomial.X (Sum.inr q)) = MvPolynomial.C (MvPolynomial.X q) :=
    fun q => sumRingEquiv_X_inr' _ _ _ q
  have hCE : ∀ b, MvPolynomial.sumRingEquiv (Ω c) (Fin (d.N + 1)) ({i : Fin (d.D + 1) // i ≠ 0} × Fin d.N) (MvPolynomial.C b) = MvPolynomial.C (MvPolynomial.C b) :=
    fun b => sumRingEquiv_C' _ _ _ b
  have hXlL : ∀ b, MvPolynomial.sumRingEquiv K (Fin (d.N + 1)) {v : TVar d.D d.N // v.1 ≠ 0} (MvPolynomial.X (Sum.inl b)) = MvPolynomial.X b :=
    fun b => sumRingEquiv_X_inl' _ _ _ b
  have hXrL : ∀ q, MvPolynomial.sumRingEquiv K (Fin (d.N + 1)) {v : TVar d.D d.N // v.1 ≠ 0} (MvPolynomial.X (Sum.inr q)) = MvPolynomial.C (MvPolynomial.X q) :=
    fun q => sumRingEquiv_X_inr' _ _ _ q
  have hCL : ∀ b, MvPolynomial.sumRingEquiv K (Fin (d.N + 1)) {v : TVar d.D d.N // v.1 ≠ 0} (MvPolynomial.C b) = MvPolynomial.C (MvPolynomial.C b) :=
    fun b => sumRingEquiv_C' _ _ _ b
  have hEX : ∀ p, FractionFieldVariableLift.hE (Ω c) d.D d.N (d.jc c) p =
      MvPolynomial.sumRingEquiv (Ω c) (Fin (d.N + 1)) ({i : Fin (d.D + 1) // i ≠ 0} × Fin d.N) (MvPolynomial.rename (FractionFieldVariableLift.eS d.D d.N (d.jc c)) p) := fun p => rfl
  have hLX : ∀ p, FractionFieldVariableLift.hL K d.D d.N p =
      MvPolynomial.sumRingEquiv K (Fin (d.N + 1)) {v : TVar d.D d.N // v.1 ≠ 0} (MvPolynomial.rename (FractionFieldVariableLift.eT d.D d.N) p) := fun p => rfl
  have sac1 : ∀ {β : Type} (y : β) (p : Fin d.N → β),
      Fin.succAboveCases (α := fun _ => β) (d.jc c) y p (d.jc c) = y :=
    fun y p => Fin.insertNth_apply_same (α := fun _ => _) _ y p
  have sac2 : ∀ {β : Type} (y : β) (p : Fin d.N → β) (k : Fin d.N),
      Fin.succAboveCases (α := fun _ => β) (d.jc c) y p ((d.jc c).succAbove k) = p k :=
    fun y p k => Fin.insertNth_apply_succAbove (α := fun _ => _) _ y p k
  have hpsiC : ∀ a, d.offBaseSubstitution c (MvPolynomial.C a) = MvPolynomial.C (algebraMap K (Ω c) a) := by
    intro a
    rw [← MvPolynomial.algebraMap_eq (R := K), AlgHom.commutes, MvPolynomial.algebraMap_apply]
  have hpsiX : ∀ v, d.offBaseSubstitution c (MvPolynomial.X v) =
      Fin.succAboveCases (α := fun _ => MvPolynomial ({i : Fin (d.D + 1) // i ≠ 0} × Fin d.N) (Ω c))
        (d.jc c) (-∑ k, MvPolynomial.X (⟨v.1.1, v.2⟩, k) * MvPolynomial.C (d.x c k))
        (fun k => MvPolynomial.X (⟨v.1.1, v.2⟩, k)) v.1.2 := by
    intro v
    simp only [Data.offBaseSubstitution, MvPolynomial.aeval_X]
  have e1 : ∀ a, d.sH c (MvPolynomial.C a) = algebraMap (MvPolynomial (SVar d.D d.N) (Ω c))
      (OmS (Ω c) d.D d.N) (MvPolynomial.C (algebraMap K (Ω c) a)) := by
    intro a
    rw [← MvPolynomial.algebraMap_eq (R := K), AlgHom.commutes, ← MvPolynomial.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]
  have e2 : ∀ p, d.sH c (MvPolynomial.X p) = sImg (d.jc c) (d.x c) p := by
    intro p
    simp only [Data.sH, sHom, MvPolynomial.aeval_X]
  have key : (d.eEX4 c).toRingHom.comp (d.sH c).toRingHom =
      (algebraMap (MvPolynomial (Fin (d.N + 1)) (d.FracFieldPositiveRowsOmega c)) (FractionRing (MvPolynomial (Fin (d.N + 1)) (d.FracFieldPositiveRowsOmega c)))).comp
        ((MvPolynomial.map (d.psiE c)).comp (FractionFieldVariableLift.hL K d.D d.N).toRingHom) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      show d.eEX4 c (d.sH c (MvPolynomial.C a)) = algebraMap (MvPolynomial (Fin (d.N + 1)) (d.FracFieldPositiveRowsOmega c)) (FractionRing (MvPolynomial (Fin (d.N + 1)) (d.FracFieldPositiveRowsOmega c)))
        (MvPolynomial.map (d.psiE c) (FractionFieldVariableLift.hL K d.D d.N (MvPolynomial.C a)))
      simp [e1, d.eEX4_algebraMap, hEX, hLX, hCE, hCL, FractionFieldVariableLift.toFracY, d.psiE_apply, hpsiC]
    · rintro ⟨i, j⟩
      show d.eEX4 c (d.sH c (MvPolynomial.X (i, j))) = algebraMap (MvPolynomial (Fin (d.N + 1)) (d.FracFieldPositiveRowsOmega c)) (FractionRing (MvPolynomial (Fin (d.N + 1)) (d.FracFieldPositiveRowsOmega c)))
        (MvPolynomial.map (d.psiE c) (FractionFieldVariableLift.hL K d.D d.N (MvPolynomial.X (i, j))))
      rcases Fin.eq_self_or_eq_succAbove (d.jc c) j with rfl | ⟨k, rfl⟩
      · by_cases hi : i = 0
        · subst hi
          simp [e2, sImg, sac1, d.eEX4_algebraMap, hEX, hLX, hXlE, hXlL, hXrE, hXrL, hCE,
            FractionFieldVariableLift.eS, FractionFieldVariableLift.eT, FractionFieldVariableLift.toFracY]
        · simp [e2, sImg, sac1, hi, d.eEX4_algebraMap, hEX, hLX, hXlE, hXlL, hXrE, hXrL, hCE,
            FractionFieldVariableLift.eS, FractionFieldVariableLift.eT, FractionFieldVariableLift.toFracY, d.psiE_apply, hpsiX, hpsiC]
      · by_cases hi : i = 0
        · subst hi
          simp [e2, sImg, sac2, d.eEX4_algebraMap, hEX, hLX, hXlE, hXlL, hXrE, hXrL,
            FractionFieldVariableLift.eS, FractionFieldVariableLift.eT, FractionFieldVariableLift.toFracY]
        · simp [e2, sImg, sac2, hi, d.eEX4_algebraMap, hEX, hLX, hXlE, hXlL, hXrE, hXrL,
            FractionFieldVariableLift.eS, FractionFieldVariableLift.eT, FractionFieldVariableLift.toFracY, d.psiE_apply, hpsiX]
  exact RingHom.congr_fun key P

theorem psiE_injective (h : d.S1) (c : ι) : Function.Injective (d.psiE c) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  have e := d.compat0 c ((FractionFieldVariableLift.hL K d.D d.N).symm (MvPolynomial.C p))
  rw [RingEquiv.apply_symm_apply, MvPolynomial.map_C, hp, map_zero, map_zero] at e
  have e2 := (RingEquiv.map_eq_zero_iff (d.eEX4 c)).mp e
  have e3 := h c (e2.trans (map_zero (d.sH c)).symm)
  have e4 : (MvPolynomial.C p : MvPolynomial (Fin (d.N + 1)) d.PolyRingPositiveRowsBase) = 0 := by
    rw [← RingEquiv.apply_symm_apply (FractionFieldVariableLift.hL K d.D d.N) (MvPolynomial.C p), e3, map_zero]
  exact MvPolynomial.C_eq_zero.mp e4

noncomputable def algLE (h : d.S1) (c : ι) : Algebra d.FracFieldPositiveRowsBase (d.FracFieldPositiveRowsOmega c) :=
  (IsFractionRing.lift (A := d.PolyRingPositiveRowsBase) (K := d.FracFieldPositiveRowsBase) (d.psiE_injective h c)).toAlgebra

theorem algLE_algebraMap (h : d.S1) (c : ι) (p : d.PolyRingPositiveRowsBase) :
    letI := d.algLE h c
    algebraMap d.FracFieldPositiveRowsBase (d.FracFieldPositiveRowsOmega c) (algebraMap d.PolyRingPositiveRowsBase d.FracFieldPositiveRowsBase p) = d.psiE c p := IsFractionRing.lift_algebraMap (d.psiE_injective h c) p

theorem fieldEquiv_compat_liftY (h : d.S1) (c : ι) (q : KTf K d.D d.N) :
    letI := d.algLE h c
    d.eEX4 c (d.KTtoS h c q) = VariableBasisExtension.liftY (L := d.FracFieldPositiveRowsBase) (E := d.FracFieldPositiveRowsOmega c) (σ := Fin (d.N + 1)) (d.eLX4 q) := by
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := KTp K d.D d.N) q
  simp only [map_div₀]
  congr 1
  all_goals
    rw [show ∀ P : KTp K d.D d.N, d.KTtoS h c (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) P) =
      d.sH c P from fun P => IsFractionRing.lift_algebraMap _ _]
    rw [d.compat0 c, d.eLX4_algebraMap]
    unfold FractionFieldVariableLift.toFracY VariableBasisExtension.liftY
    rw [RingHom.comp_apply, IsFractionRing.lift_algebraMap, RingHom.comp_apply, MvPolynomial.map_map]
    rw [show (@algebraMap d.FracFieldPositiveRowsBase (d.FracFieldPositiveRowsOmega c) _ _ (d.algLE h c)).comp (algebraMap d.PolyRingPositiveRowsBase d.FracFieldPositiveRowsBase) =
      d.psiE c from RingHom.ext fun p => d.algLE_algebraMap h c p]

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscAB
section
namespace ReciprocityTheory.ChartRestriction.G.T0

namespace HDiscLat

open Module

variable {R F : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field F]
  [Algebra R F] [IsFractionRing R F]
  {ι : Type} [Fintype ι] [DecidableEq ι] {L : ι → Type} [∀ c, Field (L c)] [∀ c, Algebra F (L c)]
  [∀ c, FiniteDimensional F (L c)] [∀ c, Algebra.IsSeparable F (L c)] [∀ c, Algebra R (L c)]
  [∀ c, IsScalarTower R F (L c)]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R F] [Fintype ι] [DecidableEq ι]
  [∀ c, FiniteDimensional F (L c)] [∀ c, Algebra.IsSeparable F (L c)] in
theorem trace_algebraMap_mul (c : ι) (r : R) (z : L c) :
    Algebra.trace F (L c) (algebraMap R (L c) r * z) =
      algebraMap R F r * Algebra.trace F (L c) z := by
  rw [IsScalarTower.algebraMap_apply R F (L c), ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R F] [Fintype ι] [DecidableEq ι]
  [∀ c, FiniteDimensional F (L c)] [∀ c, Algebra.IsSeparable F (L c)] in
theorem trace_term (c : ι) (r r' : R) (h x y : L c) :
    Algebra.trace F (L c) (algebraMap R (L c) r * (h * x) * (algebraMap R (L c) r' * (h * y))) =
      algebraMap R F r * Algebra.trace F (L c) (h * h * x * y) * algebraMap R F r' := by
  have e : algebraMap R (L c) r * (h * x) * (algebraMap R (L c) r' * (h * y)) =
      algebraMap R (L c) r * (algebraMap R (L c) r' * (h * h * x * y)) := by ring
  rw [e, trace_algebraMap_mul, trace_algebraMap_mul]
  ring

theorem sum_three_comm {α β γ M : Type*} [AddCommMonoid M] (s : Finset α) (t : Finset β) (u : Finset γ)
    (f : α → β → γ → M) :
    ∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, f a b c = ∑ c ∈ u, ∑ b ∈ t, ∑ a ∈ s, f a b c := by
  calc ∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, f a b c = ∑ a ∈ s, ∑ c ∈ u, ∑ b ∈ t, f a b c :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ c ∈ u, ∑ a ∈ s, ∑ b ∈ t, f a b c := Finset.sum_comm
    _ = ∑ c ∈ u, ∑ b ∈ t, ∑ a ∈ s, f a b c := Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem lattice_main {ϖ : R} (hϖ : Irreducible ϖ) (g : ∀ c, L c) (hg : ∀ c, g c ≠ 0)
    {m : ℕ} (hm : m = ∑ c, finrank F (L c)) (b : Fin m → ∀ c, L c)
    (hb : ∀ k c, g c * b k c ∈ integralClosure R (L c)) (hli : LinearIndependent F b) :
    ∃ n t : ℕ, ∃ u : Rˣ,
      Module.length R
        (↥(Submodule.span R {y : ∀ c, L c | ∀ c, g c * y c ∈ integralClosure R (L c)}) ⧸
          (Submodule.span R (Set.range b)).comap
            (Submodule.span R {y : ∀ c, L c | ∀ c, g c * y c ∈ integralClosure R (L c)}).subtype) = n ∧
      (Matrix.of fun k l : Fin m => ∑ c, Algebra.trace F (L c) (b k c * b l c)).det *
          (∏ c, Algebra.norm F (g c)) ^ 2 = algebraMap R F (↑u * ϖ ^ (2 * n + t)) := by
  classical
  have hB : ∀ c, Module.Finite R (integralClosure R (L c)) ∧
      Module.Free R (integralClosure R (L c)) ∧
      finrank R (integralClosure R (L c)) = finrank F (L c) := fun c => by
    obtain ⟨_, h1, h2, h3, _⟩ := ReciprocityTheory.MultiplicativeHeights.Closed.dedekindRank R F (L c)
    exact ⟨h1, h2, h3⟩
  haveI : ∀ c, Module.Finite R (integralClosure R (L c)) := fun c => (hB c).1
  haveI : ∀ c, Module.Free R (integralClosure R (L c)) := fun c => (hB c).2.1
  let a := fun c => Module.Free.chooseBasis R (integralClosure R (L c))
  let α := Pi.basis a
  have hcard : Fintype.card (Σ c, Module.Free.ChooseBasisIndex R (integralClosure R (L c))) = m := by
    rw [hm, Fintype.card_sigma]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Module.finrank_eq_card_chooseBasisIndex, (hB c).2.2]
  let σ := Fintype.equivFinOfCardEq hcard
  let φ : (∀ c, integralClosure R (L c)) →ₗ[R] (∀ c, L c) :=
    LinearMap.pi fun c => (LinearMap.mulLeft R (g c)⁻¹) ∘ₗ
      (integralClosure R (L c)).val.toLinearMap ∘ₗ LinearMap.proj c
  have hφ : ∀ x c, φ x c = (g c)⁻¹ * (x c : L c) := fun x c => rfl
  have hφinj : Function.Injective φ := by
    intro x y hxy
    funext c
    apply Subtype.ext
    have := congrFun hxy c
    rw [hφ, hφ] at this
    exact mul_left_cancel₀ (inv_ne_zero (hg c)) this
  have hSA : Submodule.span R {y : ∀ c, L c | ∀ c, g c * y c ∈ integralClosure R (L c)} =
      LinearMap.range φ := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro y hy
      refine ⟨fun c => ⟨g c * y c, hy c⟩, ?_⟩
      funext c
      rw [hφ]
      simp [← mul_assoc, inv_mul_cancel₀ (hg c)]
    · rintro _ ⟨x, rfl⟩
      apply Submodule.subset_span
      intro c
      rw [hφ, ← mul_assoc, mul_inv_cancel₀ (hg c), one_mul]
      exact (x c).2
  let b' : Fin m → ∀ c, integralClosure R (L c) := fun k c => ⟨g c * b k c, hb k c⟩
  have hb' : φ ∘ b' = b := by
    funext k c
    simp only [Function.comp_apply]
    rw [hφ]
    simp [b', ← mul_assoc, inv_mul_cancel₀ (hg c)]
  have hliR : LinearIndependent R b :=
    hli.restrict_scalars (by
      intro x y hxy
      simp only [Algebra.smul_def, mul_one] at hxy
      exact IsFractionRing.injective R F hxy)
  have hli' : LinearIndependent R b' := LinearIndependent.of_comp φ (by rw [hb']; exact hliR)
  obtain ⟨n, u, hlen, hdet⟩ := length_quot hϖ α φ hφinj _ hSA b' hli' σ
  rw [hb'] at hlen
  set T := α.toMatrix (b' ∘ σ) with hT
  have hdetT : T.det = ↑u * ϖ ^ n := by rw [hT, ← Basis.det_apply]; exact hdet
  have hexp : ∀ q c, ((b' (σ q) c : integralClosure R (L c)) : L c) =
      ∑ p, algebraMap R (L c) (T p q) * ((α p c : integralClosure R (L c)) : L c) := by
    intro q c
    have h1 := congrArg (fun x : (∀ c, integralClosure R (L c)) =>
      ((x c : integralClosure R (L c)) : L c)) (α.sum_repr (b' (σ q)))
    simp only [Finset.sum_apply, Pi.smul_apply] at h1
    rw [← h1]
    simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, hT,
      Basis.toMatrix_apply, Function.comp_apply]
    simp only [Algebra.smul_def]
  have hbexp : ∀ q c, b (σ q) c = ∑ p, algebraMap R (L c) (T p q) *
      ((g c)⁻¹ * ((α p c : integralClosure R (L c)) : L c)) := by
    intro q c
    have : b (σ q) c = (g c)⁻¹ * ((b' (σ q) c : integralClosure R (L c)) : L c) := by
      rw [← hb']; rfl
    rw [this, hexp, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  let H : Matrix (Σ c, Module.Free.ChooseBasisIndex R (integralClosure R (L c)))
      (Σ c, Module.Free.ChooseBasisIndex R (integralClosure R (L c))) F :=
    Matrix.of fun p q => ∑ c, Algebra.trace F (L c) ((g c)⁻¹ * (g c)⁻¹ *
      ((α p c : integralClosure R (L c)) : L c) * ((α q c : integralClosure R (L c)) : L c))
  have hG : (Matrix.of fun k l : Fin m => ∑ c, Algebra.trace F (L c) (b k c * b l c)).submatrix σ σ =
      (T.map (algebraMap R F)).transpose * H * T.map (algebraMap R F) := by
    ext p' q'
    simp only [Matrix.submatrix_apply, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply, H, hbexp]
    simp only [Finset.sum_mul, Finset.mul_sum, map_sum, trace_term]
    rw [sum_three_comm, Finset.sum_comm]
  have hH : H = Matrix.blockDiagonal' fun c => Matrix.of fun i j => Algebra.trace F (L c)
      ((g c)⁻¹ * (g c)⁻¹ * ((a c i : integralClosure R (L c)) : L c) *
        ((a c j : integralClosure R (L c)) : L c)) := by
    ext ⟨c, i⟩ ⟨c', j⟩
    simp only [H, Matrix.of_apply, α, Pi.basis_apply]
    rw [Finset.sum_eq_single c]
    · by_cases hc : c = c'
      · subst hc
        simp [Matrix.blockDiagonal'_apply_eq]
      · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hc, Pi.single_eq_of_ne hc]
        simp
    · intro c'' _ hc''
      rw [Pi.single_eq_of_ne hc'']
      simp
    · simp
  haveI : ∀ c, IsLocalization (Algebra.algebraMapSubmonoid (integralClosure R (L c))
      (nonZeroDivisors R)) (L c) := fun c =>
    IsIntegralClosure.isLocalization R F (L c) (integralClosure R (L c))
  let a' := fun c => (a c).localizationLocalization F (nonZeroDivisors R) (L c)
  have hblock : ∀ c, (Matrix.of fun i j => Algebra.trace F (L c)
      ((g c)⁻¹ * (g c)⁻¹ * ((a c i : integralClosure R (L c)) : L c) *
        ((a c j : integralClosure R (L c)) : L c))).det =
      Algebra.norm F ((g c)⁻¹ * (g c)⁻¹) * algebraMap R F (Algebra.discr R (a c)) := by
    intro c
    rw [← Algebra.discr_localizationLocalization R (nonZeroDivisors R) (L c) (a c), ← gram_mul]
    congr 1
    ext i j
    simp only [Matrix.of_apply, a', Module.Basis.localizationLocalization_apply]
    rfl
  have hd0 : ∀ c, Algebra.discr R (a c) ≠ 0 := by
    intro c h
    have := Algebra.discr_not_zero_of_basis F (a' c)
    rw [Algebra.discr_localizationLocalization R (nonZeroDivisors R) (L c) (a c), h, map_zero] at this
    exact this rfl
  have hN : ∀ c, Algebra.norm F ((g c)⁻¹ * (g c)⁻¹) * Algebra.norm F (g c) ^ 2 = 1 := by
    intro c
    have h1 : Algebra.norm F (g c)⁻¹ * Algebra.norm F (g c) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ (hg c), map_one]
    rw [map_mul, sq]
    calc Algebra.norm F (g c)⁻¹ * Algebra.norm F (g c)⁻¹ * (Algebra.norm F (g c) * Algebra.norm F (g c))
        = (Algebra.norm F (g c)⁻¹ * Algebra.norm F (g c)) *
          (Algebra.norm F (g c)⁻¹ * Algebra.norm F (g c)) := by ring
      _ = 1 := by rw [h1, one_mul]
  have hprod : (∏ c, Algebra.discr R (a c)) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun c _ => hd0 c
  obtain ⟨t, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hprod hϖ
  refine ⟨n, t, u * u * v, hlen, ?_⟩
  rw [← Matrix.det_submatrix_equiv_self σ, hG, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    hH, det_blockDiagonal', Finset.prod_congr rfl fun c _ => hblock c]
  have hmap : (T.map (algebraMap R F)).det = algebraMap R F T.det := by
    rw [RingHom.map_det]; rfl
  rw [hmap, hdetT, Finset.prod_mul_distrib, ← map_prod, hv]
  have hNN : (∏ c, Algebra.norm F ((g c)⁻¹ * (g c)⁻¹)) * (∏ c, Algebra.norm F (g c)) ^ 2 = 1 := by
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun c _ => hN c
  calc algebraMap R F (↑u * ϖ ^ n) * ((∏ c, Algebra.norm F ((g c)⁻¹ * (g c)⁻¹)) *
          algebraMap R F (↑v * ϖ ^ t)) * algebraMap R F (↑u * ϖ ^ n) * (∏ c, Algebra.norm F (g c)) ^ 2
      = algebraMap R F (↑u * ϖ ^ n) * algebraMap R F (↑v * ϖ ^ t) * algebraMap R F (↑u * ϖ ^ n) *
          ((∏ c, Algebra.norm F ((g c)⁻¹ * (g c)⁻¹)) * (∏ c, Algebra.norm F (g c)) ^ 2) := by ring
    _ = algebraMap R F (↑(u * u * v) * ϖ ^ (2 * n + t)) := by
      rw [hNN, mul_one, ← map_mul, ← map_mul]
      congr 1
      rw [Units.val_mul, Units.val_mul, pow_add, pow_mul]
      ring

end HDiscLat

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HeightKerScaledSubstitutionLeOne
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem height_ker_scaledSubstitution_le_one (hd : d.AxH 𝒜) (c : ι) : (RingHom.ker (d.scaledSubstitution c)).height ≤ 1 := by
  classical
  obtain ⟨J, hJ⟩ := hd.a1 c
  obtain ⟨δ, hδ⟩ := ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence.exists_dual_derivations (K := K) (d.x c) J hJ
  have hy : d.affineCoord c (d.jc c) = 1 := scalarRatio_self (hd.w_base c)
  let ρ : Option (Fin d.D) → Fin (d.D + 2) := fun o =>
    (finSuccEquiv (d.D + 1)).symm (some ((finSuccEquiv d.D).symm o))
  have hρ : Function.Injective ρ := by
    intro o o' h
    simpa [ρ] using h
  have hind := algebraicIndependent_scaledForms (K := K) (d.affineCoord c) (d.jc c) hy J δ hδ ρ hρ
  let e : (Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2) ≃
      Option ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Option (Fin d.D)) :=
    { toFun := fun x => match x with
        | Sum.inl p => some (Sum.inl p)
        | Sum.inr i => (finSuccEquiv (d.D + 1) i).map fun j => Sum.inr (finSuccEquiv d.D j)
      invFun := fun y => match y with
        | none => Sum.inr 0
        | some (Sum.inl p) => Sum.inl p
        | some (Sum.inr o) => Sum.inr (ρ o)
      left_inv := by
        rintro (p | i)
        · rfl
        · rcases h : finSuccEquiv (d.D + 1) i with _ | j <;>
          · have := (finSuccEquiv (d.D + 1)).symm_apply_apply i
            rw [h] at this
            simpa [h, ρ] using this
      right_inv := by
        rintro (_ | p | o)
        · simp
        · rfl
        · simp [ρ] }
  let g := (MvPolynomial.renameEquiv K e).trans
    (MvPolynomial.optionEquivLeft K ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Option (Fin d.D)))
  let gr := g.toRingEquiv
  rw [← RingEquiv.height_comap gr.symm (RingHom.ker (d.scaledSubstitution c))]
  haveI hk : (RingHom.ker (d.scaledSubstitution c)).IsPrime := RingHom.ker_isPrime _
  haveI : (Ideal.comap gr.symm (RingHom.ker (d.scaledSubstitution c))).IsPrime := Ideal.comap_isPrime _ _
  refine ReciprocityTheory.CA.height_le_one_of_comap_C_eq_bot _ ?_
  rw [eq_bot_iff]
  intro a ha
  rw [Ideal.mem_comap, Ideal.mem_comap, RingHom.mem_ker] at ha
  rw [Ideal.mem_bot]
  have h2 : (MvPolynomial.optionEquivLeft K ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Option (Fin d.D))).symm
      (Polynomial.C a) = MvPolynomial.rename some a := by
    rw [AlgEquiv.symm_apply_eq]
    exact (optionEquivLeft_rename_some' a).symm
  have h1 : gr.symm (Polynomial.C a) = MvPolynomial.rename (fun s => e.symm (some s)) a := by
    show (MvPolynomial.renameEquiv K e).symm ((MvPolynomial.optionEquivLeft K
      ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Option (Fin d.D))).symm (Polynomial.C a)) = _
    rw [h2, MvPolynomial.renameEquiv_symm, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_rename]
    rfl
  rw [h1, scaledSubstitution_eq, MvPolynomial.aeval_rename] at ha
  have hfam : (Sum.elim (fun p => (MvPolynomial.X (some p) :
        MvPolynomial (Option (Fin (d.D + 2) × Fin (d.N + 1))) (Ω c)))
      (fun i => MvPolynomial.X none *
        ∑ j, MvPolynomial.X (some (i, j)) * MvPolynomial.C (d.affineCoord c j))) ∘
      (fun s => e.symm (some s)) =
      Sum.elim (fun p => (MvPolynomial.X (some p) :
        MvPolynomial (Option (Fin (d.D + 2) × Fin (d.N + 1))) (Ω c)))
      (fun o => MvPolynomial.X none *
        ∑ j, MvPolynomial.X (some (ρ o, j)) * MvPolynomial.C (d.affineCoord c j)) := by
    funext s
    rcases s with p | o <;> rfl
  rw [hfam] at ha
  exact (injective_iff_map_eq_zero _).mp hind a ha

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

