import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2250
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2246
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1605
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0081
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2249
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2240
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0038
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0061
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2247
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2225

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PropertyOfCodimOneLocalUnits
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.HartogsUnit

variable {A : Type} [CommRing A] [IsDomain A]

noncomputable def toFrac (p : Ideal A) [p.IsPrime] : Localization.AtPrime p →+* FractionRing A :=
  IsLocalization.lift (M := p.primeCompl) (S := Localization.AtPrime p)
    (g := algebraMap A (FractionRing A))
    (fun s => IsUnit.mk0 _ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (p.primeCompl_le_nonZeroDivisors s.2)))

theorem toFrac_comp (p : Ideal A) [p.IsPrime] :
    (toFrac p).comp (algebraMap A (Localization.AtPrime p)) = algebraMap A (FractionRing A) :=
  IsLocalization.lift_comp _

theorem toFrac_injective (p : Ideal A) [p.IsPrime] : Function.Injective (toFrac p) := by
  rw [toFrac, IsLocalization.lift_injective_iff]
  intro x y
  rw [(IsLocalization.injective (Localization.AtPrime p) p.primeCompl_le_nonZeroDivisors).eq_iff,
    (IsFractionRing.injective A (FractionRing A)).eq_iff]

theorem toFrac_mem (p : Ideal A) [p.IsPrime] (w : Localization.AtPrime p) :
    ∃ s, s ∉ p ∧ s • toFrac p w ∈ (algebraMap A (FractionRing A)).range := by
  obtain ⟨⟨m, s⟩, e⟩ := IsLocalization.surj p.primeCompl w
  refine ⟨s, s.2, m, ?_⟩
  have h := congrArg (toFrac p) e
  simp only [map_mul] at h
  rw [← RingHom.comp_apply (toFrac p), ← RingHom.comp_apply (toFrac p), toFrac_comp] at h
  rw [Algebra.smul_def, mul_comm, h]

theorem exists_unit_of_local_units : ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A]
    (P : ∀ (k : Type) [Field k], (A →+* k) → k → Prop) (good : Set (PrimeSpectrum A)),
    (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∈ good →
    (∀ 𝔭 : PrimeSpectrum A, (𝔭 ∈ good ∨ 𝔭.asIdeal.height = 1) → ∃ u : (Localization.AtPrime 𝔭.asIdeal)ˣ,
      ∀ (k : Type) [Field k] (φ : Localization.AtPrime 𝔭.asIdeal →+* k), P k (φ.comp (algebraMap A _)) (φ u)) →
    (∃ (k : Type) (_ : Field k) (φ : A →+* k), Function.Injective φ ∧ ∀ v v', P k φ v → P k φ v' → v = v') →
    (∀ (k : Type) [Field k] (φ : A →+* k) (v : k),
      (⟨RingHom.ker φ, RingHom.ker_isPrime φ⟩ : PrimeSpectrum A) ∉ good → P k φ v) →
    ∃ f : Aˣ, ∀ (k : Type) [Field k] (φ : A →+* k), P k φ (φ f) := by
  intro A _ _ _ _ P good hbot hloc ⟨k, _, φ, hinj, huniq⟩ hbad
  classical
  let K := FractionRing A
  let ψ : K →+* k := IsFractionRing.lift hinj
  have hφ : ψ.comp (algebraMap A K) = φ := RingHom.ext fun a => IsFractionRing.lift_algebraMap hinj a
  obtain ⟨u₀, hu₀⟩ := hloc ⟨⊥, Ideal.isPrime_bot⟩ (Or.inl hbot)
  let x : K := toFrac _ (u₀ : Localization.AtPrime (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A).asIdeal)
  let y : K := toFrac _ ((u₀⁻¹ : (Localization.AtPrime (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A).asIdeal)ˣ) :
    Localization.AtPrime (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A).asIdeal)
  have hxy : x * y = 1 := by simp only [x, y, ← map_mul, Units.mul_inv, map_one]
  have key : ∀ (𝔭 : PrimeSpectrum A) (u : (Localization.AtPrime 𝔭.asIdeal)ˣ),
      (∀ (k : Type) [Field k] (φ : Localization.AtPrime 𝔭.asIdeal →+* k),
        P k (φ.comp (algebraMap A _)) (φ u)) → toFrac 𝔭.asIdeal u = x := by
    intro 𝔭 u hu
    have h1 := hu k (ψ.comp (toFrac 𝔭.asIdeal))
    have h0 := hu₀ k (ψ.comp (toFrac _))
    rw [RingHom.comp_assoc, toFrac_comp, hφ] at h1 h0
    exact ψ.injective (huniq _ _ h1 h0)
  have hmem : ∀ z : K, (∀ 𝔭 : PrimeSpectrum A, 𝔭.asIdeal.height = 1 →
      ∃ w, toFrac 𝔭.asIdeal w = z) → ∃ a : A, algebraMap A K a = z := by
    intro z hz
    refine RingHom.mem_range.mp ((GlobalTheory.mem_range_algebraMap_iff_forall_height_eq_one (A := A) z).mpr ?_)
    intro p _ hp
    obtain ⟨w, hw⟩ := hz ⟨p, inferInstance⟩ hp
    rw [GlobalTheory.mem_primeLocalSubalgebra_iff, ← hw]
    exact toFrac_mem p w
  have hx0 : x ≠ 0 := left_ne_zero_of_mul_eq_one hxy
  obtain ⟨a, ha⟩ := hmem x fun 𝔭 hp => by
    obtain ⟨u, hu⟩ := hloc 𝔭 (Or.inr hp)
    exact ⟨u, key 𝔭 u hu⟩
  obtain ⟨b, hb⟩ := hmem y fun 𝔭 hp => by
    obtain ⟨u, hu⟩ := hloc 𝔭 (Or.inr hp)
    refine ⟨((u⁻¹ : (Localization.AtPrime 𝔭.asIdeal)ˣ) : Localization.AtPrime 𝔭.asIdeal), ?_⟩
    apply mul_left_cancel₀ hx0
    rw [hxy, ← key 𝔭 u hu, ← map_mul, Units.mul_inv, map_one]
  have hab : a * b = 1 := IsFractionRing.injective A K (by rw [map_mul, ha, hb, hxy, map_one])
  let f : Aˣ := ⟨a, b, hab, by rw [mul_comm]; exact hab⟩
  refine ⟨f, fun k' _ φ' => ?_⟩
  by_cases hg : (⟨RingHom.ker φ', RingHom.ker_isPrime φ'⟩ : PrimeSpectrum A) ∈ good
  · obtain ⟨u, hu⟩ := hloc _ (Or.inl hg)
    let φl : Localization.AtPrime (RingHom.ker φ') →+* k' :=
      IsLocalization.lift (M := (RingHom.ker φ').primeCompl) (g := φ')
        (fun s => IsUnit.mk0 _ (fun h => s.2 (RingHom.mem_ker.mpr h)))
    have hl : φl.comp (algebraMap A _) = φ' := IsLocalization.lift_comp _
    have h := hu k' φl
    rw [hl] at h
    have hu' : (u : Localization.AtPrime (RingHom.ker φ')) = algebraMap A _ (f : A) :=
      toFrac_injective _ (by rw [key _ u hu, ← RingHom.comp_apply, toFrac_comp]; exact ha.symm)
    rwa [hu', ← RingHom.comp_apply, hl] at h
  · exact hbad k' φ' _ hg

end GlobalTheory.HartogsUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackMemCuspFormSupLatticeIff
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.AllWt GlobalTheory.CovTop

namespace GlobalTheory.CovTop.PullLat

variable {D : D7}

theorem levPull_of_pull {T : Core D} {j : ℕ} (Y : Deep T j) {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : T.R j}
    (hf : f ∈ sec (T.Q.Xo j) T.Q.c a n) {g : Rul Y.d.Xo₂ Y.d.c₂} (hp : Y.Pull f g) :
    GlobalTheory.LevPull.Pull Y.d (GlobalTheory.FieldBC.rulBC Y.hle f) g := by
  intro k _ _ _ _ hk y₂ y hov
  letI : Algebra T.Q.c.F k := GlobalTheory.FieldBC.resAlg Y.hle k
  have ho : AlgOver T.Q.c Y.c' Y.hle k := fun _ => rfl
  rw [((GlobalTheory.FieldBC.rulBC_sec_val_linear _ _ _ _ _ _ _ Y.hle).1 a n f hf).2 k ho y]
  exact hp k ho hk y₂ y (y.res Y.hle ho) hov rfl rfl HEq.rfl

theorem pull_mem_latW : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), LawsJ T → InR D j →
    Y.Good e o → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n))
      (g : Y.V (wtZ a n)), Y.Pull f g → (g ∈ latW Y.U (wtZ a n) ↔ f ∈ latW (T.U j) (wtZ a n)) := by
  intro D T j Y e o hT hj hY a n f g hp
  have hpos := GlobalTheory.CovTop.Inhab.rank_pos T.toCore hT.pins j hj
  have hfs : (f : T.R j) ∈ sec (T.Q.Xo j) T.Q.c a n := by
    have h : (f : T.R j) ∈ cusp (T.Q.Xo j) T.Q.c (T.U j) a n := by rw [← cuspW_wtZ]; exact f.2
    exact cusp_le_sec _ _ _ _ _ h
  have hgs : (g : Rul Y.d.Xo₂ Y.d.c₂) ∈ sec Y.d.Xo₂ Y.d.c₂ a n := by
    have h : (g : Rul Y.d.Xo₂ Y.d.c₂) ∈ cusp Y.d.Xo₂ Y.d.c₂ Y.U a n := by rw [← cuspW_wtZ]; exact g.2
    exact cusp_le_sec _ _ _ _ _ h
  have hfs' := ((GlobalTheory.FieldBC.rulBC_sec_val_linear _ _ _ _ (T.Q.Xo j) _ _ Y.hle).1 a n _ hfs).1
  have hL := GlobalTheory.LevGeo.laws_core D T j hT hj
  have hne : (T.Q.Dw j).p ≠ (T.Q.Dw j).q := by
    obtain ⟨hp, hq, -⟩ := hL.dat
    obtain ⟨h1, h2⟩ := hj
    have hk := D.R.m_add_three_le_k
    rw [hp, hq]
    simp only [Ranks.sigW]
    omega
  have h1 := GlobalTheory.CoverInt.pull_intAt_iff _ _ _ _ _ _ Y.d hpos hY.lev.1 (Or.inl ⟨hne, hL.levA⟩) a n _ hfs' _ hgs (levPull_of_pull Y hfs hp)
  have h2 := GlobalTheory.T.isIntegralRule_ruleBaseChangeCoeffField_iff _ _ _ _ _ _ _ Y.hle a n _ hfs
  exact h1.trans h2

end GlobalTheory.CovTop.PullLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadNonnegOfInt
section
open GlobalTheory.Poinc Matrix

namespace GlobalTheory.Poinc

open Matrix in
private lemma exists_nat_mul_rat_eq_int' {s : ℕ} (q : Fin s → ℚ) :
    ∃ N : ℕ, 0 < N ∧ ∃ n : Fin s → ℤ, ∀ u, (N : ℚ) * q u = n u := by
  refine ⟨∏ v, (q v).den, Finset.prod_pos fun v _ => (q v).den_pos,
    fun u => (q u).num * ∏ v ∈ Finset.univ.erase u, ((q v).den : ℤ), fun u => ?_⟩
  rw [← Finset.mul_prod_erase Finset.univ (fun v => (q v).den) (Finset.mem_univ u)]
  push_cast
  rw [← Rat.mul_den_eq_num (q u)]
  ring

open Matrix in
private lemma bilinForm_sum_zsmul_eq_sum_mul {s : ℕ} {X : Type} [AddCommGroup X]
    (β : LinearMap.BilinForm ℤ X) (y : Fin s → X) (n : Fin s → ℤ) :
    β (∑ u, n u • y u) (∑ v, n v • y v) = ∑ u, ∑ v, n u * n v * β (y u) (y v) := by
  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  ring

open Matrix in
private lemma gram_quadratic_real_nonneg {s : ℕ} {X : Type} [AddCommGroup X]
    (β : LinearMap.BilinForm ℤ X) (hpos : ∀ x, 0 ≤ β x x) (y : Fin s → X) (c : Fin s → ℝ) :
    0 ≤ ∑ u, ∑ v, c u * c v * ((β (y u) (y v) : ℤ) : ℝ) := by
  have hdense : DenseRange (Pi.map fun _ : Fin s => (Rat.cast : ℚ → ℝ)) :=
    DenseRange.piMap fun _ => Rat.denseRange_cast
  refine hdense.induction_on (p := fun c : Fin s → ℝ =>
    0 ≤ ∑ u, ∑ v, c u * c v * ((β (y u) (y v) : ℤ) : ℝ)) c
    (isClosed_le continuous_const (by fun_prop)) fun q => ?_
  obtain ⟨N, hN, n, hn⟩ := exists_nat_mul_rat_eq_int' q
  have hnR : ∀ u, (N : ℝ) * (q u : ℝ) = (n u : ℝ) := fun u => by exact_mod_cast hn u
  have hNpos : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  have key : (N : ℝ) ^ 2 * ∑ u, ∑ v, (q u : ℝ) * (q v : ℝ) * ((β (y u) (y v) : ℤ) : ℝ) =
      ((β (∑ u, n u • y u) (∑ v, n v • y v) : ℤ) : ℝ) := by
    rw [bilinForm_sum_zsmul_eq_sum_mul]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← hnR u, ← hnR v]
    ring
  have h0 : (0 : ℝ) ≤ ((β (∑ u, n u • y u) (∑ v, n v • y v) : ℤ) : ℝ) := by
    exact_mod_cast hpos _
  rw [← key] at h0
  exact (mul_nonneg_iff_of_pos_left hNpos).mp h0

open Matrix in

theorem _root_.GlobalTheory.Poinc.qW_nonneg_of_posW : ∀ {s : ℕ} (W : Matrix (Fin s) (Fin s) ℤ),
    _root_.GlobalTheory.Poinc.PosW W → ∀ {X : Type} [AddCommGroup X]
    (β : LinearMap.BilinForm ℤ X), (∀ a b, β a b = β b a) → (∀ x, 0 ≤ β x x) →
    ∀ y : Fin s → X, 0 ≤ _root_.GlobalTheory.Poinc.qW W β y := by
  intro s W hW X _ β hsymm hpos y
  unfold _root_.GlobalTheory.Poinc.PosW at hW
  unfold _root_.GlobalTheory.Poinc.qW
  obtain ⟨m, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hW.posSemidef
  set S : ℤ := ∑ u, ∑ w, W u w * β (y u) (y w) with hS
  have hswap : ∑ u, ∑ w, W w u * β (y u) (y w) = S := by
    rw [hS, Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun w _ => ?_
    rw [hsymm]
  have htwo : ((2 * S : ℤ) : ℝ) = ∑ u, ∑ w,
      ((W + W.transpose).map (Int.cast : ℤ → ℝ)) u w * ((β (y u) (y w) : ℤ) : ℝ) := by
    have : (2 * S : ℤ) = ∑ u, ∑ w, (W u w + W w u) * β (y u) (y w) := by
      simp only [add_mul, Finset.sum_add_distrib, hswap, hS]
      ring
    rw [this]
    push_cast
    simp [Matrix.map_apply, Matrix.add_apply, Matrix.transpose_apply]
  have hnonneg : (0 : ℝ) ≤ ∑ u, ∑ w,
      ((W + W.transpose).map (Int.cast : ℤ → ℝ)) u w * ((β (y u) (y w) : ℤ) : ℝ) := by
    rw [hv]
    have e : ∀ u w, (∑ i, vecMulVec (v i) (star (v i))) u w * ((β (y u) (y w) : ℤ) : ℝ) =
        ∑ i, v i u * v i w * ((β (y u) (y w) : ℤ) : ℝ) := by
      intro u w
      simp [Matrix.sum_apply, Matrix.vecMulVec_apply, Finset.sum_mul]
    simp_rw [e]
    calc (0 : ℝ) ≤ ∑ i, ∑ u, ∑ w, v i u * v i w * ((β (y u) (y w) : ℤ) : ℝ) :=
          Finset.sum_nonneg fun i _ => gram_quadratic_real_nonneg β hpos y (v i)
      _ = ∑ u, ∑ i, ∑ w, v i u * v i w * ((β (y u) (y w) : ℤ) : ℝ) := Finset.sum_comm
      _ = ∑ u, ∑ w, ∑ i, v i u * v i w * ((β (y u) (y w) : ℤ) : ℝ) :=
          Finset.sum_congr rfl fun u _ => Finset.sum_comm
  rw [← htwo] at hnonneg
  have : (0 : ℝ) ≤ (S : ℝ) := by push_cast at hnonneg; linarith
  exact_mod_cast this

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFunctionUnitAtPointOfFibreQuotientStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalFunctionUnitAtPoint_of_fibre_quotient : ∀ (X W : Scheme.{0}) [IsIntegral X] [IsIntegral W] (Γ : Type) [Group Γ] [Finite Γ]
    (ρ : Γ →* Aut X) (q : X ⟶ W) [IsDominant q], IsAffineQuotient ρ q → ∀ (y : W) (b : W.functionField),
    (∀ x, q x = y → UnitAt x (functionFieldMap q b)) → UnitAt y b := by
  first | exact @GlobalTheory.OrbitSep.unitAt_of_forall_unitAt_fibre | exact GlobalTheory.OrbitSep.unitAt_of_forall_unitAt_fibre | (intros; apply GlobalTheory.OrbitSep.unitAt_of_forall_unitAt_fibre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalTopFormPullbackNeZeroOfEtale
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.EtaleKlt

theorem formallyEtale_of_isIso {R S : CommRingCat.{0}} (e : R ⟶ S) [IsIso e] :
    e.hom.FormallyEtale := by
  letI := e.hom.toAlgebra
  let E : R ≃ₐ[R] S := { (asIso e).commRingCatIsoToRingEquiv with commutes' := fun _ => rfl }
  show Algebra.FormallyEtale R S
  exact Algebra.FormallyEtale.of_equiv E

theorem genericPoint_mem_of_nonempty {X : Scheme.{0}} [IsIntegral X] (U : X.Opens)
    (hU : (U : Set X).Nonempty) : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).2 (by simpa using hU)

theorem map_genericPoint {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)
    [IsDominant f] : f (genericPoint X) = genericPoint Y := by
  have := (genericPoint_spec X).image f.continuous
  rw [Set.image_univ, f.denseRange.closure_range] at this
  exact this.eq (genericPoint_spec Y)

theorem formallyEtale_functionFieldMap {M W : Scheme.{0}} [IsIntegral M] [IsIntegral W]
    (f : M ⟶ W) [IsDominant f] (U : M.Opens) (hf : Etale (U.ι ≫ f))
    (hU : (U : Set M).Nonempty) : (functionFieldMap f).FormallyEtale := by
  have hξ := genericPoint_mem_of_nonempty U hU
  let u : (U : Scheme.{0}) := ⟨genericPoint M, hξ⟩
  have h1 : ((U.ι ≫ f).stalkMap u).hom.FormallyEtale := by
    have hu := FormallyUnramified.stalkMap (U.ι ≫ f) u
    have hs : ((U.ι ≫ f).stalkMap u).hom.FormallySmooth :=
      Scheme.Hom.mem_smoothLocus.mp ((U.ι ≫ f).smoothLocus_eq_top.ge (Set.mem_univ u))
    algebraize [((U.ι ≫ f).stalkMap u).hom]
    exact Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr ⟨hu, hs⟩
  rw [Scheme.Hom.stalkMap_comp] at h1
  have h2 : (f.stalkMap (genericPoint M)).hom.FormallyEtale := by
    have e : f.stalkMap (genericPoint M) =
        (f.stalkMap (U.ι u) ≫ U.ι.stalkMap u) ≫ inv (U.ι.stalkMap u) := by simp; rfl
    rw [e]
    exact RingHom.FormallyEtale.comp h1 (formallyEtale_of_isIso _)
  have hiso : ∀ {x : W} (h : x ⤳ genericPoint W), x = genericPoint W →
      IsIso (W.presheaf.stalkSpecializes h) := by
    rintro x h rfl
    rw [TopCat.Presheaf.stalkSpecializes_refl]
    infer_instance
  have key : ∀ h : f (genericPoint M) ⤳ genericPoint W,
      (W.presheaf.stalkSpecializes h ≫ f.stalkMap (genericPoint M)).hom.FormallyEtale := by
    intro h
    haveI := hiso h (map_genericPoint f)
    exact RingHom.FormallyEtale.comp (formallyEtale_of_isIso _) h2
  exact key _

theorem injective_of_isBaseChange_field {A B M N : Type*} [Field A] [CommRing B] [Nontrivial B]
    [Algebra A B] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [Module B N]
    [IsScalarTower A B N] {φ : M →ₗ[A] N} (hφ : IsBaseChange B φ) : Function.Injective φ := by
  have e : (φ : M → N) = hφ.equiv ∘ ((Algebra.linearMap A B).rTensor M) ∘
      (TensorProduct.lid A M).symm := by
    funext m
    simp [hφ.equiv_tmul]
  rw [e]
  refine hφ.equiv.injective.comp ((Module.Flat.rTensor_preserves_injective_linearMap _
    (algebraMap A B).injective).comp (TensorProduct.lid A M).symm.injective)

theorem ratPull_ne_zero : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] [IsLocallyNoetherian M]
    [IsLocallyNoetherian W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f] (n : ℕ)
    [SmoothOfRelativeDimension n p] [SmoothOfRelativeDimension n (f ≫ p)] (U : M.Opens),
    Etale (U.ι ≫ f) → (U : Set M).Nonempty → ∀ η : RatForms p n, η ≠ 0 →
      GlobalTheory.EtaleKlt.ratPull p f n η ≠ 0 := by
  intro M W _ _ _ _ p f _ n _ _ U hf hU η hη h0
  have hE := formallyEtale_functionFieldMap f U hf hU
  letI := (Cartier.constFn p).toAlgebra
  letI := (Cartier.constFn (f ≫ p)).toAlgebra
  letI := (functionFieldMap f).toAlgebra
  haveI : IsScalarTower ℂ W.functionField M.functionField :=
    IsScalarTower.of_algebraMap_eq' (functionFieldMap_comp_constFn p f).symm
  haveI : Algebra.FormallyEtale W.functionField M.functionField := hE
  have hb := isBaseChange_exteriorPower
    (KaehlerDifferential.isBaseChange_of_formallyEtale ℂ W.functionField M.functionField) n
  exact hη (injective_of_isBaseChange_field hb (h0.trans (map_zero _).symm))

end GlobalTheory.EtaleKlt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RdZeroOfPetAt
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.PetDef

open MeasureTheory Formalism.L2.Theta Formalism.BasicNotions.TH ReciprocityTheory.ChartRestriction.G.FD Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped Topology TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {D : D7} {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}

theorem adelAut_of_gamma {V : HSp D} {X : Comp → Data E r} {dict : GA D V → Σ k, Frame (X k).Ψ r}
    {mu : GA D V → ℂ} {Kf : Subgroup (GA D V)} {th : ∀ c, (X c).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
    {hr : V.rank = r} (hχ : ∀ k la γ, γ ∈ (X k).Γ → (X k).χ la γ = 1) (hd : DictIsUnif V dict Kf th hr)
    (hm : MuUnit V dict mu) (hL : DictLoc V dict) (hmc : Continuous mu) : AdelAut V dict mu := by
  intro la P hP
  refine ⟨fun γ hγ g => ?_, ?_⟩
  · obtain ⟨γ', hγ', he⟩ := hd.1 γ hγ g
    have hE := (eqv_holSub X la (holCusp_mem_holSub X la hP)).2 (dict g).1 γ' hγ' (dict g).2 (hd.2.2.2.1 g)
    show mu (γ * g) * P (dict (γ * g)).1 (dict (γ * g)).2 = mu g * P (dict g).1 (dict g).2
    rw [he, hm.1, hm.2.2.1 γ hγ, one_mul]
    show mu g * P (dict g).1 (lact γ' (dict g).2) = _
    rw [hE, hχ _ _ _ hγ', one_mul]
  · rw [continuous_iff_continuousAt]
    intro g₀
    obtain ⟨N, hN, k, x, hx, hs⟩ := hL g₀
    have hsec : (X k).IsSec (la k) (P k) := (hP k).1.1
    have hPc : ContinuousOn (P k) (X k).dom := hsec.1.continuousOn
    have hc : ContinuousOn (fun g => mu g * P k (x g)) N :=
      hmc.continuousOn.mul (hPc.comp hx fun g hg => (hs g hg).1)
    have heq : (fun g => mu g * P k (x g)) =ᶠ[𝓝 g₀] adel V dict mu P := by
      filter_upwards [hN] with g hg
      obtain ⟨hd', γ, hγ, he⟩ := hs g hg
      show mu g * P k (x g) = mu g * P (dict g).1 (dict g).2
      rw [he]
      show mu g * P k (x g) = mu g * P k (lact γ (x g))
      rw [hsec.2.2 γ hγ (x g) hd', hχ _ _ _ hγ, one_mul]
    exact (hc.continuousAt hN).congr heq

end Gen

section Cover

variable {D : D7} {T : Core D} {j : ℕ}

theorem dictLoc_of_good (Y : Deep T j) {e : ℕ} {o : ℝ} (h : Y.Good e o) (σ : Y.d.c₂.F →+* ℂ)
    (hσ : GoodEmb Y.d.c₂ σ) : ∃ th hr, DictIsUnif (D.sp.W j) (Y.dict σ) Y.Kf th hr ∧ DictLoc (D.sp.W j) (Y.dict σ) := by
  obtain ⟨th, hr, hth, hd⟩ := h.dictU σ hσ
  refine ⟨th, hr, hd, ?_⟩
  have hN : 0 < D.host.g 0 * D.host.g 1 * Y.d.pd := by
    rw [h.pd]
    exact Nat.mul_pos (Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos) (pow_pos (by norm_num) _)
  have hK : Y.Kf ≤ GfC (D.sp.W j) := fun k hk => ((h.levelK k).1 hk).1
  exact GlobalTheory.DictLocTest.locClause_of_unif_places hd hK (GlobalTheory.T.principalLevel_mul_archimedean_mem_nhds D _ _ Y.Kf hN h.levelK) (fun c τ => ⟨_, hth c τ⟩)

theorem muUnit_one (Y : Deep T j) {e : ℕ} {o : ℝ} (h : Y.Good e o) (σ : Y.d.c₂.F →+* ℂ) (hσ : GoodEmb Y.d.c₂ σ) :
    MuUnit (D.sp.W j) (Y.dict σ) (fun _ => (1 : ℂ)) :=
  ⟨fun _ _ => (mul_one 1).symm, fun _ => norm_one, fun _ _ => rfl, h.unit σ hσ⟩

theorem adelAut_good (Y : Deep T j) {e : ℕ} {o : ℝ} (h : Y.Good e o) (σ : Y.d.c₂.F →+* ℂ) (hσ : GoodEmb Y.d.c₂ σ) :
    AdelAut (D.sp.W j) (Y.dict σ) (fun _ => (1 : ℂ)) := by
  obtain ⟨th, hr, hd, hL⟩ := dictLoc_of_good Y h σ hσ
  exact adelAut_of_gamma (fun k la γ hγ => GlobalTheory.CovTop.Model.chi_eq_one h σ hσ k la γ hγ) hd (muUnit_one Y h σ hσ) hL
    continuous_const

theorem aeDom_good (Y : Deep T j) {e : ℕ} {o : ℝ} (h : Y.Good e o) (σ : Y.d.c₂.F →+* ℂ) (hσ : GoodEmb Y.d.c₂ σ) :
    AeDom Y.U σ (D.sp.W j) (Y.dict σ) (fun _ => (1 : ℂ)) := by
  obtain ⟨th, hr, hd, -⟩ := dictLoc_of_good Y h σ hσ
  obtain ⟨hP, hV⟩ := GlobalTheory.FinalJoin2.volPairEx_and_finVol D (D.sp.W j) (D.sp.W_sig j)
  exact aeDom_of_aut Y.d.Xo₂ Y.d.c₂ (adelAut_good Y h σ hσ) (quotSupp_of _ hV hP) (muUnit_one Y h σ hσ) hd

theorem rd_zero_of_petAt (Y : Deep T j) {e : ℕ} {o : ℝ} (h : Y.Good e o) (σ : Y.d.c₂.F →+* ℂ)
    (hσ : GoodEmb Y.d.c₂ σ) (G : WTZ D.host.E) (f : Rul Y.d.Xo₂ Y.d.c₂) (hf : f ∈ GlobalTheory.AllWt.cuspW Y.d.Xo₂ Y.d.c₂ Y.U G)
    (h0 : GlobalTheory.AllWt.petAt (Y.U σ) (xiR D) (D.sp.W j) (Y.dict σ) (muQ1 (D.sp.W j)) G f = 0) :
    ∀ k, ∀ z ∈ ((Y.U σ).X k).dom, rdU (Y.U σ) f k z = 0 := by
  have hP : rdU (Y.U σ) f ∈ holSub (Y.U σ).X (GlobalTheory.AllWt.modelWt (Y.U σ) G) := (GlobalTheory.AllWt.mem_cuspW.1 hf).2 σ hσ
  obtain ⟨th, hr, hd, -⟩ := dictLoc_of_good Y h σ hσ
  have hfin := GlobalTheory.AllWt.petE_ne_top (D.sp.W j) (Y.dict σ) (muQ1 (D.sp.W j)) prob_le_one hd.2.2.2.1 hP
  have hE : GlobalTheory.AllWt.petE (D.sp.W j) (Y.dict σ) (muQ1 (D.sp.W j)) (GlobalTheory.AllWt.modelWt (Y.U σ) G) (rdU (Y.U σ) f) = 0 := by
    unfold GlobalTheory.AllWt.petAt at h0
    rcases mul_eq_zero.1 h0 with h1 | h1
    · exact absurd h1 (GlobalTheory.AllWt.lieFacZ_pos _ _).ne'
    · exact ((ENNReal.toReal_eq_zero_iff _).1 h1).resolve_right hfin
  have hmeas := aesm_of_holSub (adelMeas_of_aut Y.d.Xo₂ Y.d.c₂ (U := Y.U) (σ := σ) (adelAut_good Y h σ hσ)) _ hP
  have heqn : (fun q : AutQ (D.sp.W j) => GlobalTheory.AllWt.ptN (GlobalTheory.AllWt.modelWt (Y.U σ) G) (rdU (Y.U σ) f) (Y.dict σ q.out)) =
      fun q => ‖onQ (D.sp.W j) (adel (D.sp.W j) (Y.dict σ) (fun _ => (1 : ℂ)) (rdU (Y.U σ) f)) q‖ := by
    funext q
    show ((Y.U σ).X _).pnorm _ _ _ = ‖(1 : ℂ) * rdU (Y.U σ) f _ _‖
    rw [pnorm_eq_of_unit _ _ _ _ (h.unit σ hσ q.out), one_mul]
  have hz : onQ (D.sp.W j) (adel (D.sp.W j) (Y.dict σ) (fun _ => (1 : ℂ)) (rdU (Y.U σ) f)) =ᵐ[muQ1 (D.sp.W j)] 0 := by
    have h2 : eLpNorm (onQ (D.sp.W j) (adel (D.sp.W j) (Y.dict σ) (fun _ => (1 : ℂ)) (rdU (Y.U σ) f))) 2
        (muQ1 (D.sp.W j)) = 0 := by
      rw [← eLpNorm_norm]
      unfold GlobalTheory.AllWt.petE at hE
      rw [heqn] at hE
      exact hE
    exact (eLpNorm_eq_zero_iff hmeas two_ne_zero).1 h2
  exact aeDom_good Y h σ hσ _ _ hP hz

end Cover

theorem nrm_eq_zero : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o →
    2 < Module.finrank ℚ D.host.E / 2 → ∀ (G : WTZ D.host.E) (v : InfinitePlace Y.d.c₂.F) (x : Y.V G),
    Y.nrm G v.embedding x = 0 → x = 0 := by
  intro D T j Y e o h _ G v x h0
  have hσ := goodEmb_goodOf Y.d.c₂ v.embedding
  exact GlobalTheory.T.eq_zero_of_restrictions_vanish D T j Y e o h _ hσ G x (rd_zero_of_petAt Y h _ hσ G x x.2 h0)

end GlobalTheory.PetDef
end
end

