import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0020
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.OneSTr
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FibreFactorHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0025
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0021
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0022

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuotientMeasureByInvariantSubgroupStatement
section
open MeasureTheory Topology
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_measure_by_invariant_subgroup : ∀ (V A : Type) [AddCommGroup V] [AddCommGroup A] [MeasurableSpace V] [MeasurableSpace A] [MeasurableAdd₂ V] [MeasurableAdd₂ A] [MeasurableNeg A] [MeasurableNeg V] (μ : Measure V) (lam : Measure A) [SFinite μ] [SFinite lam] [μ.IsAddRightInvariant] [lam.IsAddRightInvariant] (j : A →+ V), Measurable j → ∀ f : V → A, Measurable f → (∀ v a, f (v + j a) = f v) → ∀ K : Set A, MeasurableSet K → lam K ≠ 0 → lam K ≠ ⊤ → ∀ ψ : V → ℝ≥0∞, Measurable ψ → ∫⁻ v, ψ (v + j (f v)) ∂μ = ∫⁻ v, ψ v ∂μ := by
  first | exact @GlobalTheory.CompanionTheory.Shear.lintegral_shear_eq | exact GlobalTheory.CompanionTheory.Shear.lintegral_shear_eq | (intros; apply GlobalTheory.CompanionTheory.Shear.lintegral_shear_eq <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationAdd
section
open CrystallineSemistableComparison.Pb.Kap

namespace GlobalTheory.CompanionTheory.KapRho

theorem rho_add {Λ A B K : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K]
    (C : Chain.{1} Λ A B K) {j : ℕ} (x y : ∀ n, C.S n j) (f g : Module.Dual K (C.V j) →+ B) :
    C.Rho x f → C.Rho y g → C.Rho (x + y) (f + g) := by
  rintro ⟨hf, e₁, z₁, hz₁, hb₁⟩ ⟨hg, e₂, z₂, hz₂, hb₂⟩
  refine ⟨fun k φ => by simp only [AddMonoidHom.add_apply, hf, hg, mul_add], e₁ + e₂,
    ((C.ℓ : A) ^ e₂) • z₁ + ((C.ℓ : A) ^ e₁) • z₂, fun n => ?_, fun {m} bs => ?_⟩
  · simp only [map_add, map_smul, hz₁, hz₂, Pi.add_apply]
    rw [pow_add]
    module
  · simp only [AddMonoidHom.add_apply, add_smul, Finset.sum_add_distrib, map_add,
      LinearMap.map_smulₛₗ, map_pow, map_natCast, ← hb₁ bs, ← hb₂ bs]
    rw [pow_add]
    module

end GlobalTheory.CompanionTheory.KapRho
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationCupProduct
section
set_option backward.isDefEq.respectTransparency false

open CrystallineSemistableComparison.Pb.Kap

namespace GlobalTheory.CompanionTheory.KapRho

theorem semilinear_eq_sum_coord {K B : Type*} {V : Type*} [Field K] [CommRing B] [AddCommGroup V]
    [Module K V] (o : K →+* B) (f : Module.Dual K V →+ B)
    (hf : ∀ (k : K) φ, f (k • φ) = o k * f φ) {m : ℕ} (bs : Module.Basis (Fin m) K V)
    (φ : Module.Dual K V) : f φ = ∑ s, f (bs.coord s) * o (φ (bs s)) := by
  have hφ : φ = ∑ s, φ (bs s) • bs.coord s := by
    refine bs.ext fun t => ?_
    simp [LinearMap.sum_apply, Finsupp.single_apply]
  conv_lhs => rw [hφ]
  rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [hf, mul_comm]

theorem rho_cup :
    ∀ {Λ A B K : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K] (C : Chain.{1} Λ A B K)
      (hC : C.Good) (P : Cup C), P.Good → ∀ {i j : ℕ} (x : ∀ n, C.S n i) (y : ∀ n, C.S n j)
      (f : Module.Dual K (C.V i) →+ B) (g : Module.Dual K (C.V j) →+ B)
      (h : Module.Dual K (C.V (i + j)) →+ B), C.Rho x f → C.Rho y g →
      C.Rho (fun n => P.cS n i j (x n) (y n)) h →
      ∀ {m m' : ℕ} (bs : Module.Basis (Fin m) K (C.V i)) (bs' : Module.Basis (Fin m') K (C.V j))
        (φ : Module.Dual K (C.V (i + j))),
        h φ = ∑ s, ∑ s', f (bs.coord s) * g (bs'.coord s') *
          C.o (φ (P.cV i j (bs s) (bs' s'))) := by
  intro Λ A B K _ _ _ _ C hC P hP i j x y f g h hf hg hh m m' bs bs' φ
  obtain ⟨-, e, z, hzr, hzb⟩ := hf
  obtain ⟨-, e', w, hwr, hwb⟩ := hg
  obtain ⟨hh1, e'', u, hur, hub⟩ := hh
  haveI := hC.fin (i + j)
  let b := Module.finBasis K (C.V (i + j))
  have hv : ∀ n, C.red n (i + j) (P.cZ i j z w) =
      ((C.ℓ : A) ^ (e + e')) • C.r n (i + j) (P.cS n i j (x n) (y n)) := by
    intro n
    rw [hP.red, hzr, hwr, hP.r, map_smul, LinearMap.map_smul₂, smul_smul, pow_add, mul_comm]
  have hd : C.b (i + j) (((C.ℓ : A) ^ (e + e')) • u - ((C.ℓ : A) ^ e'') • P.cZ i j z w) = 0 := by
    refine hC.sep _ _ fun n => ?_
    have hu := hur n
    simp only at hu
    rw [map_sub, map_smul, map_smul, hu, hv n, smul_smul, smul_smul, mul_comm, sub_self]
  have key : ((C.ℓ : B) ^ (e + e')) • C.b (i + j) u =
      ((C.ℓ : B) ^ e'') • C.b (i + j) (P.cZ i j z w) := by
    rw [map_sub, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, sub_eq_zero] at hd
    simpa only [map_pow, map_natCast] using hd
  let c : Fin (Module.finrank K (C.V (i + j))) → B := fun t =>
    ∑ s, ∑ s', f (bs.coord s) * g (bs'.coord s') *
      C.o (b.coord t (P.cV i j (bs s) (bs' s')))
  have hμ : ∀ s s', P.cW i j (C.μ i (bs s)) (C.μ j (bs' s')) =
      ∑ t, C.o (b.coord t (P.cV i j (bs s) (bs' s'))) • C.μ (i + j) (b t) := by
    intro s s'
    rw [← hP.μ]
    conv_lhs => rw [← b.sum_repr (P.cV i j (bs s) (bs' s'))]
    rw [map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [LinearMap.map_smulₛₗ, Module.Basis.coord_apply]
  have hcup : P.cW i j (∑ s, f (bs.coord s) • C.μ i (bs s))
      (∑ s', g (bs'.coord s') • C.μ j (bs' s')) = ∑ t, c t • C.μ (i + j) (b t) := by
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, hμ, c,
      Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    symm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s' _ => Finset.sum_congr rfl fun t _ => ?_
    congr 1
    ring
  have hcoef : ∑ t, h (b.coord t) • C.μ (i + j) (b t) = ∑ t, c t • C.μ (i + j) (b t) := by
    have hu : IsUnit ((C.ℓ : B) ^ (e + e') * (C.ℓ : B) ^ e'') :=
      (hC.unit.pow _).mul (hC.unit.pow _)
    refine (hu.smul_left_cancel).1 ?_
    rw [hP.b, ← hub b, ← hzb bs, ← hwb bs', map_smul, LinearMap.map_smul₂, hcup, smul_smul,
      smul_smul, smul_smul] at key
    have hl : (C.ℓ : B) ^ e'' * (C.ℓ : B) ^ e' * (C.ℓ : B) ^ e =
        (C.ℓ : B) ^ (e + e') * (C.ℓ : B) ^ e'' := by ring
    rwa [hl] at key
  have hc : ∀ t, h (b.coord t) = c t := by
    obtain ⟨g₀, -, hg₀⟩ := hC.basis (i + j) b (∑ t, c t • C.μ (i + j) (b t))
    have h1 := hg₀ c rfl
    have h2 := hg₀ (fun t => h (b.coord t)) hcoef.symm
    exact fun t => congrFun (h2.trans h1.symm) t
  have hφ : ∀ s s', C.o (φ (P.cV i j (bs s) (bs' s'))) =
      ∑ t, C.o (b.coord t (P.cV i j (bs s) (bs' s'))) * C.o (φ (b t)) := by
    intro s s'
    conv_lhs => rw [← b.sum_repr (P.cV i j (bs s) (bs' s'))]
    simp only [map_sum, map_smul, smul_eq_mul, map_mul, Module.Basis.coord_apply]
  refine (semilinear_eq_sum_coord C.o h hh1 b φ).trans ?_
  simp only [hc, c, hφ, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s' _ => Finset.sum_congr rfl fun t _ => ?_
  rw [mul_assoc]

end GlobalTheory.CompanionTheory.KapRho
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationFunctorial
section
open CrystallineSemistableComparison.Pb.Kap

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.KapRhoHom

private theorem dual_expand {K B : Type} {V : Type*} [Field K] [CommRing B] [AddCommGroup V] [Module K V]
    (o : K →+* B) (f : Module.Dual K V →+ B) (hf : ∀ (k : K) φ, f (k • φ) = o k * f φ)
    {m : ℕ} (bs : Module.Basis (Fin m) K V) (φ : Module.Dual K V) :
    f φ = ∑ s, f (bs.coord s) * o (φ (bs s)) := by
  have hφ : φ = ∑ s, φ (bs s) • bs.coord s := by
    refine bs.ext fun t => ?_
    simp [LinearMap.sum_apply, Finsupp.single_apply]
  conv_lhs => rw [hφ]
  rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [hf, mul_comm]

theorem rho_hom :
    ∀ {Λ A B K Λ' A' B' : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K] [CommRing Λ']
      [CommRing A'] [CommRing B'] (C : Chain.{1} Λ A B K) (C' : Chain.{1} Λ' A' B' K)
      (h : Hom C C'), C.Good → C'.Good → h.Good → ∀ {j : ℕ} (x : ∀ n, C.S n j)
      (f : Module.Dual K (C.V j) →+ B), C.Rho x f →
        C'.Rho (fun n => h.fS n j (x n)) (h.tr j f) := by
  intro Λ A B K Λ' A' B' _ _ _ _ _ _ _ C C' h hC hC' hh j x f hR
  obtain ⟨hs, e, z, hz, hW⟩ := hR
  have htr : ∀ φ : Module.Dual K (C'.V j),
      h.tr j f φ = h.sB (f (Module.Dual.transpose (R := K) (h.fV j) φ)) := fun φ => rfl
  refine ⟨fun k φ => ?_, e, h.fZ j z, fun n => ?_, ?_⟩
  · rw [htr, htr, map_smul, hs, map_mul, hh.o]
  · rw [← hh.red, hz, map_smulₛₗ, hh.r, map_pow, map_natCast, hh.ℓ]
  · intro m bs'
    haveI := hC.fin j
    have bs := Module.finBasis K (C.V j)
    have hE := congrArg (h.fW j) (hW bs)
    rw [hh.b, map_smulₛₗ, map_sum, map_pow, map_natCast] at hE
    rw [← hE, hh.ℓ]
    congr 1
    have hexp : ∀ t, h.tr j f (bs'.coord t) =
        ∑ s, h.sB (f (bs.coord s)) * C'.o (bs'.coord t (h.fV j (bs s))) := by
      intro t
      rw [htr, dual_expand C.o f hs bs, map_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [map_mul, hh.o]
      rfl
    have hμ : ∀ s, C'.μ j (h.fV j (bs s)) =
        ∑ t, C'.o (bs'.coord t (h.fV j (bs s))) • C'.μ j (bs' t) := by
      intro s
      conv_lhs => rw [← bs'.sum_repr (h.fV j (bs s))]
      rw [map_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [map_smulₛₗ]
      rfl
    calc ∑ t, h.tr j f (bs'.coord t) • C'.μ j (bs' t)
        = ∑ t, ∑ s, (h.sB (f (bs.coord s)) * C'.o (bs'.coord t (h.fV j (bs s)))) • C'.μ j (bs' t) := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [hexp, Finset.sum_smul]
      _ = ∑ s, ∑ t, (h.sB (f (bs.coord s)) * C'.o (bs'.coord t (h.fV j (bs s)))) • C'.μ j (bs' t) :=
          Finset.sum_comm
      _ = ∑ s, h.fW j (f (bs.coord s) • C.μ j (bs s)) := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [map_smulₛₗ, hh.μ, hμ, Finset.smul_sum]
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [mul_smul]

end GlobalTheory.CompanionTheory.KapRhoHom
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationSmul
section
open CrystallineSemistableComparison.Pb.Kap

namespace GlobalTheory.CompanionTheory.KapChain

theorem rho_smul : ∀ {Λ A B K : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K] (C : Chain.{1} Λ A B K) {j : ℕ}
    (c : Λ) (x : ∀ n, C.S n j) (f : Module.Dual K (C.V j) →+ B), C.Rho x f →
    C.Rho (c • x) ((AddMonoidHom.mulLeft (C.ι (C.lam c))).comp f) := by
  intro Λ A B K _ _ _ _ C j c x f hf
  obtain ⟨h1, e, z, h2, h3⟩ := hf
  refine ⟨?_, e, C.lam c • z, ?_, ?_⟩
  · intro k φ
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft, h1]
    ring
  · intro n
    rw [map_smul, h2 n, Pi.smul_apply, LinearMap.map_smulₛₗ, smul_comm]
  · intro m bs
    rw [LinearMap.map_smulₛₗ, ← h3 bs]
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft, mul_smul]
    rw [← Finset.smul_sum, smul_comm]

end GlobalTheory.CompanionTheory.KapChain
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationUnique
section
open Module CrystallineSemistableComparison.Pb.Kap

namespace GlobalTheory.CompanionTheory.KapUniq

theorem eq_of_unit_smul_combination {K B V M : Type*} [Field K] [CommRing B] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [AddCommGroup M] [Module B M]
    (o : K →+* B) (μ : V → M) (c : B) (hc : IsUnit c)
    (hind : ∀ (m : ℕ) (bs : Basis (Fin m) K V) (g : Fin m → B),
      ∑ s, g s • μ (bs s) = 0 → ∀ s, g s = 0)
    (f f' : Dual K V →+ B)
    (hf : ∀ (k : K) (φ : Dual K V), f (k • φ) = o k * f φ)
    (hf' : ∀ (k : K) (φ : Dual K V), f' (k • φ) = o k * f' φ)
    (h : ∀ (m : ℕ) (bs : Basis (Fin m) K V),
      c • ∑ s, (f (bs.coord s) - f' (bs.coord s)) • μ (bs s) = 0) :
    f = f' := by
  classical
  let bs := Module.finBasis K V
  have h0 : ∑ s, (f (bs.coord s) - f' (bs.coord s)) • μ (bs s) = 0 := by
    obtain ⟨u, rfl⟩ := hc
    have := congrArg (fun x => ((u⁻¹ : Bˣ) : B) • x) (h _ bs)
    simpa [smul_smul] using this
  have hco : ∀ s, f (bs.coord s) = f' (bs.coord s) :=
    fun s => sub_eq_zero.mp (hind _ bs _ h0 s)
  have key : ∀ F : Dual K V →+ B, (∀ (k : K) (φ : Dual K V), F (k • φ) = o k * F φ) →
      ∀ φ : Dual K V, F φ = ∑ s, F (bs.coord s) * o (φ (bs s)) := by
    intro F hF φ
    have e : ∑ s, φ (bs s) • bs.coord s = φ := bs.sum_dual_apply_smul_coord φ
    calc F φ = F (∑ s, φ (bs s) • bs.coord s) := by rw [e]
      _ = _ := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun s _ => by rw [hF, mul_comm]
  ext φ
  rw [key f hf, key f' hf']
  exact Finset.sum_congr rfl fun s _ => by rw [hco]

theorem rho_unique {Λ A B K : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K]
    (C : Chain.{1} Λ A B K) (hC : C.Good) {j : ℕ} (x : ∀ n, C.S n j)
    (f f' : Module.Dual K (C.V j) →+ B) : C.Rho x f → C.Rho x f' → f = f' := by
  rintro ⟨hfs, e, z, hz, hzb⟩ ⟨hfs', e', z', hz', hzb'⟩
  haveI := hC.fin j
  have hw : C.b j (((C.ℓ : A) ^ e) • z' - ((C.ℓ : A) ^ e') • z) = 0 := by
    apply hC.sep
    intro n
    rw [map_sub, map_smul, map_smul, hz n, hz' n, smul_smul, smul_smul, mul_comm, sub_self]
  have hb : ∀ (a : A) (y : C.Z j), C.b j (a • y) = C.ι a • C.b j y :=
    fun a y => (C.b j).map_smulₛₗ a y
  refine (eq_of_unit_smul_combination C.o (C.μ j) ((C.ℓ : B) ^ (e + e')) (hC.unit.pow _) ?_
    f' f hfs' hfs ?_).symm
  · intro m bs g hg s
    obtain ⟨g0, _, hu⟩ := hC.basis j bs 0
    have h1 := hu g hg.symm
    have h2 := hu 0 (by simp)
    exact congrFun (h1.trans h2.symm) s
  · intro m bs
    have h := hw
    rw [map_sub, hb, hb, ← hzb bs, ← hzb' bs] at h
    simp only [map_pow, map_natCast, smul_smul] at h
    simp_rw [sub_smul, Finset.sum_sub_distrib, smul_sub]
    rw [← h, pow_add, mul_comm ((C.ℓ : B) ^ e') ((C.ℓ : B) ^ e)]

end GlobalTheory.CompanionTheory.KapUniq
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationUnitClass
section
open CrystallineSemistableComparison.Pb.Kap

namespace GlobalTheory.CompanionTheory.KapUnit

theorem rho_one_eval : ∀ {Λ A B K : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K] (C : Chain.{1} Λ A B K) (hC : C.Good) (P : Cup C), P.Good → ∀ h : Module.Dual K (C.V 0) →+ B, C.Rho P.oneS h → ∀ φ : Module.Dual K (C.V 0), h φ = C.o (φ P.oneV) := by
  intro Λ A B K _ _ _ _ C hC P hP h hR φ
  obtain ⟨hsem, e, z, hz, hb⟩ := hR
  have hw : C.b 0 z = ((C.ℓ : B) ^ e) • C.μ 0 P.oneV := by
    have h0 : C.b 0 (z - ((C.ℓ : A) ^ e) • P.oneZ) = 0 := hC.sep 0 _ (fun n => by
      rw [map_sub, map_smul, hP.one_r, hz, sub_self])
    rw [map_sub, map_smulₛₗ, hP.one_b, sub_eq_zero] at h0
    rw [h0]
    simp
  haveI := hC.fin 0
  let bs := Module.finBasis K (C.V 0)
  have h1 := hb bs
  rw [hw] at h1
  have h2 : ∑ s, h (bs.coord s) • C.μ 0 (bs s) = C.μ 0 P.oneV := by
    obtain ⟨u, hu⟩ := hC.unit.pow e
    rw [← hu] at h1
    have h1' := congrArg (fun w => ((u⁻¹ : Bˣ) : B) • w) h1
    simpa only [smul_smul, Units.inv_mul, one_smul] using h1'
  have h3 : C.μ 0 P.oneV = ∑ s, C.o (bs.coord s P.oneV) • C.μ 0 (bs s) := by
    conv_lhs => rw [← bs.sum_repr P.oneV]
    rw [map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_smulₛₗ]
    rfl
  have h4 : (fun s => h (bs.coord s)) = fun s => C.o (bs.coord s P.oneV) :=
    (hC.basis 0 bs (C.μ 0 P.oneV)).unique h2.symm h3
  have h5 : φ = ∑ s, φ (bs s) • bs.coord s := by
    refine bs.ext fun t => ?_
    simp [Finset.sum_apply, Module.Basis.coord_apply, Finsupp.single_apply]
  have h6 : φ P.oneV = ∑ s, bs.coord s P.oneV * φ (bs s) := by
    conv_lhs => rw [← bs.sum_repr P.oneV]
    rw [map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_smul, smul_eq_mul]
    rfl
  rw [h6, map_sum]
  conv_lhs => rw [h5]
  rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [hsem, map_mul, mul_comm]
  exact congrArg (· * C.o (φ (bs s))) (congrFun h4 s)

end GlobalTheory.CompanionTheory.KapUnit
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RegularizedExponentialSum
section
open Filter Topology
open scoped Classical

namespace GlobalTheory.CompanionTheory.ExpSums

theorem tendsto_one_add_pow_mul_pow {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) (N : ℕ) :
    Tendsto (fun n : ℕ => (1 + (n : ℝ)) ^ N * t ^ n) atTop (𝓝 0) := by
  have ht : |t| < 1 := by rw [abs_of_nonneg h0]; exact h1
  have hlim : Tendsto (fun n : ℕ => (2 : ℝ) ^ N * ((n : ℝ) ^ N * t ^ n)) atTop (𝓝 0) := by
    have h := (tendsto_pow_const_mul_const_pow_of_abs_lt_one N ht).const_mul ((2 : ℝ) ^ N)
    rwa [mul_zero] at h
  refine squeeze_zero' (Filter.Eventually.of_forall fun n => mul_nonneg (by positivity) (pow_nonneg h0 n)) ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hle : (1 + (n : ℝ)) ^ N ≤ (2 * (n : ℝ)) ^ N := by
    gcongr
    linarith
  calc (1 + (n : ℝ)) ^ N * t ^ n ≤ (2 * (n : ℝ)) ^ N * t ^ n :=
        mul_le_mul_of_nonneg_right hle (pow_nonneg h0 n)
    _ = (2 : ℝ) ^ N * ((n : ℝ) ^ N * t ^ n) := by ring

theorem expSum_holds : PositivityTheory.Rg.BcB.F.ExpSum := by
  intro ι _ c lam ρ C N hρ hbound μ hμ
  obtain ⟨d, hd⟩ : ∃ d : ℂ → ℂ, ∀ ν, d ν = ∑ i with lam i = ν, c i := ⟨_, fun _ => rfl⟩
  rw [← hd]
  obtain ⟨S, hS⟩ : ∃ S : Finset ℂ, S = Finset.univ.image lam := ⟨_, rfl⟩
  by_cases hμS : μ ∉ S
  · rw [hd]
    refine Finset.sum_eq_zero fun i hi => absurd ?_ hμS
    rw [hS, ← (Finset.mem_filter.mp hi).2]
    exact Finset.mem_image_of_mem lam (Finset.mem_univ i)
  push_neg at hμS
  have hmaps : ∀ i ∈ (Finset.univ : Finset ι), lam i ∈ S := fun i _ => by
    rw [hS]; exact Finset.mem_image_of_mem lam (Finset.mem_univ i)
  have hsum : ∀ k : ℕ, ∑ i, c i * lam i ^ k = ∑ ν ∈ S, d ν * ν ^ k := by
    intro k
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [hd, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [(Finset.mem_filter.mp hi).2]
  obtain ⟨e, -⟩ : ∃ e : Fin S.card ≃ S, e = S.equivFin.symm := ⟨_, rfl⟩
  obtain ⟨α, hα⟩ : ∃ α : Fin S.card → ℂ, ∀ k, α k = (e k : ℂ) := ⟨_, fun _ => rfl⟩
  have hinj : Function.Injective α := by
    intro a b hab
    rw [hα, hα] at hab
    exact e.injective (Subtype.val_injective hab)
  have hpow : ∀ n : ℕ, ∑ k, d (α k) * α k ^ n = ∑ i, c i * lam i ^ n := by
    intro n
    rw [hsum n]
    simp only [hα]
    exact (Equiv.sum_comp e (fun x : S => d x * (x : ℂ) ^ n)).trans
      (Finset.sum_coe_sort S (fun ν => d ν * ν ^ n))
  obtain ⟨C', hC'⟩ := GlobalTheory.CompanionTheory.ExpSums.vandermonde_separation S.card α hinj
  obtain ⟨C1, hC1, hC'1⟩ : ∃ C1 : ℝ, 0 ≤ C1 ∧ C' ≤ C1 := ⟨max C' 0, le_max_right _ _, le_max_left _ _⟩
  obtain ⟨C2, hC2, hCC2⟩ : ∃ C2 : ℝ, 0 ≤ C2 ∧ C ≤ C2 := ⟨max C 0, le_max_right _ _, le_max_left _ _⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = ∑ s : Fin S.card, (1 + ((s : ℕ) : ℝ)) ^ N * ρ ^ (s : ℕ) := ⟨_, rfl⟩
  obtain ⟨K0, hK0⟩ := Filter.eventually_atTop.mp hbound
  have hK0' : ∀ k : ℕ, K0 ≤ k → ‖∑ i, c i * lam i ^ k‖ ≤ C2 * (1 + (k : ℝ)) ^ N * ρ ^ k := by
    intro k hk
    refine (hK0 k hk).trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCC2 (pow_nonneg (by positivity) N)) (pow_nonneg hρ k)
  obtain ⟨j, hj⟩ : ∃ j : Fin S.card, α j = μ := ⟨e.symm ⟨μ, hμS⟩, by rw [hα, Equiv.apply_symm_apply]⟩
  have key : ∀ m : ℕ, K0 ≤ m → ‖d μ‖ * ‖μ‖ ^ m ≤ C1 * (C2 * (1 + (m : ℝ)) ^ N * ρ ^ m * B) := by
    intro m hm
    have h1 := hC' (fun k => d (α k) * α k ^ m) j
    have hinner : ∀ s : Fin S.card,
        ∑ k, d (α k) * α k ^ m * α k ^ (s : ℕ) = ∑ i, c i * lam i ^ (m + (s : ℕ)) := by
      intro s
      rw [← hpow (m + (s : ℕ))]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [pow_add]
      ring
    simp only [hinner, hj, norm_mul, norm_pow] at h1
    have hT : 0 ≤ ∑ s : Fin S.card, ‖∑ i, c i * lam i ^ (m + (s : ℕ))‖ :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hsb : ∑ s : Fin S.card, ‖∑ i, c i * lam i ^ (m + (s : ℕ))‖ ≤
        C2 * (1 + (m : ℝ)) ^ N * ρ ^ m * B := by
      rw [hB, Finset.mul_sum]
      refine Finset.sum_le_sum fun s _ => ?_
      have hk := hK0' (m + (s : ℕ)) (le_trans hm (Nat.le_add_right m _))
      rw [Nat.cast_add] at hk
      have hbase : 1 + ((m : ℝ) + ((s : ℕ) : ℝ)) ≤ (1 + (m : ℝ)) * (1 + ((s : ℕ) : ℝ)) := by
        have hms : (0 : ℝ) ≤ (m : ℝ) * ((s : ℕ) : ℝ) := by positivity
        nlinarith
      have hle : (1 + ((m : ℝ) + ((s : ℕ) : ℝ))) ^ N ≤ (1 + (m : ℝ)) ^ N * (1 + ((s : ℕ) : ℝ)) ^ N := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (by positivity) hbase N
      calc ‖∑ i, c i * lam i ^ (m + (s : ℕ))‖
          ≤ C2 * (1 + ((m : ℝ) + ((s : ℕ) : ℝ))) ^ N * ρ ^ (m + (s : ℕ)) := hk
        _ ≤ C2 * ((1 + (m : ℝ)) ^ N * (1 + ((s : ℕ) : ℝ)) ^ N) * ρ ^ (m + (s : ℕ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle hC2) (pow_nonneg hρ _)
        _ = C2 * (1 + (m : ℝ)) ^ N * ρ ^ m * ((1 + ((s : ℕ) : ℝ)) ^ N * ρ ^ (s : ℕ)) := by
          rw [pow_add]
          ring
    calc ‖d μ‖ * ‖μ‖ ^ m ≤ C' * ∑ s : Fin S.card, ‖∑ i, c i * lam i ^ (m + (s : ℕ))‖ := h1
      _ ≤ C1 * ∑ s : Fin S.card, ‖∑ i, c i * lam i ^ (m + (s : ℕ))‖ :=
        mul_le_mul_of_nonneg_right hC'1 hT
      _ ≤ C1 * (C2 * (1 + (m : ℝ)) ^ N * ρ ^ m * B) := mul_le_mul_of_nonneg_left hsb hC1
  have hμpos : 0 < ‖μ‖ := lt_of_le_of_lt hρ hμ
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = ρ / ‖μ‖ := ⟨_, rfl⟩
  have ht0 : 0 ≤ t := by rw [ht]; exact div_nonneg hρ (norm_nonneg _)
  have ht1 : t < 1 := by rw [ht, div_lt_one hμpos]; exact hμ
  have hlim := (tendsto_one_add_pow_mul_pow ht0 ht1 N).const_mul (C1 * (C2 * B))
  rw [mul_zero] at hlim
  have hle : ∀ m : ℕ, K0 ≤ m → ‖d μ‖ ≤ C1 * (C2 * B) * ((1 + (m : ℝ)) ^ N * t ^ m) := by
    intro m hm
    have h := (le_div_iff₀ (pow_pos hμpos m)).mpr (key m hm)
    rw [ht, div_pow]
    calc ‖d μ‖ ≤ C1 * (C2 * (1 + (m : ℝ)) ^ N * ρ ^ m * B) / ‖μ‖ ^ m := h
      _ = C1 * (C2 * B) * ((1 + (m : ℝ)) ^ N * (ρ ^ m / ‖μ‖ ^ m)) := by ring
  have h0 : ‖d μ‖ ≤ 0 := ge_of_tendsto hlim (Filter.eventually_atTop.mpr ⟨K0, hle⟩)
  exact norm_le_zero_iff.mp h0

end GlobalTheory.CompanionTheory.ExpSums
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RetractBaseChangeKernelCompatibleStatement
section
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.retract_base_change_kernel_compatible : ∀ (R R' M A₀ A₁ B₀ B₁ : Type) [CommRing R] [CommRing R'] [Algebra R R'] [AddCommGroup M] [Module R M] [AddCommGroup A₀] [Module R A₀] [AddCommGroup A₁] [Module R A₁] [AddCommGroup B₀] [Module R' B₀] [AddCommGroup B₁] [Module R' B₁] (i : M →ₗ[R] R') (j : R' →ₗ[R] M) (d₀ : A₀ →ₗ[R] A₁) (d' : B₀ →ₗ[R'] B₁) (E₀ : R' ⊗[R] A₀ ≃ₗ[R'] B₀) (E₁ : R' ⊗[R] A₁ ≃ₗ[R'] B₁) (e : A₀), j ∘ₗ i = LinearMap.id → (∀ x, E₁ (d₀.baseChange R' x) = d' (E₀ x)) → (∀ r : R', r • E₀ (1 ⊗ₜ e) = 0 → r = 0) → (∀ z, d' z = 0 → ∃ r : R', r • E₀ (1 ⊗ₜ e) = z) → Function.Injective (fun m : M ↦ m ⊗ₜ[R] e) ∧ ∀ x : M ⊗[R] A₀, d₀.lTensor M x = 0 → ∃ m : M, m ⊗ₜ[R] e = x := by
  first | exact @GlobalTheory.CompanionTheory.Retract.constants_of_retract | exact GlobalTheory.CompanionTheory.Retract.constants_of_retract | (intros; apply GlobalTheory.CompanionTheory.Retract.constants_of_retract <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzLinearChangeStatement
section
open scoped Matrix SchwartzMap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_linear_change : ∀ (m n : ℕ) (c : ℂ) (a : Matrix (Fin n) (Fin n) ℂ), IsUnit a.det → ∀ φ : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ∃ ψ : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ⇑ψ = fun u => c * φ (Matrix.of u * a) := by
  first | exact @GlobalTheory.CompanionTheory.KlocopSw.exists_schwartz_rightMul | exact GlobalTheory.CompanionTheory.KlocopSw.exists_schwartz_rightMul | (intros; apply GlobalTheory.CompanionTheory.KlocopSw.exists_schwartz_rightMul <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SemidirectProductHomeomorphOfClosedComplementStatement
section
open MeasureTheory
open scoped NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semidirect_product_homeomorph_of_closed_complement : ∀ (Q : Type) [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [LocallyCompactSpace Q] [T2Space Q] [SecondCountableTopology Q] (N M : Subgroup Q), IsClosed (N : Set Q) → IsClosed (M : Set Q) → (∀ q, ∃ n ∈ N, ∃ m ∈ M, q = n * m) → (∀ x, x ∈ N → x ∈ M → x = 1) → ∃ Φ : (N × M) ≃ₜ Q, ∀ p, Φ p = (p.1 : Q) * (p.2 : Q) := by
  first | exact @GlobalTheory.CompanionTheory.TopGroup.homeomorph_prod_of_closed_complements | exact GlobalTheory.CompanionTheory.TopGroup.homeomorph_prod_of_closed_complements | (intros; apply GlobalTheory.CompanionTheory.TopGroup.homeomorph_prod_of_closed_complements <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SemistableModelRingIsDomainStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semistable_model_ring_isDomain : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (m r : ℕ), 1 ≤ r → r ≤ m → IsDomain (MvPolynomial (Fin m) O ⧸ Ideal.span {(∏ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < r), MvPolynomial.X i) - MvPolynomial.C ϖ}) := by
  first | exact @GlobalTheory.CompanionTheory.SemistableLocal.isDomain_quotient_prod_X_sub_C | exact GlobalTheory.CompanionTheory.SemistableLocal.isDomain_quotient_prod_X_sub_C | (intros; apply GlobalTheory.CompanionTheory.SemistableLocal.isDomain_quotient_prod_X_sub_C <;> assumption)
end

