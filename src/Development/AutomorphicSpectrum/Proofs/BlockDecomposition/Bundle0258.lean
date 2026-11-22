import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0253
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubMemSpanOfEtale
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.LiftFlat

theorem flat_of_eval₂Hom_etale {Λ D : Type} [CommRing Λ] [CommRing D] (i : Λ →+* D) {d : ℕ}
    (t : Fin d → D) (het : (MvPolynomial.eval₂Hom i t).Etale) : i.Flat := by
  have h1 : (MvPolynomial.eval₂Hom i t).Flat := by
    letI := (MvPolynomial.eval₂Hom i t).toAlgebra
    haveI : Algebra.Etale (MvPolynomial (Fin d) Λ) D := het
    exact Algebra.Smooth.flat (MvPolynomial (Fin d) Λ) D
  have h2 : (MvPolynomial.C : Λ →+* MvPolynomial (Fin d) Λ).Flat := by
    rw [← MvPolynomial.algebraMap_eq, RingHom.flat_algebraMap_iff]
    infer_instance
  have h3 := RingHom.Flat.comp h2 h1
  rwa [MvPolynomial.eval₂Hom_comp_C] at h3

theorem sub_mem_span_of_etale {Λ D : Type} [CommRing Λ] [CommRing D] (i : Λ →+* D) {d : ℕ}
    (t : Fin d → D) (het : (MvPolynomial.eval₂Hom i t).Etale) (J : Ideal D) (μ : D) (g : D →+* D)
    (hJ : ∀ x ∈ J, IsNilpotent x) (hgi : g.comp i = i)
    (hgt : ∀ k, g (t k) - t k ∈ Ideal.span {μ}) (hgJ : ∀ z, g z - z ∈ J) (z : D) :
    g z - z ∈ Ideal.span {μ} := by
  classical
  letI : Algebra (MvPolynomial (Fin d) Λ) D := (MvPolynomial.eval₂Hom i t).toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin d) Λ) D := het
  let q : D →+* D ⧸ Ideal.span ({μ} : Set D) := Ideal.Quotient.mk _
  have hcomm : (q.comp g).comp (MvPolynomial.eval₂Hom i t) = q.comp (MvPolynomial.eval₂Hom i t) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
      rw [← RingHom.comp_apply g i, hgi]
    · intro k
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
      exact Ideal.Quotient.eq.mpr (hgt k)
  let φ₁ : D →ₐ[MvPolynomial (Fin d) Λ] D ⧸ Ideal.span ({μ} : Set D) := Ideal.Quotient.mkₐ _ _
  let φ₂ : D →ₐ[MvPolynomial (Fin d) Λ] D ⧸ Ideal.span ({μ} : Set D) :=
    { (q.comp g) with
      commutes' := fun a => by
        change q (g (algebraMap _ D a)) = q (algebraMap _ D a)
        exact RingHom.congr_fun hcomm a }
  obtain ⟨S, hS⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra (MvPolynomial (Fin d) Λ) D).FG)
  let I : Ideal (D ⧸ Ideal.span ({μ} : Set D)) :=
    Ideal.span ((fun s => q (g s - s)) '' (S : Set D))
  have hfg : I.FG := Submodule.fg_span (S.finite_toSet.image _)
  have hnil : IsNilpotent I := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical hfg]
    rw [Ideal.span_le]
    rintro _ ⟨s, -, rfl⟩
    exact mem_nilradical.mpr ((hJ _ (hgJ s)).map q)
  have hψ : (Ideal.Quotient.mkₐ (MvPolynomial (Fin d) Λ) I).comp φ₁ =
      (Ideal.Quotient.mkₐ (MvPolynomial (Fin d) Λ) I).comp φ₂ := by
    apply AlgHom.ext_of_adjoin_eq_top hS
    intro s hs
    have hmem : q (g s - s) ∈ I := Ideal.subset_span ⟨s, hs, rfl⟩
    rw [map_sub] at hmem
    show Ideal.Quotient.mk I (q s) = Ideal.Quotient.mk I (q (g s))
    exact (Ideal.Quotient.eq.mpr hmem).symm
  have hφ : φ₁ = φ₂ := by
    apply Algebra.FormallyUnramified.ext I hnil
    intro x
    exact congrArg (fun ψ : D →ₐ[MvPolynomial (Fin d) Λ] _ => ψ x) hψ
  have hz : q z = q (g z) := congrArg (fun ψ : D →ₐ[MvPolynomial (Fin d) Λ] _ => ψ z) hφ
  exact Ideal.Quotient.eq.mp hz.symm

theorem lift_flat : ∀ {Λ D : Type} [CommRing Λ] [CommRing D] (i : Λ →+* D) {d : ℕ} (t : Fin d → D), (MvPolynomial.eval₂Hom i t).Etale → i.Flat ∧ ∀ (J : Ideal D) (μ : D) (g : D →+* D), (∀ x ∈ J, IsNilpotent x) → g.comp i = i → (∀ k, g (t k) - t k ∈ Ideal.span {μ}) → (∀ z, g z - z ∈ J) → ∀ z, g z - z ∈ Ideal.span {μ} := by
  intro Λ D _ _ i d t het
  exact ⟨flat_of_eval₂Hom_etale i t het, fun J μ g hJ hgi hgt hgJ z =>
    sub_mem_span_of_etale i t het J μ g hJ hgi hgt hgJ z⟩

end GlobalTheory.CompanionTheory.LiftFlat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SurjectiveOfUnramified
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
open TensorProduct

namespace GlobalTheory.CompanionTheory.EtalePerfect

theorem surjective_of_unramified {R S : Type} [CommRing R] [CommRing S] (p : ℕ) (hp : p.Prime)
    (hS : (p : S) = 0) (f : R →+* S) (hu : f.FormallyUnramified) (hft : f.FiniteType)
    (hpow : ∀ x : S, ∃ r, f r = x ^ p) : Function.Surjective f := by
  algebraize [f]
  have hint : Algebra.IsIntegral R S := ⟨fun x => by
    obtain ⟨r, hr⟩ := hpow x
    refine IsIntegral.of_pow hp.pos ?_
    rw [← hr]
    exact isIntegral_algebraMap⟩
  have hfin : Module.Finite R S := Algebra.IsIntegral.finite
  obtain ⟨t, ht2, ht1⟩ := Algebra.FormallyUnramified.iff_exists_tensorProduct.1
    (inferInstance : Algebra.FormallyUnramified R S)
  have hT : (p : S ⊗[R] S) = 0 := by
    rw [← map_natCast (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] S), hS, map_zero]
  have hadd : ∀ x y : S ⊗[R] S, (x + y) ^ p = x ^ p + y ^ p := by
    intro x y
    obtain ⟨c, hc⟩ := exists_add_pow_prime_eq hp x y
    rw [hc, hT]
    simp
  have haddS : ∀ x y : S, (x + y) ^ p = x ^ p + y ^ p := by
    intro x y
    obtain ⟨c, hc⟩ := exists_add_pow_prime_eq hp x y
    rw [hc, hS]
    simp
  have hfrob : ∀ u : S ⊗[R] S,
      u ^ p = ((Algebra.TensorProduct.lmul' R (S := S) u) ^ p) ⊗ₜ[R] (1 : S) := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp [zero_pow hp.ne_zero]
    | tmul a b =>
      obtain ⟨s, hs⟩ := hpow b
      have hs' : b ^ p = s • (1 : S) := by
        rw [← hs, Algebra.smul_def, mul_one]; rfl
      rw [Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.lmul'_apply_tmul, mul_pow, hs',
        TensorProduct.tmul_smul, mul_smul_comm, mul_one, TensorProduct.smul_tmul']
    | add x y hx hy =>
      rw [hadd, hx, hy, map_add, haddS, TensorProduct.add_tmul]
  have hmul : ∀ u : S ⊗[R] S,
      u * t = (Algebra.TensorProduct.lmul' R (S := S) u ⊗ₜ[R] (1 : S)) * t := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      have hb := ht2 b
      rw [sub_mul, sub_eq_zero] at hb
      have : a ⊗ₜ[R] b = (a ⊗ₜ[R] (1 : S)) * ((1 : S) ⊗ₜ[R] b) := by simp
      rw [this, mul_assoc, hb, ← mul_assoc]
      simp
    | add x y hx hy =>
      rw [add_mul, hx, hy, map_add, TensorProduct.add_tmul, add_mul]
  have hidem : t * t = t := by
    rw [hmul t, ht1]
    exact one_mul t
  have htp : t ^ p = t := (show IsIdempotentElem t from hidem).pow_eq hp.ne_zero
  have ht : t = 1 := by
    rw [← htp, hfrob t, ht1, one_pow]
    rfl
  have hepi : Algebra.IsEpi R S := by
    rw [Algebra.isEpi_iff_forall_one_tmul_eq]
    intro s
    have := ht2 s
    rw [ht, mul_one, sub_eq_zero] at this
    exact this
  exact Algebra.isEpi_iff_surjective_algebraMap_of_finite.1 hepi

theorem pf_of_etale : ∀ (p : ℕ), p.Prime → ∀ {P E : Type} [CommRing P] [CommRing E] (ψ : P →+* E),
    ψ.Etale → D.Pf p P → D.Pf p E := by
  intro p hp P E _ _ ψ hψ hP
  have hEc : (p : E) = 0 := by rw [← map_natCast ψ, hP.char, map_zero]
  have hadd : ∀ {A : Type} [CommRing A], (p : A) = 0 → ∀ x y : A, (x + y) ^ p = x ^ p + y ^ p := by
    intro A _ h x y
    obtain ⟨c, hc⟩ := exists_add_pow_prime_eq hp x y
    rw [hc, h]
    simp
  let φ : E →+* E :=
    { toFun := fun x => x ^ p
      map_one' := one_pow p
      map_mul' := fun x y => mul_pow x y p
      map_zero' := zero_pow hp.ne_zero
      map_add' := hadd hEc }
  let Fp : P →+* P :=
    { toFun := fun x => x ^ p
      map_one' := one_pow p
      map_mul' := fun x y => mul_pow x y p
      map_zero' := zero_pow hp.ne_zero
      map_add' := hadd hP.char }
  let e : P ≃+* P := RingEquiv.ofBijective Fp hP.bij
  let G : P →+* P := e.symm.toRingHom
  have hFG : ∀ x, (G x) ^ p = x := fun x => e.apply_symm_apply x
  have hGF : ∀ x, G (x ^ p) = x := fun x => e.symm_apply_apply x
  have hcomp : φ.comp (ψ.comp G) = ψ := by
    ext x
    change (ψ (G x)) ^ p = ψ x
    rw [← map_pow, hFG]
  have hUψ : ψ.FormallyUnramified := hψ.formallyUnramified
  have hFTψ : ψ.FiniteType := by
    algebraize [ψ]
    have : Algebra.Etale P E := hψ.toAlgebra
    exact (inferInstance : Algebra.FiniteType P E)
  have hu : φ.FormallyUnramified := by
    rw [← hcomp] at hUψ
    exact RingHom.FormallyUnramified.of_comp hUψ
  have hft : φ.FiniteType := by
    rw [← hcomp] at hFTψ
    exact RingHom.FiniteType.of_comp_finiteType hFTψ
  have hsurj : Function.Surjective φ :=
    surjective_of_unramified p hp hEc φ hu hft (fun x => ⟨x, rfl⟩)
  let N : Ideal E := RingHom.ker φ
  have hN : ∀ x ∈ N, IsNilpotent x := fun x hx => ⟨p, hx⟩
  have hL : EtLift N := GlobalTheory.T.etale_lifting_of_nil_ideal N hN
  let eb : (E ⧸ N) ≃+* E := RingHom.quotientKerEquivOfSurjective hsurj
  have heb : ∀ x, eb (Ideal.Quotient.mk N x) = x ^ p := fun x => rfl
  let g : E →+* E ⧸ N := eb.symm.toRingHom
  have hg : ∀ x, g (x ^ p) = Ideal.Quotient.mk N x := by
    intro x
    apply eb.injective
    rw [heb]
    exact eb.apply_symm_apply _
  have hgψ : g.comp ψ = (Ideal.Quotient.mk N).comp (ψ.comp G) := by
    ext x
    apply eb.injective
    change eb (eb.symm (ψ x)) = eb (Ideal.Quotient.mk N (ψ (G x)))
    rw [eb.apply_symm_apply, heb, ← map_pow, hFG]
  obtain ⟨h, ⟨hh1, hh2⟩, -⟩ := hL P E ψ hψ (ψ.comp G) g hgψ
  have hid : h.comp φ = RingHom.id E := by
    refine (hL P E ψ hψ ψ (Ideal.Quotient.mk N) rfl).unique ⟨?_, ?_⟩ ⟨?_, ?_⟩
    · ext x
      change h ((ψ x) ^ p) = ψ x
      rw [← map_pow]
      have := RingHom.congr_fun hh1 (x ^ p)
      simp only [RingHom.comp_apply] at this
      rw [this, hGF]
    · ext x
      have := RingHom.congr_fun hh2 (x ^ p)
      simp only [RingHom.comp_apply] at this
      change Ideal.Quotient.mk N (h (x ^ p)) = _
      rw [this, hg]
    · rfl
    · rfl
  refine ⟨hEc, ?_, ?_⟩
  · intro x y hxy
    have hx := RingHom.congr_fun hid x
    have hy := RingHom.congr_fun hid y
    simp only [RingHom.comp_apply, RingHom.id_apply] at hx hy
    rw [← hx, ← hy]
    exact congrArg h hxy
  · exact hsurj

end GlobalTheory.CompanionTheory.EtalePerfect
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WedgeTransport
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.HodgeO

section Transport

variable {R : Type} [CommRing R]

theorem finrank_of_vb {k M : Type} [Field k] [AddCommGroup M] [Module k M] {g : ℕ} (h : VB k M g) :
    Module.finrank k M = g := by
  obtain ⟨p⟩ : Nonempty (PrimeSpectrum k) := inferInstance
  have e := congrFun (Module.rankAtStalk_eq_finrank_of_free (R := k) (M := M)) p
  exact e.symm.trans (h.2.2 p)

theorem vb_of_equiv {M N : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] {g : ℕ}
    (e : M ≃ₗ[R] N) (h : VB R M g) : VB R N g :=
  have := h.1
  have := h.2.1
  ⟨Module.Finite.equiv e, Module.Projective.of_equiv e, fun p ↦
    (congrFun (Module.rankAtStalk_eq_of_equiv e) p).symm.trans (h.2.2 p)⟩

def wedgeEquiv {M N : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) :
    ⋀[R]^2 M ≃ₗ[R] ⋀[R]^2 N :=
  LinearEquiv.ofLinear (exteriorPower.map 2 e.toLinearMap) (exteriorPower.map 2 e.symm.toLinearMap)
    (by rw [← exteriorPower.map_comp]; simp)
    (by rw [← exteriorPower.map_comp]; simp)

theorem wedge_transport {M M' N N' : Type} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N'] (e₁ : M ≃ₗ[R] M') (e₂ : N ≃ₗ[R] N')
    (B : M → M → N) (B' : M' → M' → N') (hB : ∀ a b, e₂ (B a b) = B' (e₁ a) (e₁ b))
    (h : ∃ e : ⋀[R]^2 M ≃ₗ[R] N, ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = B a b) :
    ∃ e : ⋀[R]^2 M' ≃ₗ[R] N', ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = B' a b := by
  obtain ⟨e, he⟩ := h
  refine ⟨(wedgeEquiv e₁.symm).trans (e.trans e₂), fun a b ↦ ?_⟩
  have k : wedgeEquiv e₁.symm (exteriorPower.ιMulti R 2 ![a, b]) =
      exteriorPower.ιMulti R 2 ![e₁.symm a, e₁.symm b] := by
    refine (exteriorPower.map_apply_ιMulti _ _).trans (congrArg _ ?_)
    funext i
    fin_cases i <;> rfl
  simp only [LinearEquiv.trans_apply]
  rw [k, he, hB, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

variable {C C' : Type} [Category.{0} C] [Category.{0} C'] {F : C ⥤ CommAlgCat.{0} R}
  {F' : C' ⥤ CommAlgCat.{0} R}

theorem wedge_of_bij (m : CoefMap (RingHom.id R) F F') (h₁ : Function.Bijective m.pull1)
    (h₂ : Function.Bijective m.pull2) (h : Wedge F) : Wedge F' :=
  wedge_transport (LinearEquiv.ofBijective m.pull1 h₁) (LinearEquiv.ofBijective m.pull2 h₂)
    (fun a b ↦ cup F a b) (fun a b ↦ cup F' a b) (fun a b ↦ m.pullCohomologyTwo_cup a b) h

theorem wedge_of_bij' (m : CoefMap (RingHom.id R) F F') (h₁ : Function.Bijective m.pull1)
    (h₂ : Function.Bijective m.pull2) (h : Wedge F') : Wedge F :=
  wedge_transport (LinearEquiv.ofBijective m.pull1 h₁).symm (LinearEquiv.ofBijective m.pull2 h₂).symm
    (fun a b ↦ cup F' a b) (fun a b ↦ cup F a b) (fun a b ↦ by
      refine (LinearEquiv.symm_apply_eq _).2 ?_
      refine Eq.trans ?_ (m.pullCohomologyTwo_cup _ _).symm
      change _ = cup F' (LinearEquiv.ofBijective m.pull1 h₁ _) (LinearEquiv.ofBijective m.pull1 h₁ _)
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]) h

theorem hopf_false {b : Prop} (h : Hopf F b) : Hopf F False := by
  obtain ⟨D, _, G, π, m, h₁, h₂, -⟩ := h
  exact ⟨D, _, G, π, m, h₁, h₂, False.elim⟩

end Transport

theorem pack {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) {R' : Type} [CommRing R'] [Algebra R R'] (A' : Over (Sp R'))
    {i : GrpObj A'} (φ : A'.left ⟶ A.left) (hφ : IsGrpPullback A' A (spMap (algebraMap R R')) φ) :
    ∃ (A' : Over (Sp R')) (_ : GrpObj A') (φ : A'.left ⟶ A.left),
      IsPullback φ A'.hom A.hom (spMap (algebraMap R R')) ∧ IsAbelianScheme A' ∧
        SmoothOfRelativeDimension g A'.hom :=
  ⟨A', i, φ, hφ.1, GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hφ,
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hφ.1 hg⟩

theorem exists_base {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) (R' : Type) [CommRing R'] [Algebra R R'] :
    ∃ (A' : Over (Sp R')) (_ : GrpObj A') (φ : A'.left ⟶ A.left),
      IsPullback φ A'.hom A.hom (spMap (algebraMap R R')) ∧ IsAbelianScheme A' ∧
        SmoothOfRelativeDimension g A'.hom :=
  pack A g hA hg _ _ (isGrpPullback_pullback A (spMap (algebraMap R R')))

theorem low (hD : DescentSt) (hL : LowSt) {P : Type} [SemilatticeInf P] (R' : Type) [CommRing R'] (A' : Over (Sp R'))
    [GrpObj A'] (ha : IsAbelianScheme A') (S' : Sys A'.left P) :
    Function.Bijective (resSys A'.hom S').pull1 ∧ Function.Bijective (resSys A'.hom S').pull2 ∧
      (Stein (OAff A'.hom) ↔ Stein (OSys A'.hom S')) := by
  have := ha.proper
  exact hL R' _ _ (OAff A'.hom) (OSys A'.hom S') (resSys A'.hom S') (hD R' A'.left A'.hom inferInstance P S')

theorem base (hS : SysBCSt) {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) {P : Type} [SemilatticeInf P] (S : Sys A.left P) (R' : Type)
    [CommRing R'] [Algebra R R'] : ∃ (A' : Over (Sp R')) (_ : GrpObj A') (S' : Sys A'.left P)
      (_ : BC (OSys A.hom S) (OSys A'.hom S')), IsAbelianScheme A' ∧ SmoothOfRelativeDimension g A'.hom := by
  have pr := hA.proper
  have sep : IsSeparated A.hom := inferInstance
  obtain ⟨A', _, φ, h, ha, hg'⟩ := exists_base A g hA hg R'
  obtain ⟨S', m, -⟩ := hS R R' A.left A'.left A.hom A'.hom φ h sep P S
  exact ⟨A', _, S', m, ha, hg'⟩

theorem steinU (hD : DescentSt) (hL : LowSt) (hS : SysBCSt) (hSt : SteinSt) {R : Type} [CommRing R]
    (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    {P : Type} [SemilatticeInf P] (S : Sys A.left P) : SteinU (OSys A.hom S) := fun R' _ _ ↦ by
  obtain ⟨A', _, S', m, ha, hg'⟩ := base hS A g hA hg S R'
  exact ⟨_, m, (low hD hL R' A' ha S').2.2.1 (hSt R' A' g ha hg')⟩

theorem vbSys (hD : DescentSt) (hL : LowSt) (hH1 : H1StructureBundle) {R : Type} [CommRing R]
    (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    {P : Type} [SemilatticeInf P] (S : Sys A.left P) : VB R (H1 (OSys A.hom S)) g :=
  vb_of_equiv (LinearEquiv.ofBijective _ (low hD hL R A hA S).1) (hH1 R A g hA hg)

theorem finFib (hD : DescentSt) (hL : LowSt) (hS : SysBCSt) (hH1 : H1StructureBundle) {R : Type} [CommRing R]
    (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    {P : Type} [SemilatticeInf P] (S : Sys A.left P) (k : Type) [Field k] [Algebra R k] :
    ∃ (F' : Pᵒᵖ ⥤ CommAlgCat.{0} k) (_ : BC (OSys A.hom S) F'), Module.finrank k (H1 F') = g := by
  obtain ⟨A', _, S', m, ha, hg'⟩ := base hS A g hA hg S k
  exact ⟨_, m, finrank_of_vb (vbSys hD hL hH1 A' g ha hg' S')⟩

theorem wedgeFib (hD : DescentSt) (hL : LowSt) (hS : SysBCSt) (hWF : WedgeFieldSt) {R : Type} [CommRing R]
    (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    {P : Type} [SemilatticeInf P] (S : Sys A.left P) (k : Type) [Field k] [Algebra R k] :
    ∃ (F' : Pᵒᵖ ⥤ CommAlgCat.{0} k) (_ : BC (OSys A.hom S) F'), Wedge F' := by
  obtain ⟨A', _, S', m, ha, hg'⟩ := base hS A g hA hg S k
  have b := low hD hL k A' ha S'
  exact ⟨_, m, wedge_of_bij (resSys A'.hom S') b.1 b.2.1 (hWF k A' g ha hg' (Field.toIsField k))⟩

theorem coreSys (hD : DescentSt) (hL : LowSt) (hS : SysBCSt) (hSt : SteinSt) (hH1 : H1StructureBundle)
    (hWF : WedgeFieldSt) (hHopf : HopfSt) (hPH1 : PerfectH1BaseChange) (hPH2 : PerfectH2FromFibres) (hWO : WedgeOfSt)
    {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) {P : Type} [SemilatticeInf P] [Finite P] (S : Sys A.left P)
    (hPf : Perf (OSys A.hom S)) : H1CommutesBaseChange (OSys A.hom S) ∧ Wedge (OSys A.hom S) := by
  have hSU := steinU hD hL hS hSt A g hA hg S
  have hV := vbSys hD hL hH1 A g hA hg S
  have hB : H1CommutesBaseChange (OSys A.hom S) := hPH1 R P (OSys A.hom S) g hPf hSU hV fun k _ _ ↦
    finFib hD hL hS hH1 A g hA hg S k
  obtain ⟨h2, hs⟩ := hPH2 R P (OSys A.hom S) g hPf hSU hV hB fun k _ _ ↦
    wedgeFib hD hL hS hWF A g hA hg S k
  exact ⟨hB, hWO R P (OSys A.hom S) g (hopf_false (hHopf R A g hA hg P S)) hV hB h2 hs⟩

theorem oBC_wedge : DescentSt → LowSt → SysBCSt → PerfSt → SteinSt → H1StructureBundle → WedgeFieldSt → HopfSt → PerfectH1BaseChange →
    PerfectH2FromFibres → WedgeOfSt → OBCSt ∧ WedgeSt := by
  intro hD hL hS hP hSt hH1 hWF hHopf hPH1 hPH2 hWO
  refine ⟨?_, ?_⟩
  · intro R _ A _ g hA hg R' _ _ X' s' φ h
    have pr := hA.proper
    have sep : IsSeparated A.hom := inferInstance
    have sep' : IsSeparated s' := MorphismProperty.of_isPullback h sep
    obtain ⟨P, _, _, S, hPf⟩ := hP R A.left A.hom hA.smooth pr
    have hB := (coreSys hD hL hS hSt hH1 hWF hHopf hPH1 hPH2 hWO A g hA hg S hPf).1
    obtain ⟨S', m, hc⟩ := hS R R' A.left X' A.hom s' φ h sep P S
    obtain ⟨e₀, he₀⟩ := hB R' _ m
    have b₁ := (hL R _ _ _ _ (resSys A.hom S) (hD R A.left A.hom sep P S)).1
    have b₂ := (hL R' _ _ _ _ (resSys s' S') (hD R' X' s' sep' P S')).1
    let e₁ := LinearEquiv.ofBijective _ b₁
    let e₂ := LinearEquiv.ofBijective _ b₂
    refine ⟨(LinearEquiv.baseChange R R' _ _ e₁).trans (e₀.trans e₂.symm), fun c ↦ hc c _ ?_⟩
    refine (he₀ _).symm.trans ?_
    exact (e₂.apply_symm_apply _).symm
  · intro R _ A _ g hA hg
    have pr := hA.proper
    obtain ⟨P, _, _, S, hPf⟩ := hP R A.left A.hom hA.smooth pr
    have hW := (coreSys hD hL hS hSt hH1 hWF hHopf hPH1 hPH2 hWO A g hA hg S hPf).2
    have b := low hD hL R A hA S
    exact wedge_of_bij' (resSys A.hom S) b.1 b.2.1 hW

end GlobalTheory.CompanionTheory.HodgeO
end
end

