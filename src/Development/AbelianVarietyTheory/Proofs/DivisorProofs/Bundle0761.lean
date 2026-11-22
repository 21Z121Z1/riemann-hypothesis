import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0722
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0748
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0262
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0305
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0409
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0593
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0726
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0745
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0746
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0733
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0672
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0707
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0731
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0747
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodClassLinearRelationUniqueOfNilpotent
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer.Charts

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F)
  {R : Type} [CommRing R] (et : Hol F.V →+* R) (M : Ideal R)

def perZDLin : (Λ →+ R) →ₗ[R] GlobalTheory.CatCoh.Z1 (K.OD et M) where
  toFun := K.perZD et M
  map_add' q q' := Subtype.ext (funext fun _ ↦ funext fun S' ↦ funext fun f ↦ map_add (algebraMap R S'.T.C) (q f.1.deg) (q' f.1.deg))
  map_smul' r q := Subtype.ext (funext fun _ ↦ funext fun S' ↦ funext fun f ↦
    (map_mul (algebraMap R S'.T.C) r (q f.1.deg)).trans (Algebra.smul_def (A := S'.T.C) r _).symm)

end GlobalTheory.AnPer.Charts

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct in
attribute [local instance] Over.cartesianMonoidalCategory in

theorem _root_.GlobalTheory.AnPer.perClD_relation_unique : ∀ {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F₀ : _root_.GlobalTheory.AnPer.Fam Empty g Λ} (K₀ : _root_.GlobalTheory.AnPer.Charts F₀) {R : Type} [CommRing R] [Algebra ℂ R] (et : _root_.GlobalTheory.AnPer.Hol F₀.V →+* R) (M : Ideal R), K₀.Rich → (∀ z, z ∈ F₀.V) → IsNilpotent M → (∀ (f : _root_.GlobalTheory.AnPer.Hol F₀.V), ∀ z ∈ F₀.V, et f = algebraMap ℂ R (f.fn z)) → ∀ {io : Type} (S : Finset io) (d : io → R) (q : io → (Λ →+ R)) (q' : Λ →+ R), K₀.perClD et M q' = ∑ i ∈ S, d i • K₀.perClD et M (q i) → ∀ l, q' l = ∑ i ∈ S, d i * q i l := by
  intro g Λ _ F₀ K₀ R _ _ et M hrich hV hnil het io S d q q' hrel l
  let q'' : Λ →+ R := q' - ∑ i ∈ S, d i • q i
  have hq'' : ∀ m, q'' m = q' m - ∑ i ∈ S, d i * q i m := by
    intro m
    simp [q'', AddMonoidHom.finset_sum_apply, smul_eq_mul]
  have hcl : K₀.perClD et M q'' = 0 := by
    have hc : ∀ p : Λ →+ R, K₀.perClD et M p =
        _root_.GlobalTheory.CatCoh.H1.mk _
          (K₀.perZDLin et M p) := fun p => rfl
    simp only [hc] at hrel ⊢
    simp only [q'', map_sub, map_sum, map_smul, hrel, sub_self]
  obtain ⟨G, hG0, hGsh⟩ := _root_.GlobalTheory.ChartCobd.coboundary_on_charts K₀ et M hnil het q'' hcl
  have hzero : q'' l = 0 := by
    rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro φ
    let Φ : ∀ k, R ⊗[ℂ] _root_.GlobalTheory.AnPer.Hol (K₀.W k) →ₗ[ℂ]
        _root_.GlobalTheory.AnPer.Hol (K₀.W k) :=
      fun k => (TensorProduct.lid ℂ _).toLinearMap ∘ₗ LinearMap.rTensor _ φ
    have hΦ : ∀ k r h, Φ k (r ⊗ₜ h) = φ r • h := by
      intro k r h
      simp [Φ]
    have hΦd : ∀ k a y, _root_.GlobalTheory.AnPer.dw a (Φ k y) =
        Φ k (LinearMap.lTensor R (_root_.GlobalTheory.AnPer.dw a).toLinearMap y) := by
      intro k a y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul r h => simp [hΦ]
      | add y z hy hz => simp only [map_add, hy, hz]
    have hΦs : ∀ {m k k'} (h : K₀.le m k' k) y,
        Φ k' (Algebra.TensorProduct.map (AlgHom.id ℂ R)
          (_root_.GlobalTheory.AnPer.Charts.shA h) y) =
        _root_.GlobalTheory.AnPer.Charts.sh h (Φ k y) := by
      intro m k k' h y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul r b =>
        simp [hΦ, ← _root_.GlobalTheory.AnPer.Charts.shA_apply]
      | add y z hy hz => simp only [map_add, hy, hz]
    have hfsh : ∀ m k k' (h : K₀.le m k' k),
        _root_.GlobalTheory.AnPer.Charts.sh h (Φ k (G k)) =
          Φ k' (G k') + K₀.cst k' (algebraMap ℂ _ (-(φ (q'' m)))) := by
      intro m k k' h
      have h1 := congrArg (Φ k') (hGsh m k k' h)
      rw [map_sub, hΦs, hΦ] at h1
      have h2 : K₀.cst k' (algebraMap ℂ _ (-(φ (q'' m)))) =
          -(φ (q'' m) • 1) := by
        unfold _root_.GlobalTheory.AnPer.Charts.cst
        simp [Algebra.algebraMap_eq_smul_one]
      rw [h2, ← h1]
      abel
    obtain ⟨Gf, -, -, hper, hconst⟩ := _root_.GlobalTheory.AnPer.Charts.glue K₀
      hrich (fun k => Φ k (G k)) (by
        intro k k' h
        simp [hfsh 0 k k' h])
    have hc := hconst (fun k a => by rw [hΦd, hG0, map_zero])
    let p : _root_.GlobalTheory.AnPer.Tot Empty g := ((0 : Empty → ℂ), (0 : Fin g → ℂ))
    have hp := hper l (algebraMap ℂ _ (-(φ (q'' l)))) (fun k k' h => hfsh l k k' h) p (hV _)
    have e : Gf (F₀.shift l p) = Gf p := by
      calc Gf (F₀.shift l p) =
          Gf ((F₀.shift l p).1, (F₀.shift l p).2) := rfl
        _ = Gf ((F₀.shift l p).1, 0) := hc _ (hV _) _
        _ = Gf (p.1, 0) := by rw [Subsingleton.elim (F₀.shift l p).1 p.1]
        _ = Gf p := rfl
    have hfn : (algebraMap ℂ (_root_.GlobalTheory.AnPer.Hol F₀.V)
        (-(φ (q'' l)))).fn p.1 = -(φ (q'' l)) := by
      unfold _root_.GlobalTheory.AnPer.Hol.fn
      simp [hV]
    rw [e, hfn] at hp
    linear_combination hp
  rw [← sub_eq_zero, ← hq'' l]
  exact hzero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiEmbeddingDeterminantProperty
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem detConst_linear_isom : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ τ₀ : Λ →+* O, ∃ (κ₀ : ℝ) (κ : (Λ →+* O) → ℝ), ∀ (γ : O ≃+* O), IsIsom C v γ → ∀ (N h : ℕ), h = Module.finrank ℤ_[p] Λ * N → ∀ (D : Datum ε h Λ) ι (lam : C), IsIota C D ((γ : O →+* O).comp τ₀) N ι → lam ≠ 0 → ι '' (detLattice C (actT D) ((γ : O →+* O).comp τ₀) N : Set (detLine C (actT D) ((γ : O →+* O).comp τ₀) N)) = (fun w => lam • w) '' (detLattice C (actH D) ((γ : O →+* O).comp τ₀) N : Set (detLine C (actH D) ((γ : O →+* O).comp τ₀) N)) → Real.log (v lam) = N * κ₀ + ∑ᶠ σ, (D.lieRank ((γ : O →+* O).comp σ) : ℝ) * κ σ := by
  classical
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ τ₀
  obtain ⟨-, -, ψ, -, hψ, -⟩ := GlobalTheory.DetInv.psi_phi_tensor p O Λ
  obtain ⟨κ₀, κ, hlin⟩ := GlobalTheory.T.psi_determinant_valuation_bound p C v O hv ε hε Λ ψ hψ τ₀
  obtain ⟨hfin, -⟩ := GlobalTheory.card_ringHom_to_integers_eq_finrank p C v O hv Λ
  obtain ⟨-, -, -, -, hθν, -, -⟩ := GlobalTheory.AinfXi.ainf_local_xi_order p C v O hv ε hε
  set t : ℝ := Real.log (v (algebraMap O C (WittVector.fontaineTheta O p (nu ε)))) with ht
  refine ⟨κ₀, fun σ => κ σ - if σ = τ₀ then t else 0, ?_⟩
  intro γ hγ N h hh D ι lam hι hlam hlat
  obtain ⟨Δ, c, hΔ, hord, hc⟩ :=
    GlobalTheory.T.psi_determinant_element_property p C v O hv ε hε Λ ψ hψ N h hh D ((γ : O →+* O).comp τ₀) ι lam hι hlat
  obtain ⟨Δ', c', hΔ', hord', hc'⟩ :=
    GlobalTheory.T.psi_determinant_rank_property p C v O hv ε hε Λ ψ hψ γ hγ N Δ D.lieRank c hΔ hord
  have key := hlin N Δ' _ c' hΔ' hord'
  rw [hc' τ₀, hc] at key
  have hv0 : v lam ≠ 0 := (Valuation.ne_zero_iff v).mpr hlam
  have hθ0 : algebraMap O C (WittVector.fontaineTheta O p (nu ε)) ≠ 0 := by
    intro h0
    apply hθν
    apply hv.hom_inj
    rw [h0, map_zero]
  have hvθ : v (algebraMap O C (WittVector.fontaineTheta O p (nu ε))) ≠ 0 :=
    (Valuation.ne_zero_iff v).mpr hθ0
  have hlog : Real.log ((v lam * v (algebraMap O C (WittVector.fontaineTheta O p (nu ε))) ^
      D.lieRank ((γ : O →+* O).comp τ₀) : NNReal) : ℝ) =
      Real.log (v lam) + (D.lieRank ((γ : O →+* O).comp τ₀) : ℝ) * t := by
    rw [NNReal.coe_mul, NNReal.coe_pow, Real.log_mul, Real.log_pow]
    · exact_mod_cast hv0
    · exact pow_ne_zero _ (by exact_mod_cast hvθ)
  rw [hlog] at key
  haveI := hfin
  letI := Fintype.ofFinite (Λ →+* O)
  rw [finsum_eq_sum_of_fintype] at key ⊢
  simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  linarith

end GlobalTheory.DetInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PushMemLiftFilOfInjective
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqLift

theorem push_mem_liftFil_of_injective : AbelianDeRham →
  ∀ (R : Type) [CommRing R] (I : Ideal R) (h : I ^ 2 = 0) (R₀ : Type) [CommRing R₀] (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π = I →
  ∀ (S : Type) [CommRing S] (σ : S →+* R), Function.Injective σ →
  ∀ (J : Ideal S) (hJ : J ^ 2 = 0) (S₀ : Type) [CommRing S₀] (πS : S →+* S₀),
    Function.Surjective πS → RingHom.ker πS = J →
  ∀ (ι₀ : S₀ →+* R₀), ι₀.comp πS = π.comp σ →
  ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left)
    (hA : IsGrpPullback A₀ A (spMap π) i)
    (AS₀ : Over (Sp S₀)) [GrpObj AS₀] (AS : Over (Sp S)) [GrpObj AS] (iS : AS₀.left ⟶ AS.left)
    (hAS : IsGrpPullback AS₀ AS (spMap πS) iS), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    IsAbelianScheme AS → SmoothOfRelativeDimension g AS.hom →
  ∀ (φA : A.left ⟶ AS.left) (ψA : A₀.left ⟶ AS₀.left), IsGrpPullback A AS (spMap σ) φA →
    IsGrpPullback A₀ AS₀ (spMap ι₀) ψA → i ≫ φA = ψA ≫ iS →
  ∀ (g' : ℕ) (B₀ : Over (Sp R₀)) [GrpObj B₀] (B : Over (Sp R)) [GrpObj B] (j : B₀.left ⟶ B.left)
    (hB : IsGrpPullback B₀ B (spMap π) j)
    (BS₀ : Over (Sp S₀)) [GrpObj BS₀] (BS : Over (Sp S)) [GrpObj BS] (jS : BS₀.left ⟶ BS.left)
    (hBS : IsGrpPullback BS₀ BS (spMap πS) jS), IsAbelianScheme B → SmoothOfRelativeDimension g' B.hom →
    IsAbelianScheme BS → SmoothOfRelativeDimension g' BS.hom →
  ∀ (φB : B.left ⟶ BS.left) (ψB : B₀.left ⟶ BS₀.left), IsGrpPullback B BS (spMap σ) φB →
    IsGrpPullback B₀ BS₀ (spMap ι₀) ψB → j ≫ φB = ψB ≫ jS →
  ∀ (f₀ : A₀ ⟶ B₀) [IsMonHom f₀] (fS₀ : AS₀ ⟶ BS₀) [IsMonHom fS₀], f₀.left ≫ ψB = ψA ≫ fS₀.left →
    (∀ d ∈ liftFil (divided₂ h) hA, push (divided₂ h) (spMap π) f₀ d ∈ liftFil (divided₂ h) hB) →
    ∀ d ∈ liftFil (divided₂ hJ) hAS, push (divided₂ hJ) (spMap πS) fS₀ d ∈ liftFil (divided₂ hJ) hBS := by
  intro H R _ I h R₀ _ π hπ hI S _ σ hσ J hJ S₀ _ πS hπS hJk ι₀ hι g A₀ _ A _ i hA AS₀ _ AS _ iS hAS hAab hAg
    hASab hASg φA ψA hφA hψA hiA g' B₀ _ B _ j hB BS₀ _ BS _ jS hBS hBab hBg hBSab hBSg φB ψB hφB hψB hjB
    f₀ _ fS₀ _ hf hyp d hd
  obtain ⟨_, _, HBC, HR, _⟩ := H
  letI : Algebra S R := σ.toAlgebra
  have hJI : ∀ a ∈ J, σ a ∈ I := fun a ha ↦ by
    rw [← hI, RingHom.mem_ker]
    have : πS a = 0 := by rw [← RingHom.mem_ker, hJk]; exact ha
    rw [← RingHom.comp_apply, ← hι, RingHom.comp_apply, this, map_zero]
  have hdp : IsDPMorphism (divided₂ hJ) (divided₂ h) σ := isDPMorphism_sqDP hJ h σ hJI
  have hbase : spMap ι₀ ≫ spMap πS = spMap π ≫ spMap σ := by
    rw [← Cris.spMap_comp, ← Cris.spMap_comp, hι]
  have mA := GrpMor.of_isGrpPullback hdp hbase hψA
  have mB := GrpMor.of_isGrpPullback hdp hbase hψB
  have nA := GlobalTheory.Published.AbelianDeRham.bcMor (R := S) (R' := R) hφA
  have nB := GlobalTheory.Published.AbelianDeRham.bcMor (R := S) (R' := R) hφB
  have hBCA := HBC S AS g hASab hASg R A φA hφA
  obtain ⟨y, hy⟩ := hBCA.1.exists (crysToDR (divided₂ hJ) hAS d)
  obtain ⟨d', rfl⟩ :=
    (GlobalTheory.Published.AbelianDeRham.Rigid.crysToDR_bijective HR hAab hAg (isDPNilpotent_squareZero h) hπ hI hA).2 y
  have hsurj := (HR S AS g hASab hASg J (divided₂ hJ) (isDPNilpotent_squareZero hJ) S₀ πS hπS hJk AS₀ iS hAS).2
  have hm : mA.Corr d d' := fun c ↦ by
    obtain ⟨c0, rfl⟩ := hsurj c
    have k := (liftMor (divided₂ hJ) hAS).comp mA
    rw [GrpMor.pull_pull (liftMor (divided₂ hJ) hAS) mA k (fun _ ↦ rfl) rfl c0,
      ← GrpMor.pull_pull nA (liftMor (divided₂ h) hA) k (fun _ ↦ rfl) hiA c0]
    exact (crysToDR_apply _ hA d' _).symm.trans ((hy c0).trans (congrArg σ (crysToDR_apply _ hAS d c0)))
  have hd' : d' ∈ liftFil (divided₂ h) hA := by
    have hle : PrimitiveSubmodule A ≤ LinearMap.ker (crysToDR (divided₂ h) hA d') := by
      rw [hBCA.2, Submodule.span_le]
      rintro _ ⟨c, hc, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, hy c]
      rw [liftFil, Submodule.mem_comap, Fil, Submodule.mem_dualAnnihilator] at hd
      rw [hd c hc, map_zero]
    exact (Submodule.mem_dualAnnihilator _).2 fun c hc ↦ hle hc
  have hpush := hyp d' hd'
  have hcorr := GrpMor.Corr.push (m := mA) mB fS₀ f₀ hf.symm hm
  have hx := crysToDR_corr (divided₂ hJ) hBS hB mB nB hjB hcorr
  rw [liftFil, Submodule.mem_comap, Fil, Submodule.mem_dualAnnihilator]
  rw [liftFil, Submodule.mem_comap, Fil, Submodule.mem_dualAnnihilator] at hpush
  intro c hc
  apply hσ
  show σ _ = σ 0
  rw [map_zero]
  exact (hx c).symm.trans (hpush _ (nB.isMor.pullback1_mem_hodgeFiltration hc))

end GlobalTheory.SqLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogLiftPdivGroupFrame
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog.FrobQL

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q]

theorem in_add {σ : Type} {N : Ideal B} {f g : MvPowerSeries σ Q} (hf : In N f) (hg : In N g) :
    In N (f + g) := fun α => by
  obtain ⟨a, ha, e⟩ := hf α
  obtain ⟨b, hb, e'⟩ := hg α
  exact ⟨a + b, N.add_mem ha hb, by rw [map_add, e, e', map_add]⟩

theorem in_mono {σ : Type} {N N' : Ideal B} (h : N ≤ N') {f : MvPowerSeries σ Q} (hf : In N f) :
    In N' f := fun α => by
  obtain ⟨a, ha, e⟩ := hf α
  exact ⟨a, h ha, e⟩

theorem in_map {σ : Type} (t : B →+* B) (s : Q →+* Q)
    (hs : ∀ b, s (algebraMap B Q b) = algebraMap B Q (t b))
    {N N' : Ideal B} (hN : ∀ b ∈ N, t b ∈ N') {f : MvPowerSeries σ Q} (hf : In N f) :
    In N' (map s f) := fun α => by
  obtain ⟨a, ha, e⟩ := hf α
  exact ⟨t a, hN a ha, by rw [coeff_map, e, hs]⟩

theorem in_expand {σ : Type} (p : ℕ) (hp : p ≠ 0) {N : Ideal B} {f : MvPowerSeries σ Q}
    (hf : In N f) : In N (expand p hp f) := fun α => by
  by_cases h : ∀ i, p ∣ α i
  · obtain ⟨m, hm⟩ : ∃ m : σ →₀ ℕ, p • m = α := ⟨α.mapRange (fun a ↦ a / p) (by simp),
      by ext i; simp [Nat.mul_div_cancel' (h i)]⟩
    rw [← hm, coeff_expand_smul]
    exact hf m
  · push_neg at h
    obtain ⟨i, hi⟩ := h
    exact ⟨0, N.zero_mem, by rw [coeff_expand_of_not_dvd p hp f hi, map_zero]⟩

theorem frob_congr (p : ℕ) [Fact p.Prime] (t : B →+* B) (ht : ∀ b, (p : B) ∣ t b - b ^ p)
    (hu : ¬IsUnit (p : B)) {τ : Type} (w : MvPowerSeries τ B) (α : τ →₀ ℕ) :
    coeff α (w ^ p - expand p (Fact.out : p.Prime).ne_zero (map t w)) ∈
      Ideal.span {(p : B)} := by
  set I : Ideal B := Ideal.span {(p : B)}
  haveI : CharP (B ⧸ I) p := CharP.quotient B p (by simpa [mem_nonunits_iff] using hu)
  haveI : ExpChar (B ⧸ I) p := ExpChar.prime Fact.out
  have hw : map (Ideal.Quotient.mk I) (map t w) =
      map (frobenius (B ⧸ I) p) (map (Ideal.Quotient.mk I) w) := by
    ext n
    simp only [coeff_map, frobenius_def]
    rw [← map_pow, Ideal.Quotient.eq, Ideal.mem_span_singleton]
    exact ht _
  have key : map (Ideal.Quotient.mk I)
      (w ^ p - expand p (Fact.out : p.Prime).ne_zero (map t w)) = 0 := by
    rw [map_sub, map_pow, map_expand, hw, ← map_expand, map_frobenius_expand, sub_self]
  have := congrArg (coeff α) key
  rwa [coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem] at this

end GlobalTheory.QLog.FrobQL

namespace GlobalTheory.QLog.FrobQL

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q]

theorem frob_eq_expand (p : ℕ) (hp : p ≠ 0) {σ : Type} (s : Q →+* Q) (f : MvPowerSeries σ Q) :
    frob p s f = expand p hp (map s f) := by
  simp only [frob, expand, substAlgHom_apply]

theorem cob1_expand_frobenius_map (p : ℕ) (hp : p ≠ 0) (t : B →+* B) (s : Q →+* Q)
    (hs : ∀ b, s (algebraMap B Q b) = algebraMap B Q (t b)) {d : ℕ}
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) (h0 : ∀ i, constantCoeff (μ i) = 0)
    (f : MvPowerSeries (Fin d) Q) :
    cob1 (up Q μ) (expand p hp (map s f)) =
      (subst (up Q fun i => μ i ^ p) (map s f) -
        subst (up Q fun i => expand p hp (map t (μ i))) (map s f)) +
        expand p hp (map s (cob1 (up Q μ) f)) := by
  have hU : HasSubst (up Q μ) := hasSubst_of_constantCoeff_zero fun i => by
    simp [up, constantCoeff_map, h0]
  have hXp : HasSubst (fun i : Fin d => (X i : MvPowerSeries (Fin d) Q) ^ p) := HasSubst.X_pow hp
  have hL : HasSubst (fun i : Fin d => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) Q)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hR : HasSubst (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) Q)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hexp : ∀ {σ : Type} (g : MvPowerSeries σ Q), expand p hp g = subst (fun i => X i ^ p) g :=
    fun g => by simp only [expand, substAlgHom_apply]
  have hmapU : (fun i => map s (up Q μ i)) = up Q (fun i => map t (μ i)) := by
    funext i; ext n; simp [up, coeff_map, hs]
  have e1 : subst (up Q μ) (expand p hp (map s f)) = subst (up Q fun i => μ i ^ p) (map s f) := by
    rw [hexp, subst_comp_subst_apply hXp hU]
    congr 1
    funext i
    rw [subst_pow hU, subst_X hU]
    simp [up, map_pow]
  have e2 : inL (expand p hp (map s f)) = subst (fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) Q) ^ p) (map s f) := by
    rw [inL, hexp, subst_comp_subst_apply hXp hL]
    congr 1
    funext i
    rw [subst_pow hL, subst_X hL]
  have e3 : inR (expand p hp (map s f)) = subst (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) Q) ^ p) (map s f) := by
    rw [inR, hexp, subst_comp_subst_apply hXp hR]
    congr 1
    funext i
    rw [subst_pow hR, subst_X hR]
  have hV : HasSubst (up Q fun i => map t (μ i)) := hasSubst_of_constantCoeff_zero fun i => by
    simp [up, constantCoeff_map, h0]
  have m1 : map s (subst (up Q μ) f) = subst (up Q fun i => map t (μ i)) (map s f) := by
    rw [map_subst hU, hmapU]
  have m2 : map s (subst (fun i : Fin d => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) Q)) f) =
      subst (fun i : Fin d => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) Q)) (map s f) := by
    rw [map_subst hL]; congr 1; funext i; simp
  have m3 : map s (subst (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) Q)) f) =
      subst (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) Q)) (map s f) := by
    rw [map_subst hR]; congr 1; funext i; simp
  have x1 : expand p hp (subst (up Q fun i => map t (μ i)) (map s f)) =
      subst (up Q fun i => expand p hp (map t (μ i))) (map s f) := by
    rw [expand_subst p hp hV]; congr 1; funext i; simp [up, map_expand]
  have x2 : expand p hp (subst (fun i : Fin d => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) Q)) (map s f)) =
      subst (fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) Q) ^ p) (map s f) := by
    rw [expand_subst p hp hL]; congr 1; funext i; simp
  have x3 : expand p hp (subst (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) Q)) (map s f)) =
      subst (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) Q) ^ p) (map s f) := by
    rw [expand_subst p hp hR]; congr 1; funext i; simp
  have e4 : expand p hp (map s (cob1 (up Q μ) f)) =
      subst (up Q fun i => expand p hp (map t (μ i))) (map s f) -
        subst (fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) Q) ^ p) (map s f) -
        subst (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) Q) ^ p) (map s f) := by
    simp only [cob1, inL, inR, map_sub, m1, m2, m3, x1, x2, x3]
  rw [cob1, e1, e2, e3, e4]
  abel

end GlobalTheory.QLog.FrobQL

namespace GlobalTheory.QLog

open GlobalTheory.QLog.FrobQL in

theorem ql_frob : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O →
    ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ)
    (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' →
    (∀ i, map F.θ (μ' i) = c.μ i) → ∀ f : MvPowerSeries (Fin d) F.Q, QL μ' ⊤ f →
    QL μ' ⊤ (frob p F.s f) ∧
      (In (RingHom.ker F.θ) (cob1 (up F.Q μ') f) →
        QL μ' (Ideal.span {(p : F.B)}) (frob p F.s f)) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ ε hε F G d c μ' hμ _ f hf
  have hpp : p.Prime := Fact.out
  have hp : p ≠ 0 := hpp.ne_zero
  have hu : ¬IsUnit (p : F.B) := fun h =>
    (Fact.out : ¬IsUnit (p : O)) (by simpa using h.map F.θ)
  rw [frob_eq_expand p hp]
  have hc0 : constantCoeff (expand p hp (map F.s f)) = 0 := by
    rw [constantCoeff_expand, constantCoeff_map, hf.1, map_zero]
  have hlin : ∀ i, lin (expand p hp (map F.s f)) i = 0 := fun i => by
    unfold lin
    exact coeff_expand_of_not_dvd p hp _ (i := i) (by simpa using hpp.not_dvd_one)
  have hJ : ∀ x ∈ Ideal.span {(p : F.B)}, ∃ y ∈ Ideal.span {(p : F.B)}, x ^ p = p * y := by
    intro x hx
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    have e : (p : F.B) ^ p = p * p ^ (p - 1) := by
      rw [← pow_succ']; congr 1; have := hpp.one_lt; omega
    refine ⟨(p : F.B) ^ (p - 1) * b ^ p, Ideal.mul_mem_right _ _
      (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) _ (by have := hpp.one_lt; omega)), ?_⟩
    rw [mul_pow, e]; ring
  have hD : DIn (⊤ : Ideal F.B) (map F.s f) := by
    have h := GlobalTheory.T.divided_in_of_quasi_logarithm p F.B O F.Q F.θ F.frame d μ' hμ ⊤ f hf
    intro α i
    obtain ⟨b, _, e⟩ := h α i
    exact ⟨F.σ b, trivial, by rw [coeff_map, ← map_natCast F.s, ← map_mul, e, F.s_alg]⟩
  have hK := GlobalTheory.T.subst_sub_subst_mem_mul_of_coeff_sub_mem p F.B O F.Q F.θ F.frame _ hJ (Fin d) (Fin d ⊕ Fin d) ⊤ (map F.s f)
    (fun i => μ' i ^ p) (fun i => expand p hp (map F.σ (μ' i))) hD
    (fun i => by rw [map_pow, hμ.const i, zero_pow hp])
    (fun i => by rw [constantCoeff_expand, constantCoeff_map, hμ.const i, map_zero])
    (fun i α => frob_congr p F.σ F.σ_pow hu (μ' i) α)
  rw [Ideal.mul_top] at hK
  simp only [QL]
  rw [cob1_expand_frobenius_map p hp F.σ F.s F.s_alg μ' hμ.const f]
  refine ⟨⟨hc0, fun i => ⟨0, trivial, by rw [hlin, map_zero]⟩,
    in_add (in_mono le_top hK) (in_expand p hp (in_map F.σ F.s F.s_alg (N' := ⊤) (fun _ _ => Submodule.mem_top) hf.2.2))⟩,
    fun hker => ⟨hc0, fun i => ⟨0, Ideal.zero_mem _, by rw [hlin, map_zero]⟩,
      in_add hK (in_expand p hp (in_map F.σ F.s F.s_alg ?_ hker))⟩⟩
  intro b hb
  rw [RingHom.mem_ker] at hb
  obtain ⟨y, _, hy⟩ := F.frame.pd b hb
  obtain ⟨z, hz⟩ := F.σ_pow b
  rw [Ideal.mem_span_singleton]
  exact ⟨z + y, by rw [mul_add, ← hz, ← hy]; ring⟩

end GlobalTheory.QLog
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogReduces
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

open CategoryTheory TensorProduct MvPowerSeries in
private lemma mem_quasiLog_iff (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (h : _root_.GlobalTheory.Katz.IsLaw μ)
    (f : MvPowerSeries (Fin d) (_root_.GlobalTheory.Katz.Fr p k)) :
    f ∈ _root_.GlobalTheory.Katz.quasiLog p h ↔
      f ∈ _root_.GlobalTheory.Katz.quasiInt p k (Fin d) ∧
        _root_.GlobalTheory.Katz.cob1 (fun i => _root_.GlobalTheory.Katz.lift p (μ i)) f ∈
          _root_.GlobalTheory.Katz.intBy p k (Fin d ⊕ Fin d) 1 := by
  unfold _root_.GlobalTheory.Katz.quasiLog
  exact Iff.rfl

open CategoryTheory TensorProduct MvPowerSeries in
private lemma exists_lin_eq_algebraMap_of_mem_quasiInt (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    {d : ℕ} {f : MvPowerSeries (Fin d) (_root_.GlobalTheory.Katz.Fr p k)}
    (hf : f ∈ _root_.GlobalTheory.Katz.quasiInt p k (Fin d)) (i : Fin d) :
    ∃ a, _root_.GlobalTheory.Katz.lin f i = algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k) a := by
  obtain ⟨a, ha⟩ := hf (Finsupp.single i 1) i
  exact ⟨a, by simpa [_root_.GlobalTheory.Katz.lin] using ha⟩

open CategoryTheory TensorProduct MvPowerSeries in
private lemma isCoc_of_red_cob1_quasiInt (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k)
    (h : _root_.GlobalTheory.Katz.IsLaw μ) (f : MvPowerSeries (Fin d) (_root_.GlobalTheory.Katz.Fr p k))
    (hf : f ∈ _root_.GlobalTheory.Katz.quasiInt p k (Fin d))
    (c : MvPowerSeries (Fin d ⊕ Fin d) k)
    (hc : _root_.GlobalTheory.Katz.Red p
      (_root_.GlobalTheory.Katz.cob1 (fun i => _root_.GlobalTheory.Katz.lift p (μ i)) f) c) :
    _root_.GlobalTheory.Katz.IsCoc μ c := by
  obtain ⟨-, huniq, -, hadd, -, hdivp, -⟩ := _root_.GlobalTheory.Katz.red_rules p k (Fin d ⊕ Fin d)
  obtain ⟨-, huniq3, -, -, -, hdivp3, -⟩ :=
    _root_.GlobalTheory.Katz.red_rules p k (Fin d ⊕ Fin d ⊕ Fin d)
  obtain ⟨htwo, hswap⟩ := _root_.GlobalTheory.Katz.cob2_cob1_lift_mem_intBy_and_swap_sub_mem p k d μ h f hf
  obtain ⟨hcomm, -⟩ := _root_.GlobalTheory.Katz.red_coboundaries p k d μ
    h.const
  obtain ⟨hred2, hredswap⟩ := hcomm _ c hc
  unfold _root_.GlobalTheory.Katz.IsCoc
  refine ⟨huniq3 _ _ _ hred2 ((hdivp3 _).1 htwo), ?_⟩
  exact sub_eq_zero.1 (huniq _ _ _ (hadd _ _ _ _ hredswap hc).2 ((hdivp _).1 hswap))

open CategoryTheory TensorProduct MvPowerSeries in

theorem _root_.GlobalTheory.quasiLog_reduces : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (h : _root_.GlobalTheory.Katz.IsLaw μ), (∀ f ∈ _root_.GlobalTheory.Katz.quasiLog p h, ∃ c w, _root_.GlobalTheory.Katz.Red p (_root_.GlobalTheory.Katz.cob1 (fun i => _root_.GlobalTheory.Katz.lift p (μ i)) f) c ∧ _root_.GlobalTheory.Katz.RedV p (_root_.GlobalTheory.Katz.lin f) w) ∧ ∀ f ∈ _root_.GlobalTheory.Katz.quasiLog p h, ∀ c, _root_.GlobalTheory.Katz.Red p (_root_.GlobalTheory.Katz.cob1 (fun i => _root_.GlobalTheory.Katz.lift p (μ i)) f) c → _root_.GlobalTheory.Katz.IsCoc μ c := by
  intro p _ k _ _ _ d μ h
  refine ⟨fun f hf => ?_, fun f hf c hc => ?_⟩
  · obtain ⟨hint, hcob⟩ := (mem_quasiLog_iff p k d μ h f).1 hf
    obtain ⟨c, hc⟩ := ((_root_.GlobalTheory.Katz.red_rules p k (Fin d ⊕ Fin d)).1 _).1 hcob
    choose a ha using exists_lin_eq_algebraMap_of_mem_quasiInt p k hint
    exact ⟨c, fun i => WittVector.constantCoeff (a i), hc, fun i => ⟨a i, ha i, rfl⟩⟩
  · exact isCoc_of_red_cob1_quasiInt p k d μ h f
      ((mem_quasiLog_iff p k d μ h f).1 hf).1 c hc

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjOfStrictHenselisationPolynomialStatement
section
open GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.surj_of_strictHenselisation_polynomial_alt : ∀ (T : Type) [CommRing T] (A : Type) [CommRing A] [Algebra (Polynomial T) A] [Algebra T A] [IsScalarTower T (Polynomial T) A], SH A → (∀ a : A, ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E) (φ : E →ₐ[Polynomial T] A), a ∈ φ.range) → ∃ (O : Type) (_ : CommRing O) (_ : Algebra T O) (_ : Algebra (Polynomial T) O) (_ : IsScalarTower T (Polynomial T) O) (_ : HenselianLocalRing O) (_ : IsSepClosed (IsLocalRing.ResidueField O)) (π : O →ₐ[Polynomial T] A), Function.Surjective π ∧ (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E) (P : Ideal E) (_ : P.IsPrime), Nonempty (Localization.AtPrime P ≃ₐ[(Polynomial T)] Si i)) := by
  first | (exact @GlobalTheory.surj_of_strictHenselisation_polynomial) | (exact GlobalTheory.surj_of_strictHenselisation_polynomial) | (intros; apply GlobalTheory.surj_of_strictHenselisation_polynomial  <;> assumption)
end

