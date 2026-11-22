import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0318
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.Bundle0001
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0006
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BasicOpenRsLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0266
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PeriodBaseChange.OB
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0024
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0058
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Bundle0002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0305
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0282
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0317
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0297
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0289
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0299
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0319
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RootExtensionLift
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.Bundle0004
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationOfValuationModSquare
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfEig
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0094
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelToBSurjectiveStatement
section
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_toB_surjective : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), Function.Surjective (lev h k).toB := by
  first | exact @GlobalTheory.CompanionTheory.LatLevels.toB_surjective | exact GlobalTheory.CompanionTheory.LatLevels.toB_surjective | (intros; apply GlobalTheory.CompanionTheory.LatLevels.toB_surjective <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelXiMemIdealAndThetaCompatStatement
section
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_xi_mem_ideal_and_theta_compat : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), (lev h k).lam (algebraMap (Ainf l) (Acris l) (xi0 l)) ∈ (lev h k).I ∧ ∀ (a : OK l K) (w : Ainf l), theta0 l w = okToOC l K a → algebraMap (OK l K) (lev h k).A a - (lev h k).lam (algebraMap (Ainf l) (Acris l) w) ∈ (lev h k).I := by
  first | exact @GlobalTheory.CompanionTheory.LatC.Red.xi_and_sub_mem_I | exact GlobalTheory.CompanionTheory.LatC.Red.xi_and_sub_mem_I | (intros; apply GlobalTheory.CompanionTheory.LatC.Red.xi_and_sub_mem_I <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFrameDerivationCompat
section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

noncomputable section
namespace GlobalTheory.CompanionTheory.ConeLocal

section CoefIdeal
variable {X : Scheme.{0}} {V V' : X.Opens} (h : V ≤ V') {d m : ℕ}
  (D : Fin d → Γ(X, V) → Γ(X, V)) (κ : Fin m → Fin d)

theorem rs_mul_mem_jacSpan (b : Γ(X, V')) {y : Γ(X, V)} (hy : y ∈ jacSpan h (RingHom.id _) D κ) :
    rs h b * y ∈ jacSpan h (RingHom.id _) D κ := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b', bs, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨b * b', bs, ?_⟩
    simp only [RingHom.id_apply, map_mul, mul_assoc]
  | zero => rw [mul_zero]; exact zero_mem _
  | add _ _ _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
  | neg _ _ h1 => rw [mul_neg]; exact neg_mem h1

def coefIdeal (y : Γ(X, V)) : Ideal Γ(X, V') where
  carrier := {a | rs h a * y ∈ jacSpan h (RingHom.id _) D κ}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_add, add_mul]
    exact add_mem ha hb
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    rw [map_zero, zero_mul]
    exact zero_mem _
  smul_mem' b a ha := by
    simp only [Set.mem_setOf_eq, smul_eq_mul] at ha ⊢
    rw [map_mul, mul_assoc]
    exact rs_mul_mem_jacSpan h D κ b ha

theorem mem_coefIdeal {y : Γ(X, V)} {a : Γ(X, V')} :
    a ∈ coefIdeal h D κ y ↔ rs h a * y ∈ jacSpan h (RingHom.id _) D κ := Iff.rfl

theorem ideal_eq_top_of_local {U : X.Opens} (hU : IsAffineOpen U) (𝔠 : Ideal Γ(X, U))
    (H : ∀ x : X, x ∈ U → ∃ (f : Γ(X, U)) (M : ℕ), x ∈ X.basicOpen f ∧ f ^ M ∈ 𝔠) : 𝔠 = ⊤ := by
  by_contra hne
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal 𝔠 hne
  have hPp : P.IsPrime := hP.isPrime
  let p : PrimeSpectrum Γ(X, U) := ⟨P, hPp⟩
  have hxU : hU.fromSpec p ∈ U := by
    have : hU.fromSpec p ∈ Set.range hU.fromSpec := ⟨p, rfl⟩
    rwa [hU.range_fromSpec] at this
  obtain ⟨f, M, hx, hf⟩ := H _ hxU
  have hfP : f ∈ P := hPp.mem_of_pow_mem M (hle hf)
  have e : hU.fromSpec p ∈ X.basicOpen f := hx
  have e2 : p ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen f := e
  rw [hU.fromSpec_preimage_basicOpen] at e2
  exact e2 hfP

end CoefIdeal

theorem coef_mem_jacSpan : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q] (s : ℕ) {V V' : X.Opens} (hVV : V ≤ V'), IsAffineOpen V' → ∀ {d : ℕ} (c : Coord q V d),
    letI := (strV q V).toAlgebra
    ∀ (D : Fin d → Derivation K Γ(X, V) Γ(X, V)), (∀ k j, D k (c.t j) = if k = j then 1 else 0) →
    ∀ (E : Frame (sP (KS q s {V})) d) (ε : Γ(X, V) ≃+* (sP (KS q s {V})).A.obj E.D), IsLoc q s c.t E ε →
    ∀ (σ : ∀ T, E.D ⟶ T) (m : ℕ) (r : ℤ), r = m → m + 1 ≤ s → ∀ (ξ : HQ (KS q s {V'}) r (r + 1) m) (y : Idx m d → Γ(X, V)),
      CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {V}) r) (sFil (KS q s {V}) (r + 1)) (fun u => ∑ I : Idx m d, E.form σ I.1 (ε (y I)) u) (resKS q s hVV _ _ _ ξ) →
      ∀ I, y I ∈ jacSpan hVV (RingHom.id _) (fun k => D k) I.1 := by
  intro K _ _ X q _ s V V' hVV hV' d c
  intro D hD E ε hL σ m r hr hs ξ y hRep I
  have top : coefIdeal hVV (fun k => D k) I.1 (y I) = ⊤ := by
    refine ideal_eq_top_of_local hV' _ fun x hx => ?_
    obtain ⟨f, e, cu, hxf⟩ := GlobalTheory.CompanionTheory.ConeLocal.coord_near q hV' x hx
    obtain ⟨M, hM⟩ := GlobalTheory.CompanionTheory.ConeLocal.CoefMemLoc.main q s hVV hV' c D hD E ε hL σ m r hr hs f e cu ξ y hRep I
    exact ⟨f, M, hxf, hM⟩
  have h1 : (1 : Γ(X, V')) ∈ coefIdeal hVV (fun k => D k) I.1 (y I) := top ▸ Submodule.mem_top
  have h2 := (mem_coefIdeal hVV _ _).1 h1
  rwa [map_one, one_mul] at h2

end GlobalTheory.CompanionTheory.ConeLocal
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NilpotentIdentityMorphismCompatStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nilpotent_identity_morphism_compat : ∀ {O R R' : Type} [CommRing O] [CommRing R] [CommRing R'] [Algebra R R'] [Module.Flat R R'] {I : Ideal R}
    {I' : Ideal R'} {γ : DividedPowers I} {γ' : DividedPowers I'} {p : ℕ} (hp : p ≠ 0) (hn : IsNilpotent (p : R))
    {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {κ' : O →+* R' ⧸ I'}
    (m : NMor γ q κ γ' q κ' (algebraMap R R')) (hu : m.u = 𝟙 X) (hg : m.g = RingHom.id O) (U : Cov q)
    (Q : ObjectProperty (Thick (nlFun γ p X q κ))) (Q' : ObjectProperty (Thick (nlFun γ' p X q κ')))
    (hQ : Q = St ⊤ {⊤}) (hQ' : Q' = St ⊤ {⊤}) (h : ∀ T, Q' T → Q ((m.mor p).functor.obj T))
    (ha : ∀ a : R', (m.smor Q Q' h).LeC a (oT Q) (oT Q')) (hb : ∀ a : R', (m.smor Q Q' h).LeC a (oB Q) (oB Q')) (j : ℕ),
    Tens R (N := fun _ : Unit => R') (M := fun _ => CH.H (sq (oT Q) (oB Q)) j) (M' := CH.H (sq (oT Q') (oB Q')) j)
      fun _ a x => ((m.smor Q Q' h).sqC a (ha a) (hb a)).pull j x := by
  first | exact @GlobalTheory.CompanionTheory.BcCov.bc_cover | exact GlobalTheory.CompanionTheory.BcCov.bc_cover | (intros; apply GlobalTheory.CompanionTheory.BcCov.bc_cover <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneVectorFormulaOfParts
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open PositivityTheory.Rg.Mass

namespace GlobalTheory.CompanionTheory.Mass

theorem anisotropic_binary_one_vector_formula : Prop1 → Simil → Hasse → Cnt → E1 := by
  intro hP hS hH hC F E _ _ _ _ _ σ hcm J hJ hA T hT hd d b li lam hli hlam μ 𝓕 hμ h𝓕 mi m hmi hm
  obtain ⟨β, rfl, hβ, he⟩ := GlobalTheory.T.hermitian_one_by_one_is_scalar F E σ hcm T hT
  have hβ0 : β ≠ 0 := hβ hd
  simp only [he]
  have hsph : {X : Fin 1 → Fin 2 → E | gramE σ J X = fun _ _ => algebraMap F E β} = sph σ J β := rfl
  rw [hsph]
  obtain ⟨c, hc⟩ := hP F E σ J d b li lam μ 𝓕 mi m hcm hJ hA hli hlam hμ h𝓕 hmi hm β hβ0
  by_cases h0 : mi (hermScal (Ainf F) σ (algebraMap F _ β)) = 0 ∨
      ∃ v, m v (hermScal (Fv F v) σ (algebraMap F _ β)) = 0
  · rw [(GlobalTheory.T.euler_product_measure_zero F E σ hcm d b 1 2 _ c _ _).2.1 hc h0]
    exact (GlobalTheory.T.euler_product_measure_zero F E σ hcm d b 1 2 0 1 _ _).2.2 hc.1 hc.2.1 h0
  push Not at h0
  have hne : (sph σ J β).Nonempty :=
    hH F E σ J d b li lam μ 𝓕 mi m hcm hJ hA hli hlam hμ h𝓕 hmi hm β hβ0 h0.1
  have hall : ∀ β' : F, β' ≠ 0 → EP b μ 𝓕 mi m β' c := by
    intro β' hβ'
    by_cases hn : (sph σ J β').Nonempty
    · exact hS F E σ J d b li lam μ 𝓕 mi m hcm hJ hA hli hlam hμ h𝓕 hmi hm β β' hβ0 hβ' hne hn c hc
    · obtain ⟨c', hc'⟩ := hP F E σ J d b li lam μ 𝓕 mi m hcm hJ hA hli hlam hμ h𝓕 hmi hm β' hβ'
      have hz : mi (hermScal (Ainf F) σ (algebraMap F _ β')) = 0 := by
        by_contra hz
        exact hn (hH F E σ J d b li lam μ 𝓕 mi m hcm hJ hA hli hlam hμ h𝓕 hmi hm β' hβ' hz)
      have ht : thetaMeas σ J μ 𝓕 (sph σ J β') = 0 := by
        have he' : IsEmpty (sph σ J β') := Set.not_nonempty_iff_eq_empty.1 hn ▸ inferInstance
        simp [thetaMeas]
      unfold EP
      rw [ht]
      exact (GlobalTheory.T.euler_product_measure_zero F E σ hcm d b 1 2 0 c _ _).2.2 hc'.1 hc'.2.1 (Or.inl hz)
  have h1 : c = 1 := hC F E σ J d b li lam μ 𝓕 mi m hcm hJ hA hli hlam hμ h𝓕 hmi hm c hall
  exact h1 ▸ hc

end GlobalTheory.CompanionTheory.Mass
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingIsoOfComponentIsos
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.KunGlue.Transfer

variable {K : Type} [Field K]

theorem exCls (C : Cx.{1} K) {n : ℕ} (c : C.H n) : ∃ (x : C.X n) (hx : C.d n x = 0), C.cls x hx = c := by
  obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  exact ⟨x, hx, rfl⟩

theorem sub_mem_of_cls_eq {C : Cx.{1} K} {n : ℕ} {x y : C.X n} {hx : C.d n x = 0} {hy : C.d n y = 0}
    (h : C.cls x hx = C.cls y hy) : x - y ∈ C.B n :=
  (Submodule.Quotient.eq ((C.B n).submoduleOf (C.Z n)) (x := ⟨x, hx⟩) (y := ⟨y, hy⟩)).1 h

theorem cls_eq_of_sub_mem {C : Cx.{1} K} {n : ℕ} {x y : C.X n} {hx : C.d n x = 0} {hy : C.d n y = 0}
    (h : x - y ∈ C.B n) : C.cls x hx = C.cls y hy :=
  (Submodule.Quotient.eq ((C.B n).submoduleOf (C.Z n)) (x := ⟨x, hx⟩) (y := ⟨y, hy⟩)).2 h

theorem mapH_cls_eq {C D : Cx.{1} K} (φ : Cx.Hom C D (RingHom.id K)) {n : ℕ} (x : C.X n) (hx : C.d n x = 0)
    (h : D.d n (φ.f n x) = 0) : φ.mapH n (C.cls x hx) = D.cls (φ.f n x) h := rfl

theorem d_map_cocycle {C D : Cx.{1} K} (φ : Cx.Hom C D (RingHom.id K)) {n : ℕ} {x : C.X n} (hx : C.d n x = 0) :
    D.d n (φ.f n x) = 0 := by
  rw [φ.comm, hx, map_zero]

theorem d_mu_cocycle {A B M : Cx.{1} K} (pr : CxPairing A B M) {p q n : ℕ} (h : p + q = n) {x : A.X p} {y : B.X q}
    (hx : A.d p x = 0) (hy : B.d q y = 0) : M.d n (pr.μ h x y) = 0 := by
  rw [pr.leib, hx, hy]
  simp

theorem cls_mu_left {A B M : Cx.{1} K} (pr : CxPairing A B M) {p q n : ℕ} (h : p + q = n) {x x' : A.X p} {y : B.X q}
    {hx : A.d p x = 0} {hx' : A.d p x' = 0} (hy : B.d q y = 0) {hz : M.d n (pr.μ h x y) = 0}
    {hz' : M.d n (pr.μ h x' y) = 0} (e : A.cls x hx = A.cls x' hx') :
    M.cls (pr.μ h x y) hz = M.cls (pr.μ h x' y) hz' := by
  apply cls_eq_of_sub_mem
  have hb := sub_mem_of_cls_eq e
  rw [← LinearMap.sub_apply, ← map_sub]
  cases p with
  | zero =>
    have h0 : x - x' = 0 := hb
    rw [h0, map_zero, LinearMap.zero_apply]
    exact zero_mem _
  | succ p =>
    obtain ⟨w, hw⟩ := hb
    obtain rfl : n = (p + q) + 1 := by omega
    change _ ∈ LinearMap.range (M.d (p + q))
    refine ⟨pr.μ rfl w y, ?_⟩
    rw [pr.leib, hw, hy]
    simp

theorem cls_mu_right {A B M : Cx.{1} K} (pr : CxPairing A B M) {p q n : ℕ} (h : p + q = n) {x : A.X p} {y y' : B.X q}
    (hx : A.d p x = 0) {hy : B.d q y = 0} {hy' : B.d q y' = 0} {hz : M.d n (pr.μ h x y) = 0}
    {hz' : M.d n (pr.μ h x y') = 0} (e : B.cls y hy = B.cls y' hy') :
    M.cls (pr.μ h x y) hz = M.cls (pr.μ h x y') hz' := by
  apply cls_eq_of_sub_mem
  have hb := sub_mem_of_cls_eq e
  rw [← map_sub]
  cases q with
  | zero =>
    have h0 : y - y' = 0 := hb
    rw [h0, map_zero]
    exact zero_mem _
  | succ q =>
    obtain ⟨w, hw⟩ := hb
    obtain rfl : n = (p + q) + 1 := by omega
    change _ ∈ LinearMap.range (M.d (p + q))
    refine ⟨(-1 : ℤ) ^ p • pr.μ rfl x w, ?_⟩
    rw [map_zsmul, pr.leib, hw, hx]
    simp [smul_smul, ← mul_pow]

def sumCongr {I : Type} [DecidableEq I] {A B : I → Type 1} [∀ i, AddCommGroup (A i)] [∀ i, AddCommGroup (B i)]
    [∀ i, Module K (A i)] [∀ i, Module K (B i)] (e : ∀ i, A i ≃ₗ[K] B i) : (⨁ i, A i) ≃ₗ[K] ⨁ i, B i :=
  DFinsupp.mapRange.linearEquiv e

theorem sumCongr_lof {I : Type} [DecidableEq I] {A B : I → Type 1} [∀ i, AddCommGroup (A i)] [∀ i, AddCommGroup (B i)]
    [∀ i, Module K (A i)] [∀ i, Module K (B i)] (e : ∀ i, A i ≃ₗ[K] B i) (i : I) (x : A i) :
    sumCongr e (DirectSum.lof K I A i x) = DirectSum.lof K I B i (e i x) :=
  DFinsupp.mapRange_single (hf := fun i => map_zero (e i))

theorem kunE_iff : ∀ {K : Type} [Field K] {P P' Q Q' T T' : ℕ → Cx.{1} K} (pr : ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P a) (Q a') (T c)) (pr' : ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P' a) (Q' a') (T' c)) (p : ∀ a, Cx.Hom (P a) (P' a) (RingHom.id K)) (f : ∀ a, Cx.Hom (Q a) (Q' a) (RingHom.id K)) (g : ∀ a, Cx.Hom (T a) (T' a) (RingHom.id K)), (∀ a n, Function.Bijective ((p a).mapH n)) → (∀ a n, Function.Bijective ((f a).mapH n)) → (∀ a n, Function.Bijective ((g a).mapH n)) → (∀ {a a' c : ℕ} (ha : a + a' = c) {i j n : ℕ} (h : i + j = n) (x : (P a).X i) (y : (Q a').X j), (g c).f n ((pr ha).μ h x y) = (pr' ha).μ h ((p a).f i x) ((f a').f j y)) → (KunE pr ↔ KunE pr') := by
  intro K _ P P' Q Q' T T' pr pr' p f g hp hf hg hc
  let eP : ∀ a n, (P a).H n ≃ₗ[K] (P' a).H n := fun a n => LinearEquiv.ofBijective ((p a).mapH n) (hp a n)
  let eQ : ∀ a n, (Q a).H n ≃ₗ[K] (Q' a).H n := fun a n => LinearEquiv.ofBijective ((f a).mapH n) (hf a n)
  let eT : ∀ a n, (T a).H n ≃ₗ[K] (T' a).H n := fun a n => LinearEquiv.ofBijective ((g a).mapH n) (hg a n)
  let eS : ∀ c n : ℕ, (⨁ t : Idx c n, (P t.a).H t.i ⊗[K] (Q t.a').H t.j) ≃ₗ[K]
      ⨁ t : Idx c n, (P' t.a).H t.i ⊗[K] (Q' t.a').H t.j :=
    fun c n => sumCongr fun t => TensorProduct.congr (eP t.a t.i) (eQ t.a' t.j)
  have hS : ∀ (c n : ℕ) (t : Idx c n) (x : (P t.a).X t.i) (y : (Q t.a').X t.j) (hx : (P t.a).d t.i x = 0)
      (hy : (Q t.a').d t.j y = 0),
      eS c n (DirectSum.lof K _ (fun t : Idx c n => (P t.a).H t.i ⊗[K] (Q t.a').H t.j) t
        ((P t.a).cls x hx ⊗ₜ (Q t.a').cls y hy)) =
      DirectSum.lof K _ (fun t : Idx c n => (P' t.a).H t.i ⊗[K] (Q' t.a').H t.j) t
        ((P' t.a).cls ((p t.a).f t.i x) (d_map_cocycle _ hx) ⊗ₜ (Q' t.a').cls ((f t.a').f t.j y) (d_map_cocycle _ hy)) := by
    intro c n t x y hx hy
    exact sumCongr_lof _ t _
  have hG : ∀ {a a' c : ℕ} (ha : a + a' = c) {i j n : ℕ} (h : i + j = n) (x : (P a).X i) (y : (Q a').X j)
      (hz : (T c).d n ((pr ha).μ h x y) = 0) (hz' : (T' c).d n ((pr' ha).μ h ((p a).f i x) ((f a').f j y)) = 0),
      eT c n ((T c).cls ((pr ha).μ h x y) hz) = (T' c).cls ((pr' ha).μ h ((p a).f i x) ((f a').f j y)) hz' := by
    intro a a' c ha i j n h x y hz hz'
    have e0 := hc ha h x y
    change (T' c).cls ((g c).f n ((pr ha).μ h x y)) (d_map_cocycle _ hz) = _
    exact cls_eq_of_sub_mem (by rw [e0, sub_self]; exact zero_mem _)
  constructor
  · intro H c n
    obtain ⟨e, he⟩ := H c n
    refine ⟨(eS c n).symm ≪≫ₗ e ≪≫ₗ eT c n, ?_⟩
    intro t x y hx hy hz
    obtain ⟨x0, hx0, e1⟩ := exCls (P t.a) ((eP t.a t.i).symm ((P' t.a).cls x hx))
    obtain ⟨y0, hy0, e2⟩ := exCls (Q t.a') ((eQ t.a' t.j).symm ((Q' t.a').cls y hy))
    have e1' : (P' t.a).cls ((p t.a).f t.i x0) (d_map_cocycle _ hx0) = (P' t.a).cls x hx := by
      have := congrArg (eP t.a t.i) e1
      rwa [LinearEquiv.apply_symm_apply] at this
    have e2' : (Q' t.a').cls ((f t.a').f t.j y0) (d_map_cocycle _ hy0) = (Q' t.a').cls y hy := by
      have := congrArg (eQ t.a' t.j) e2
      rwa [LinearEquiv.apply_symm_apply] at this
    have hS' := hS c n t x0 y0 hx0 hy0
    rw [e1', e2'] at hS'
    have hz0 := d_mu_cocycle (pr t.ha) t.h hx0 hy0
    have hz1 := d_mu_cocycle (pr' t.ha) t.h (d_map_cocycle (p t.a) hx0) (d_map_cocycle (f t.a') hy0)
    have hz2 := d_mu_cocycle (pr' t.ha) t.h hx (d_map_cocycle (f t.a') hy0)
    simp only [LinearEquiv.trans_apply]
    rw [← hS', LinearEquiv.symm_apply_apply, he t x0 y0 hx0 hy0 hz0, hG t.ha t.h x0 y0 hz0 hz1,
      cls_mu_left (pr' t.ha) t.h (d_map_cocycle (f t.a') hy0) (hz' := hz2) e1',
      cls_mu_right (pr' t.ha) t.h hx (hz' := hz) e2']
  · intro H c n
    obtain ⟨e, he⟩ := H c n
    refine ⟨eS c n ≪≫ₗ e ≪≫ₗ (eT c n).symm, ?_⟩
    intro t x y hx hy hz
    have hz1 := d_mu_cocycle (pr' t.ha) t.h (d_map_cocycle (p t.a) hx) (d_map_cocycle (f t.a') hy)
    simp only [LinearEquiv.trans_apply]
    rw [hS c n t x y hx hy, he t _ _ _ _ hz1, ← hG t.ha t.h x y hz hz1, LinearEquiv.symm_apply_apply]

end GlobalTheory.CompanionTheory.KunGlue.Transfer
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingRestrictCompat
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

namespace GlobalTheory.CompanionTheory.KunGlue

theorem pr_res : ∀ {K : Type} [Field K] (E : XD K) {U₁ U₁' : ObjectProperty E.C₁} {U₂ U₂' : ObjectProperty E.C₂} {U₃ U₃' : ObjectProperty E.D} (h₁ : ∀ T, U₃ T → U₁ (E.L₁.obj T)) (h₂ : ∀ T, U₃ T → U₂ (E.L₂.obj T)) (h₁' : ∀ T, U₃' T → U₁' (E.L₁.obj T)) (h₂' : ∀ T, U₃' T → U₂' (E.L₂.obj T)) (k₁ : U₁' ≤ U₁) (k₂ : U₂' ≤ U₂) (k₃ : U₃' ≤ U₃) {a a' c : ℕ} (ha : a + a' = c) {i j n : ℕ} (hn : i + j = n) (x : CH.Cn (U₁.ι ⋙ E.F₁ a) i) (y : CH.Cn (U₂.ι ⋙ E.F₂ a') j), (resU (E.F₃ c) k₃).pullC n ((E.pr U₁ U₂ U₃ h₁ h₂ ha).μ hn x y) = (E.pr U₁' U₂' U₃' h₁' h₂' ha).μ hn ((resU (E.F₁ a) k₁).pullC i x) ((resU (E.F₂ a') k₂).pullC j y) := by
  intro K _ E U₁ U₁' U₂ U₂' U₃ U₃' h₁ h₂ h₁' h₂' k₁ k₂ k₃ a a' c ha i j n hn x y
  funext s
  rfl

end GlobalTheory.CompanionTheory.KunGlue
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PlaneStrongApproxHolds
section
noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

namespace GlobalTheory.CompanionTheory.PlaneSA

theorem aniso {F : Type} [Field F] [NumberField F] (d β : F) (hanis : ∀ x : Q d β F, qn x = 0 → x = 0)
    (s : Pl F) (hs : ∃ x : Q d β (Kp s), x ≠ 0 ∧ qn x = 0) : QSA d β s := by
  have hd0 : d ≠ 0 := by
    rintro rfl
    have := hanis ⟨0, 1, 0, 0⟩ (by simp [qn])
    simpa using congrArg QuaternionAlgebra.imI this
  have hβ0 : β ≠ 0 := by
    rintro rfl
    have := hanis ⟨0, 0, 1, 0⟩ (by simp [qn])
    simpa using congrArg QuaternionAlgebra.imJ this
  have one_mem : (1 : Q d β (AF F)) ∈ SAQ d β s :=
    ⟨1, qn_one, 1, ⟨qn_one, fun u _ => map_one _⟩, by simp⟩
  intro T g hg
  refine GlobalTheory.T.support_product_over_places d β _ (subset_closure one_mem) (GlobalTheory.T.strong_approx_closure_mul d β s) (fun w a ha => ?_) T hg
  by_cases hw : w = s
  · subst hw
    exact subset_closure ⟨1, qn_one, a, ha, by simp⟩
  · have hreg := GlobalTheory.T.support_closure_regular_trace d β hd0 hβ0 w a ha
    refine closure_minimal (fun a' ha' => ?_) isClosed_closure hreg
    obtain ⟨c, hc⟩ := GlobalTheory.T.quaternion_norm_one_conj_closure d β hanis s w hs hw a' ha'.1 ha'.2
    exact GlobalTheory.T.closure_conjugation_invariant d β hanis s w a' ha'.1 c hc

theorem plane : Sa2.PropPlane := by
  refine GlobalTheory.T.plane_prop_of_all_strong_approx ?_
  intro F E _ _ _ _ _ σ hcm β hβ
  obtain ⟨d, hd, ξ, hξ, hσ⟩ := GlobalTheory.T.cm_extension_imaginary_generator σ hcm
  refine GlobalTheory.T.plane_approx_of_quaternion_approx σ hcm β hβ d hd ξ hξ hσ fun s hs => ?_
  by_cases hanis : ∀ x : Q d β F, qn x = 0 → x = 0
  · exact aniso d β hanis s hs
  · push Not at hanis
    obtain ⟨x, hx, hx0⟩ := hanis
    exact GlobalTheory.T.quaternion_isotropic_split_all_places d β hd hβ ⟨x, hx0, hx⟩ s

end GlobalTheory.CompanionTheory.PlaneSA
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictSelfPullCEq
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

namespace GlobalTheory.CompanionTheory.KunGlue

theorem resU_self_pullC : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) (U : ObjectProperty C) (k : U ≤ U) (n : ℕ) (x : CH.Cn (U.ι ⋙ F) n), (resU F k).pullC n x = x := by
  intro R _ C _ F U k n x
  funext s
  rfl

end GlobalTheory.CompanionTheory.KunGlue
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RootExtensionLiftStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_extension_lift : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {F : Fn O} {κ : O →+* OC l} {d : ℕ} {s : F.Small d} (𝒯 : Tower κ s) (k : Bool) (n : ℕ) (𝓛 : Lift s.a (fun k => (s.T k : s.R)) (bs l k n).R (bs l k n).I (κb κ k n)) (δ : DividedPowers ((bs l k n).I.map 𝓛.i)) (hδ : IsDPMorphism (bs l k n).γ δ 𝓛.i) (hp : (bs l k n).p ≠ 0) (hn : IsNilpotent ((bs l k n).p : (bs l k n).R)) (X : RootExt l 𝓛.D 𝓛.t) (θ : liftObj s (b := bs l k n) rfl 𝓛 δ hδ hp hn ⟶ (gE F κ k n).obj 𝒯.obj), n ≠ 0 → (∀ j, θ.φ (𝓛.t j) = 𝒯.A.toAcr n (WittVector.teichmuller l (𝒯.c j 0 : 𝒯.A.A))) → ∃ e : X.E →+* 𝒯.A.Acr n, Function.Bijective e ∧ (∀ z, e (algebraMap 𝓛.D X.E z) = θ.φ z) ∧ ∀ j m, e (X.r j m) = 𝒯.A.toAcr n (WittVector.teichmuller l (𝒯.c j m : 𝒯.A.A)) := by
  first | exact @GlobalTheory.CompanionTheory.TowerAcr.tower_acr | exact GlobalTheory.CompanionTheory.TowerAcr.tower_acr | (intros; apply GlobalTheory.CompanionTheory.TowerAcr.tower_acr <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientOfNonNilpotentVariant
section
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2

namespace GlobalTheory.CompanionTheory.HeckeSub

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_iterate_eq_zero_of_subquot {V U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
    {K : Subgroup (GL ι F)} {e : GL ι F → ℂ} (hE : IsHk K e) (π : Representation ℂ (GL ι F) V)
    (ρ : Representation ℂ (GL ι F) U) (hρ : IsSmooth ρ) (hfl : HasFiniteLength ρ)
    (hkill : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (GL ι F) W), IsSmooth τ →
      τ.IsIrreducible → IsSubquotient τ ρ → IsEmpty (τ.Equiv π) → ∀ w ∈ fixed τ K, hk τ K e w = 0)
    (hns : ¬ IsSubquotient π ρ) (S : Subrepresentation ρ) :
    ∃ r : ℕ, ∀ u ∈ S.toSubmodule, u ∈ fixed ρ K → (hk ρ K e)^[r] u = 0 := by
  obtain ⟨hGT, hLT⟩ := (hasFiniteLength_iff_wellFounded ρ).1 hfl
  induction S using WellFoundedLT.induction with
  | ind S ih =>
    by_cases hS : S = ⊥
    · subst hS
      exact ⟨0, fun u hu _ => hu⟩
    obtain ⟨T, hT, hmax⟩ := (wellFounded_gt (α := Subrepresentation ρ)).has_min {T | T < S}
      ⟨⊥, bot_lt_iff_ne_bot.2 hS⟩
    have hcov : T ⋖ S := ⟨hT, fun c h1 h2 => hmax c h2 h1⟩
    let p : S.toRepresentation.IntertwiningMap (subQuot S T) := ⟨Submodule.mkQ _, fun _ => rfl⟩
    have hsq : IsSubquotient (subQuot S T) ρ := ⟨S, p, Submodule.mkQ_surjective _⟩
    have hne : IsEmpty ((subQuot S T).Equiv π) := ⟨fun φ => hns
      ((IsSubquotient.trans (IsSubquotient.of_injective φ.symm.toIntertwiningMap φ.symm.toLinearEquiv.injective) hsq))⟩
    obtain ⟨r, hr⟩ := ih T hT
    refine ⟨r + 1, fun u huS hufix => ?_⟩
    have hfixS : (Submodule.mkQ _ (⟨u, huS⟩ : S.toSubmodule) :
        S.toSubmodule ⧸ T.toSubmodule.comap S.toSubmodule.subtype) ∈ fixed (subQuot S T) K := by
      intro h
      have h1 : ρ (h : GL ι F) u = u := by simpa using hufix h
      have h2 : S.toRepresentation (h : GL ι F) ⟨u, huS⟩ = ⟨u, huS⟩ := Subtype.ext h1
      simp only [MonoidHom.one_apply, Units.val_one, one_smul]
      exact congrArg (Submodule.mkQ _) h2
    have h0 := hkill _ (subQuot S T) (hsq.isSmooth hρ) (isIrreducible_subQuot hcov) hsq hne _ hfixS
    have h1 : (hk S.toRepresentation K e ⟨u, huS⟩ : S.toSubmodule).1 = hk ρ K e u :=
      hk_map S.toRepresentation ρ S.toSubmodule.subtype (fun _ _ => rfl) hE ⟨u, huS⟩
    have h2 := hk_map S.toRepresentation (subQuot S T) (Submodule.mkQ _) (fun _ _ => rfl) hE ⟨u, huS⟩
    rw [h0] at h2
    have h3 : hk ρ K e u ∈ T.toSubmodule := by
      rw [← h1]
      exact (Submodule.Quotient.mk_eq_zero (T.toSubmodule.comap S.toSubmodule.subtype)).1 h2
    rw [Function.iterate_succ_apply]
    exact hr _ h3 (GlobalTheory.CompanionTheory.HeckeFix.hk_mem_fixed F ι K e hE U ρ u hufix).1

theorem subOfNonNil_of_subquot : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ι : Type) [Fintype ι] [DecidableEq ι], SubOfNonNil' F ι := by
  intro F _ _ _ _ ι _ _ K e hE V _ _ π _ _ U _ _ ρ hρ hfl hkill hnil
  by_contra hns
  obtain ⟨r, hr⟩ := exists_iterate_eq_zero_of_subquot hE π ρ hρ hfl hkill hns ⊤
  obtain ⟨u, hu, hne⟩ := hnil r
  exact hne (hr u trivial hu)

end GlobalTheory.CompanionTheory.HeckeSub
end

