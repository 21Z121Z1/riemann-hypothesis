import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0974
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0719
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0016
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0029
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0824
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0831
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0444
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0081
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0078
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0962
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0137
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0837
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0943
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0952
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0975
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0933
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0967
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2256
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0959
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGoodOfBddAll
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0028

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmT4OfRationalRowsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admT4_of_rational_rows : GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), ∀ G : GalSide D, (∀ i, D.ntw.NonzeroIndexPlace i → ∀ j b, RatRow Y.YS X.geo.v₀ Y.Z.good i j b) → XiBdd Y.Z.rd → (∀ j, GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.HkSupAt X.core X.R.toRealDat j) → GlobalTheory.TripleLocal.GalHodge D G.wd → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (Formalism.L2.Host.embLL0 D).fieldRange) → ∃ N0, Inputs D E N0 := by
  first | exact @GlobalTheory.TwInputs.inputs_of_sides | exact GlobalTheory.TwInputs.inputs_of_sides | (intros; apply GlobalTheory.TwInputs.inputs_of_sides <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardDivisionPointsHalfSplitPlaceNormPowStatement
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_divisionPoints_half_split_place_norm_pow : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D), Formalism.L2.NTheta.IsIdemAt e P → ∀ N : ℕ, 0 < N → Nat.card (GlobalTheory.DivPtFourier.DQ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) e N) = Ideal.absNorm (P.maxPowDividing (Ideal.span {((N : ℕ) : 𝓞 D.host.E)})) ^ (S.rank * T.rank) := by
  first | exact @GlobalTheory.DivPtLocal.natCard_DQ | exact GlobalTheory.DivPtLocal.natCard_DQ | (intros; apply GlobalTheory.DivPtLocal.natCard_DQ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjFunBaseRoot
section
set_option autoImplicit false

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.ConjRefTup

section IdempotentCombination
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {T : CoreJ D}
  [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
  (O : OMDat T.toCore R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (τ : ℂ ≃+* ℂ)

theorem conj_sum_eq (hZ : ConjFun O κ τ 1 (fun _ => 0) (fun _ => 0)) {Φ : GA D (Wc D i) → ℂ} {n m : ℕ} {a : Fin n → ℂ}
    {b : Fin m → ℂ} {f : Fin n → T.toCore.cuspA ((i : ℕ) + 1) (wtA κ) κ.n} {g : Fin m → T.toCore.cuspA ((i : ℕ) + 1) (wtA κ) κ.n}
    (ha : Expands O κ Φ a f) (hb : Expands O κ Φ b g) (x : GA D (Wc D i)) :
    ∑ k, τ (a k) * ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) *
      O.phi (T.cE ((i : ℕ) + 1) O.s0) (f k : T.toCore.R ((i : ℕ) + 1)) x) =
    ∑ k, τ (b k) * ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) *
      O.phi (T.cE ((i : ℕ) + 1) O.s0) (g k : T.toCore.R ((i : ℕ) + 1)) x) := by
  have h0 : Expands O κ (fun _ => 0) (Fin.append a (fun k => -b k)) (Fin.append f g) := by
    intro y
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, neg_mul, Finset.sum_neg_distrib]
    rw [← ha y, ← hb y, add_neg_cancel]
  have h1 := hZ.2 _ _ _ h0 x
  rw [Fin.sum_univ_add] at h1
  simp only [Fin.append_left, Fin.append_right, map_neg, one_mul, neg_mul, Finset.sum_neg_distrib] at h1
  linear_combination (-1 : ℂ) * h1

theorem conjFun_lin (hZ : ConjFun O κ τ 1 (fun _ => 0) (fun _ => 0)) {Φ Φ' Ψ Ψ' : GA D (Wc D i) → ℂ}
    (h1 : ConjFun O κ τ 1 Φ Φ') (h2 : ConjFun O κ τ 1 Ψ Ψ') (c d : ℂ) :
    ConjFun O κ τ 1 (fun x => c * Φ x + d * Ψ x) (fun x => τ c * Φ' x + τ d * Ψ' x) := by
  obtain ⟨n, a, f, ha⟩ := h1.1
  obtain ⟨m, b, g, hb⟩ := h2.1
  have hs : Expands O κ (fun x => c * Φ x + d * Ψ x) (Fin.append (fun k => c * a k) (fun k => d * b k)) (Fin.append f g) := by
    intro x
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rw [ha x, hb x, Finset.mul_sum, Finset.mul_sum]
    simp only [mul_assoc]
  refine ⟨⟨_, _, _, hs⟩, fun N e h he x => ?_⟩
  simp only [one_mul]
  rw [conj_sum_eq O κ τ hZ he hs x, Fin.sum_univ_add, h1.2 _ _ _ ha x, h2.2 _ _ _ hb x]
  simp only [Fin.append_left, Fin.append_right, one_mul, map_mul, Finset.mul_sum, mul_assoc]

theorem conjFun_sum (hZ : ConjFun O κ τ 1 (fun _ => 0) (fun _ => 0)) : ∀ (n : ℕ) (α : Fin n → ℂ)
    (Φ Φ' : Fin n → GA D (Wc D i) → ℂ), (∀ k, ConjFun O κ τ 1 (Φ k) (Φ' k)) →
    ConjFun O κ τ 1 (fun g => ∑ k, α k * Φ k g) (fun g => ∑ k, τ (α k) * Φ' k g) := by
  intro n
  induction n with
  | zero => intro α Φ Φ' _; simpa using hZ
  | succ n ih =>
    intro α Φ Φ' hk
    have h := conjFun_lin O κ τ hZ (hk 0) (ih (fun k => α k.succ) (fun k => Φ k.succ) (fun k => Φ' k.succ)
      (fun k => hk k.succ)) (α 0) 1
    simp only [map_one, one_mul] at h
    simpa only [Fin.sum_univ_succ] using h

end IdempotentCombination

set_option maxHeartbeats 1000000 in

theorem conjFun_base_root : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → Finite T0 → Nonempty (FWTie T R κ v₀) → IoExt R → QGuard R → ∀ i : Fin D.R.m, OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC (O i).c') (O i).c0' c → ∃ ζ₁ : ℂ, IsRoot1 ζ₁ ∧ ∀ τ : ℂ ≃+* ℂ, FixBase T R i τ → ∀ y y' : (R.HV i A.μ0).H, ConjForm R i τ c A.μ0 A.μ0 y y' → ConjFun (O i) (κ i) τ 1 (fun g => ζ₁ * ph i * R.thF i A.μ0 y (v₀ i (sg0 D A)) g) (fun g => ζ₁ * ph i * R.thF i A.μ0 y' (v₀ i (sg0 D A)) g) := by
  intro hC D G _ _ Pl0 T0 A T _ R F κ v₀ O ph hnV hcore hfin hfw hio hQ i hpins hphase c hc
  have h2 := GlobalTheory.T.exists_normalisedData_normalCoefficientField D G Pl0 T0 A T R F κ v₀ O hcore hfin hfw hQ i hpins
  obtain ⟨M, hMp, hMl, hMe, hMn, hMc, hMx, hMs⟩ := h2
  have h3 := GlobalTheory.T.exists_rootOfUnity_coverFunction_reference_tuple hC D G Pl0 T0 A T R F κ v₀ O ph hnV hcore hfin hfw hio hQ i hpins hphase M hMp hMl hMe hMn hMc hMx hMs
  have h4 := GlobalTheory.T.referenceTuple_lifts_equivariant_rootOfUnity hC D G Pl0 T0 A T R F κ v₀ O ph hnV hcore hfin hfw hio hQ i hpins hphase M hMp hMl hMe hMn hMc hMx hMs h3.choose h3.choose_spec.1 h3.choose_spec.2
  refine ⟨h4.choose, h4.choose_spec.1, fun τ hB y y' hyy => ?_⟩
  have hP := h4.choose_spec.2
  let τa : ℂ ≃ₐ[ℚ] ℂ := AlgEquiv.ofRingEquiv (f := τ) (fun q => by simp)
  haveI := hMn
  let ta : M.c'.F ≃+* M.c'.F := (τa.restrictNormal M.c'.F).toRingEquiv
  have hta : ∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ) := fun a => AlgEquiv.restrictNormal_commutes τa M.c'.F a
  have hct : ConjTup R τ A.μ0 A.μ0 := by
    refine ⟨rfl, fun x => ?_⟩
    have h1 := hcore.lev.xi A.μ0
    rw [hcore.lev.xi_base] at h1
    rw [GlobalTheory.ChrEqUnique.eq_one_of_chrEq h1 x]
    simp
  have h5 := GlobalTheory.T.conjugate_definiteForms_descend_numberField D G Pl0 T0 A T R F κ v₀ hcore hfw i T0 id M hMp τ ta hta hB c ((hMe c).1 hc) hMx A.μ0 A.μ0 hct y y' hyy
  obtain ⟨n, α, ys, ys', hy, hy', hk⟩ := h5
  have hZ : ConjFun (O i) (κ i) τ 1 (fun _ => 0) (fun _ => 0) := by
    have := hP τ ta hta hB 0 0 (fun h => ⟨0, 0, by simp, by rw [map_zero, map_zero]; rfl, by rw [map_zero, map_zero]; rfl⟩)
    simpa using this
  have hL := conjFun_sum (O i) (κ i) τ hZ n α
    (fun k g => h4.choose * ph i * R.thF i A.μ0 (ys k) (v₀ i (sg0 D A)) g)
    (fun k g => h4.choose * ph i * R.thF i A.μ0 (ys' k) (v₀ i (sg0 D A)) g) (fun k => hP τ ta hta hB (ys k) (ys' k) (hk k))
  subst hy hy'
  convert hL using 2 with g g
  · simp only [map_sum, map_smul, MultilinearMap.sum_apply, MultilinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => by ring
  · simp only [map_sum, map_smul, MultilinearMap.sum_apply, MultilinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => by ring

end GlobalTheory.ConjRefTup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateThetaLiftsIsConjugateCuspExpansion
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ConjCombine

variable {X B : Type} (φ : B → X → ℂ) (τ : ℂ ≃+* ℂ)

def Exp (Φ : X → ℂ) {n : ℕ} (a : Fin n → ℂ) (F : Fin n → B) : Prop :=
  ∀ g, Φ g = ∑ k, a k * φ (F k) g

def CF (ζ : ℂ) (Φ Φ' : X → ℂ) : Prop :=
  (∃ (n : ℕ) (a : Fin n → ℂ) (F : Fin n → B), Exp φ Φ a F) ∧
    ∀ (n : ℕ) (a : Fin n → ℂ) (F : Fin n → B), Exp φ Φ a F → Exp φ Φ' (fun k => ζ * τ (a k)) F

variable {φ τ}

theorem conj_wd {Ψ Ψ' : X → ℂ} (h0 : CF φ τ 1 Ψ Ψ') {Φ : X → ℂ} {n m : ℕ} {a : Fin n → ℂ} {F : Fin n → B}
    {b : Fin m → ℂ} {G : Fin m → B} (ha : Exp φ Φ a F) (hb : Exp φ Φ b G) (g : X) :
    ∑ k, τ (a k) * φ (F k) g = ∑ k, τ (b k) * φ (G k) g := by
  obtain ⟨p, c, H, hc⟩ := h0.1
  have hall : Exp φ Ψ (Fin.append c (Fin.append a (-b))) (Fin.append H (Fin.append F G)) := by
    intro x
    rw [Fin.sum_univ_add, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
    rw [hc x, ← ha x, ← hb x]
    ring
  have e1 := h0.2 _ _ _ hc g
  have e2 := h0.2 _ _ _ hall g
  rw [Fin.sum_univ_add, Fin.sum_univ_add] at e2
  simp only [Fin.append_left, Fin.append_right, Pi.neg_apply, map_neg, one_mul, neg_mul,
    Finset.sum_neg_distrib] at e1 e2
  rw [e1] at e2
  linear_combination -e2

theorem conj_comb {Ψ Ψ' : X → ℂ} (h0 : CF φ τ 1 Ψ Ψ') {m : ℕ} (β : Fin m → ℂ) (Φs Φs' : Fin m → X → ℂ)
    (h : ∀ k, CF φ τ 1 (Φs k) (Φs' k)) (c : ℂ) :
    CF φ τ c (fun g => ∑ k, β k * Φs k g) (fun g => c * ∑ k, τ (β k) * Φs' k g) := by
  choose n b G hG using fun k => (h k).1
  let e := (finSigmaFinEquiv (n := n)).symm
  have hflat : Exp φ (fun g => ∑ k, β k * Φs k g) (fun q => β (e q).1 * b (e q).1 (e q).2)
      (fun q => G (e q).1 (e q).2) := by
    intro g
    rw [Fintype.sum_equiv e (fun q => β (e q).1 * b (e q).1 (e q).2 * φ (G (e q).1 (e q).2) g)
      (fun p => β p.1 * b p.1 p.2 * φ (G p.1 p.2) g) (fun _ => rfl), Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hG k g, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  refine ⟨⟨_, _, _, hflat⟩, fun N a F ha g => ?_⟩
  have hw := conj_wd h0 ha hflat g
  rw [Fintype.sum_equiv e (fun q => τ (β (e q).1 * b (e q).1 (e q).2) * φ (G (e q).1 (e q).2) g)
      (fun p => τ (β p.1 * b p.1 p.2) * φ (G p.1 p.2) g) (fun _ => rfl), Fintype.sum_sigma] at hw
  have hc : ∀ k, Φs' k g = ∑ j, τ (b k j) * φ (G k j) g := fun k => by
    rw [(h k).2 _ _ _ (hG k) g]
    simp only [one_mul]
  show c * ∑ k, τ (β k) * Φs' k g = ∑ k, c * τ (a k) * φ (F k) g
  simp only [hc, map_mul] at hw ⊢
  have e3 : ∑ k, c * τ (a k) * φ (F k) g = c * ∑ k, τ (a k) * φ (F k) g := by
    rw [Finset.mul_sum]; simp only [mul_assoc]
  rw [e3, hw]
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring

end GlobalTheory.ConjCombine

namespace GlobalTheory.ConjClassSum

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m}

theorem conjFun_iff {Tp : Type} {tup : Tp → T0} (O : OMDat T.toCore R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1))
    (τ : ℂ ≃+* ℂ) (ζ : ℂ) (Φ Φ' : GA D (Wc D i) → ℂ) :
    ConjFun O κ τ ζ Φ Φ' ↔ GlobalTheory.ConjCombine.CF (fun (F : T.toCore.cuspA ((i : ℕ) + 1) (wtA κ) κ.n) g =>
      (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * O.phi (T.cE ((i : ℕ) + 1) O.s0) (F : T.toCore.R ((i : ℕ) + 1)) g)
      τ ζ Φ Φ' := Iff.rfl

theorem conjFun_congr {Tp Tp' : Type} {tup : Tp → T0} {tup' : Tp' → T0} (O : OMDat T.toCore R i Tp tup)
    (O' : OMDat T.toCore R i Tp' tup') (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (τ : ℂ ≃+* ℂ) (ζ : ℂ) (Φ Φ' : GA D (Wc D i) → ℂ) :
    ConjFun O κ τ ζ Φ Φ' ↔ ConjFun O' κ τ ζ Φ Φ' := by
  unfold ConjFun Expands
  rw [GlobalTheory.OneMapAll.phi_eq O O' (T.cE ((i : ℕ) + 1))]

def psi {Tp : Type} {tup : Tp → T0} (M : OMDat T.toCore R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (z : G)
    (f : Rul (T.Q.Xo ((i : ℕ) + 1)) M.c') (g : GA D (Wc D i)) : ℂ :=
  T.cE ((i : ℕ) + 1) M.s0 (M.dict g).1 * (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * M.mu g *
    rdU (unfBC M.hle (T.U ((i : ℕ) + 1)) (inC M.c')) (actLev M.c' M.lev2 z f) (M.dict g).1 (M.dict g).2

theorem psi_smul {Tp : Type} {tup : Tp → T0} (M : OMDat T.toCore R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (z : G)
    (u : M.c'.F) (f : Rul (T.Q.Xo ((i : ℕ) + 1)) M.c') (g : GA D (Wc D i)) :
    psi M κ z (u • f) g = (u : ℂ) * psi M κ z f g := by
  unfold psi
  rw [map_smul, map_smulₛₗ]
  show _ * ((u : ℂ) * _) = _
  ring

set_option maxHeartbeats 8000000 in

theorem conj_lifts : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → Finite T0 → Nonempty (FWTie T R κ v₀) → IoExt R → QGuard R → ∀ i : Fin D.R.m, OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC (O i).c') (O i).c0' c → ∀ τ : ℂ ≃+* ℂ, FixBase T R i τ → ∃ ζ0 : ℂ, IsRoot1 ζ0 ∧ ∀ t t' : T0, ConjTup R τ t t' → ∃ s : (AE D)ˣ, ∀ (y : (R.HV i t).H) (y' : (R.HV i t').H), ConjForm R i τ c t t' y y' → ConjFun (O i) (κ i) τ (ζ0 * ((R.xi t' s : Circle) : ℂ)) (fun g => ph i * R.thF i t y (v₀ i (sg0 D A)) g) (fun g => ph i * R.thF i t' y' (v₀ i (sg0 D A)) g) := by
  intro hCI D G _ _ Pl0 T0 A T _ R F κ v₀ O ph hsz hC hT0 hFW hio hQ i hOP hPT c hc τ hτ
  obtain ⟨fw⟩ := hFW
  have hTie : TieIn T R κ v₀ := ⟨fw.laws, fw.alg_eq, fw.kap, fw.hv₀, fw.chiR, fw.x0⟩
  obtain ⟨M, hMP, hlev, hext, hnorm, hcurve, hxiF, hcov⟩ :=
    GlobalTheory.T.exists_normalisedData_normalCoefficientField D G Pl0 T0 A T R F κ v₀ O hC hT0 ⟨fw⟩ hQ i hOP

  let τQ : ℂ ≃ₐ[ℚ] ℂ := AlgEquiv.ofRingEquiv (f := τ) (fun q => map_ratCast τ q)
  let ta : M.c'.F ≃+* M.c'.F := (τQ.restrictNormal M.c'.F).toRingEquiv
  have hta : ∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ) := fun a => τQ.restrictNormal_commutes M.c'.F a

  have hEq0 : (O i).EquivAt (κ i) (T.cE ((i : ℕ) + 1) (O i).s0) :=
    (hPT (GlobalTheory.T.thetaOneMap_baseTuple_of_characterisation_extremal hCI D G Pl0 T0 A T R F κ v₀ hC hTie hio O i hOP)).1
  have hlev2 : M.lev2 = (O i).lev2 := by funext g; simp only [OMDat.lev2, hlev]
  have hEqM : M.EquivAt (κ i) (T.cE ((i : ℕ) + 1) M.s0) := by
    unfold OMDat.EquivAt at hEq0 ⊢
    rw [GlobalTheory.OneMapAll.phi_eq M (O i) (T.cE ((i : ℕ) + 1)), hlev2]
    exact hEq0
  have hcM : ExtC R i (inC M.c') M.c0' c := (hext c).1 hc

  obtain ⟨ζ, z, hζ, -, hser⟩ := GlobalTheory.T.oneMap_every_normalisedFamily_at_coreConstants hCI D G Pl0 T0 A T R F κ v₀ O ph hsz hC hT0 ⟨fw⟩ hio hQ i hOP hPT T0 id M hMP
    hlev hext
  obtain ⟨hf, k0, hk0, hgal⟩ := GlobalTheory.T.conj_thetaClassSum_eq_rootOfUnity_conjTuple hCI D G Pl0 T0 A T R F κ v₀ hC ⟨fw⟩ i T0 id M hMP τ ta hta hτ hcurve hxiF
  obtain ⟨a0, ha0, hza⟩ := hζ
  obtain ⟨b0, hb0, hkb⟩ := hk0
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow ha0.ne'] at hza
    exact zero_ne_one hza
  have hτζ : τ ζ ≠ 0 := (map_ne_zero τ).2 hζ0
  refine ⟨ζ * k0 / τ ζ, ⟨a0 * b0, Nat.mul_pos ha0 hb0, ?_⟩, fun t t' hct => ?_⟩
  · rw [div_pow, mul_pow, ← map_pow, pow_mul ζ a0 b0, hza, one_pow, pow_mul' k0 a0 b0, hkb, one_pow, map_one, div_one,
      one_mul]
  obtain ⟨e, hsame⟩ := hcov t t' hct.1
  obtain ⟨u, s, hu, hgal'⟩ := hgal t t' e hsame hct
  refine ⟨s, fun y y' hcf => ?_⟩
  obtain ⟨n, α, ys, ys', hy, hy', hval⟩ :=
    GlobalTheory.T.conjugate_definiteForms_descend_numberField D G Pl0 T0 A T R F κ v₀ hC ⟨fw⟩ i T0 id M hMP τ ta hta hτ c hcM hxiF t t' hct y y' hcf
  obtain ⟨h, J', hR, -⟩ := (hMP.tuple t).reps
  have hlevJ := ((GlobalTheory.T.conjugate_tuples_conjugate_residue_levels D G Pl0 T0 A T R F κ v₀ hC τ t t' hct).2.2.2 i hτ).1
  have hR' : RepsR R i t' (fun j => h (e.symm j)) (M.bad t') J' (M.Lh t') (M.gam t') (M.vol t') := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hR
    obtain ⟨-, -, -, hbad, hvol, hk⟩ := hsame
    have hQ' : R.Q t' = R.Q t := hct.1
    refine ⟨hbad ▸ h1, fun PP hPP => ?_, ?_, ?_, ?_, fun g => ?_, fun j => ?_⟩
    · rw [hbad]; exact h2 PP (hQ' ▸ hPP)
    · rw [hlevJ]; exact h3
    · rw [hlevJ]; exact h4
    · rw [hlevJ, hvol]; exact h5
    · obtain ⟨p, hp, huniq⟩ := h6 g
      refine ⟨e p, by simpa using hp, fun j hj => ?_⟩
      have := huniq (e.symm j) hj
      rw [← this]
      simp
    · obtain ⟨a1, a2, a3⟩ := h7 (e.symm j)
      have hkj := hk (e.symm j)
      simp only [Equiv.apply_symm_apply] at hkj
      exact ⟨hbad ▸ a1, hkj.1.trans a2, hkj.2.2.2.trans a3⟩

  choose xv xv' hxv using hval
  let xs : Fin n → M.Cl' t → VsV D i M.c'.F := fun k p => xv k (h p)
  let xs' : Fin n → M.Cl' t' → VsV D i M.c'.F := fun k j => xv' k (h (e.symm j))
  choose f hfc hfs using fun k => GlobalTheory.ClassSumRule.exists_cusp_isThClsD_core hCI D G Pl0 T0 A T R F κ v₀ hC hTie i T0 id M
    hMP t (xs k)
  have hsec : ∀ k, f k ∈ sec (T.Q.Xo ((i : ℕ) + 1)) M.c' (wtA (κ i)) (Vc D i).rank := fun k =>
    cusp_le_sec _ _ _ _ _ (hfc k)
  have hA : ∀ k g, ph i * R.thF i t (ys k) (v₀ i (sg0 D A)) g = ζ * psi M (κ i) z (f k) g := fun k g => by
    refine (hser t h J' hR (ys k) (xs k) (fun p => (hxv k (h p)).2.1) (f k) (hsec k) (hfs k) g).trans ?_
    unfold psi
    ring
  have hG : ∀ k, u • galRul hf (f k) ∈ sec (T.Q.Xo ((i : ℕ) + 1)) M.c' (wtA (κ i)) (Vc D i).rank ∧
      GlobalTheory.OneMapAll.IsSum M t' (xs' k) (u • galRul hf (f k)) := fun k =>
    hgal' (xs k) (xs' k) (fun p => by simp only [xs, xs', Equiv.symm_apply_apply]; exact (hxv k (h p)).1) (f k) (hsec k)
      (hfs k)
  have hB : ∀ k g, ph i * R.thF i t' (ys' k) (v₀ i (sg0 D A)) g = ζ * (u : ℂ) * psi M (κ i) z (galRul hf (f k)) g :=
    fun k g => by
    refine (hser t' (fun j => h (e.symm j)) J' hR' (ys' k) (xs' k) (fun j => (hxv k (h (e.symm j))).2.2)
      (u • galRul hf (f k)) (hG k).1 (hG k).2 g).trans ?_
    rw [show ζ * (u : ℂ) * psi M (κ i) z (galRul hf (f k)) g = ζ * ((u : ℂ) * psi M (κ i) z (galRul hf (f k)) g) by ring,
      ← psi_smul]
    unfold psi
    ring
  have hbc : ∀ k, ConjFun M (κ i) τ 1 (psi M (κ i) z (f k)) (psi M (κ i) z (galRul hf (f k))) := fun k =>
    GlobalTheory.T.cuspFormReading_galoisConj_expansion D G Pl0 T0 A T R F κ v₀ hC ⟨fw⟩ i T0 id M hMP τ ta hta hτ hf z (f k) (hfc k) hEqM
  have hbc0 : ConjFun M (κ i) τ 1 (psi M (κ i) z 0) (psi M (κ i) z (galRul hf 0)) :=
    GlobalTheory.T.cuspFormReading_galoisConj_expansion D G Pl0 T0 A T R F κ v₀ hC ⟨fw⟩ i T0 id M hMP τ ta hta hτ hf z 0 (Submodule.zero_mem _) hEqM
  have hcomb := GlobalTheory.ConjCombine.conj_comb ((conjFun_iff M (κ i) τ 1 _ _).1 hbc0) (fun k => ζ * α k)
    (fun k => psi M (κ i) z (f k)) (fun k => psi M (κ i) z (galRul hf (f k)))
    (fun k => (conjFun_iff M (κ i) τ 1 _ _).1 (hbc k)) (ζ * k0 / τ ζ * ((R.xi t' s : Circle) : ℂ))
  have hΦ : (fun g => ph i * R.thF i t y (v₀ i (sg0 D A)) g) =
      fun g => ∑ k, (ζ * α k) * psi M (κ i) z (f k) g := by
    funext g
    rw [hy, map_sum]
    simp only [map_smul, MultilinearMap.sum_apply, MultilinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_left_comm, hA k g]
    ring
  have hΦ' : (fun g => ph i * R.thF i t' y' (v₀ i (sg0 D A)) g) =
      fun g => ζ * k0 / τ ζ * ((R.xi t' s : Circle) : ℂ) * ∑ k, τ (ζ * α k) * psi M (κ i) z (galRul hf (f k)) g := by
    funext g
    rw [hy', map_sum]
    simp only [map_smul, MultilinearMap.sum_apply, MultilinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hu' : (u : ℂ) = k0 * ((R.xi t' s : Circle) : ℂ) := hu
    have hcan : ζ * k0 / τ ζ * τ ζ = ζ * k0 := div_mul_cancel₀ _ hτζ
    rw [mul_left_comm, hB k g, hu', map_mul]
    linear_combination (-(τ (α k) * ((R.xi t' s : Circle) : ℂ) * psi M (κ i) z (galRul hf (f k)) g)) * hcan
  rw [conjFun_congr (O i) M, conjFun_iff, hΦ, hΦ']
  exact hcomb

end GlobalTheory.ConjClassSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitScalarSmulCoreIntegralAdelicFormPlaces
section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ScaleInt

theorem exists_prime_mem {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) :
    ∃ p : ℕ, p.Prime ∧ ((p : ℕ) : 𝓞 K) ∈ la.asIdeal := by
  have : Finite (𝓞 K ⧸ la.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot la.asIdeal la.ne_bot
  have : la.asIdeal.IsMaximal := la.isMaximal
  let _ : Field (𝓞 K ⧸ la.asIdeal) := Ideal.Quotient.field _
  refine ⟨ringChar (𝓞 K ⧸ la.asIdeal), CharP.char_is_prime (𝓞 K ⧸ la.asIdeal) _, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.Nat.cast_ringChar

theorem exists_avoid {K : Type} [Field K] [NumberField K] (q : Ideal (𝓞 K)) (hq : q.IsPrime)
    (s : Finset (HeightOneSpectrum (𝓞 K))) (hs : ∀ p ∈ s, p.asIdeal ≠ q) (N : HeightOneSpectrum (𝓞 K) → ℕ) :
    ∃ t : 𝓞 K, t ∉ q ∧ ∀ p ∈ s, t ∈ p.asIdeal ^ N p := by
  have hle : ¬ (s.prod fun p => p.asIdeal ^ N p) ≤ q := by
    rw [hq.prod_le]
    rintro ⟨p, hp, hpq⟩
    rcases Nat.eq_zero_or_pos (N p) with h0 | hpos
    · rw [h0, pow_zero, Ideal.one_eq_top, top_le_iff] at hpq
      exact hq.ne_top hpq
    · have h1 : p.asIdeal ≤ q := hq.le_of_pow_le hpq
      exact hs p hp (p.isMaximal.eq_of_le hq.ne_top h1)
  obtain ⟨t, ht, htq⟩ := SetLike.not_le_iff_exists.1 hle
  exact ⟨t, htq, fun p hp => (Ideal.prod_le_inf.trans (Finset.inf_le hp)) ht⟩

theorem le_vLa_of_mem {K : Type} [Field K] [NumberField K] (p : HeightOneSpectrum (𝓞 K)) {t : 𝓞 K} (n : ℕ)
    (ht : t ∈ p.asIdeal ^ n) (ht0 : t ≠ 0) : (n : ℤ) ≤ vLa p (t : K) := by
  have h := (p.intValuation_le_pow_iff_mem t n).2 ht
  have hne : p.intValuation t ≠ 0 := HeightOneSpectrum.intValuation_ne_zero p t ht0
  have e : p.valuation K (t : K) = p.intValuation t := p.valuation_of_algebraMap t
  unfold vLa
  rw [e]
  have := (WithZero.log_le_log hne (by simp)).2 h
  simp at this
  omega

theorem vLa_eq_zero_of_not_mem {K : Type} [Field K] [NumberField K] (p : HeightOneSpectrum (𝓞 K)) {t : 𝓞 K}
    (ht : t ∉ p.asIdeal) : vLa p (t : K) = 0 := by
  unfold vLa
  rw [(HeightOneSpectrum.valuation_eq_one_iff_notMem p).mpr ht, WithZero.log_one, neg_zero]

end GlobalTheory.ScaleInt

namespace GlobalTheory.ScaleInt

set_option maxHeartbeats 800000 in

theorem smul_mem_baseInt : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ (i : Fin D.R.m) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)), κ.LastPos →
    ∀ (q : Ideal (𝓞 T.Q.c.F)), q.IsPrime → ∀ (P : Set (HeightOneSpectrum (𝓞 T.Q.c.F))), P.Finite →
    ∀ ψ ∈ baseInt T ((i : ℕ) + 1) T.σ₀ (wtA κ) κ.n {p | p.asIdeal = q},
      ∃ t : 𝓞 T.Q.c.F, t ∉ q ∧ T.σ₀ (t : T.Q.c.F) • ψ ∈ baseInt T ((i : ℕ) + 1) T.σ₀ (wtA κ) κ.n P := by
  intro D T hT i κ hκ q hq P hP ψ hψ
  obtain ⟨f, ⟨hfs, hfh, hfv⟩, rfl⟩ := hψ
  have hj : InR D ((i : ℕ) + 1) := inR i
  have hcusp : f ∈ cusp (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.U ((i : ℕ) + 1)) (wtA κ) κ.n := GlobalTheory.T.mem_cuspForms_allEmbeddings_of_inclusion_reading D T hT _ hj κ hκ f hfs hfh
  have hbd : ∀ p : HeightOneSpectrum (𝓞 T.Q.c.F), ∃ κ' : T.Q.c.F, κ' ≠ 0 ∧
      GlobalTheory.GoodPts.BddAll (T.Q.Xo ((i : ℕ) + 1)) T.Q.c p κ' f := by
    intro p
    obtain ⟨pr, hpr, hmem⟩ := exists_prime_mem p
    exact GlobalTheory.CuspBound.exists_bddAll_cusp _ _ _ _ _ _ _ (T.U ((i : ℕ) + 1)) (hT.unf _ hj) p pr hpr hmem
      (goodAt_of_two_primes hT.pins.2.1.1 (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne pr hpr) _ _ f
      (dom_wtA κ) hcusp
  choose κ' hκ0 hκb using hbd
  obtain ⟨t, htq, htm⟩ := exists_avoid q hq (hP.toFinset.filter fun p => p.asIdeal ≠ q)
    (fun p hp => (Finset.mem_filter.1 hp).2) (fun p => (vLa p (κ' p)).toNat)
  have ht0 : t ≠ 0 := fun h => htq (h ▸ q.zero_mem)
  have htK : (t : T.Q.c.F) ≠ 0 := by exact_mod_cast ht0
  refine ⟨t, htq, (t : T.Q.c.F) • f, ⟨(sec _ _ _ _).smul_mem _ hfs, ?_, ?_⟩, ?_⟩
  · rw [map_smulₛₗ]
    exact Submodule.smul_mem _ _ hfh
  · intro la hla v hv
    have hV := isVal_valSet la v hv
    rw [hV.smul _ _ htK]
    by_cases hlq : la.asIdeal = q
    · have h0 : vAdd la (t : T.Q.c.F) = 0 := vLa_eq_zero_of_not_mem la (hlq ▸ htq)
      rw [h0]
      simpa using hfv la hlq v hv
    · have hmem : la ∈ hP.toFinset.filter fun p => p.asIdeal ≠ q :=
        Finset.mem_filter.2 ⟨hP.mem_toFinset.2 hla, hlq⟩
      have hge : (vLa la (κ' la) : ℤ) ≤ vAdd la (t : T.Q.c.F) :=
        (Int.self_le_toNat _).trans (le_vLa_of_mem la _ (htm la hmem) ht0)
      obtain ⟨y, rfl⟩ := hv
      have hb := (GlobalTheory.GoodPtsModel.bddAll_iff_vAtV (hκ0 la) f).1 (hκb la) y
      exact hb.trans (add_le_add (by exact_mod_cast hge) le_rfl)
  · simp only [CoreJ.phiJ, map_smulₛₗ, LinearMap.map_smul, smul_comm ((lieFac _ _ _ : ℝ) : ℂ)]
    rfl

end GlobalTheory.ScaleInt
end
end

