import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0580
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCycleRationalExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0581
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0544
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0593
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0016
import Formalism.RealPlaceAnalysis.Bundle0004
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0011
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AutomorphicSpectrum.PublishedTheorems.PublishedGlobalResults.HasInfCharOfIsRegAlg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0602
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0600
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0226
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0529
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0053
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0032
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0411
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarFibreUniqueness.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0596
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.UnramifiedSchwartzDensity.SchCut
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0597
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0519
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0531
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0567
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0599
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOfComps
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.AdeleComp

open TensorProduct

theorem coord_zero {F A B E ι : Type*} [Field F] [AddCommGroup E] [Module F E]
    [AddCommGroup A] [Module F A] [AddCommGroup B] [Module F B]
    (ℬ : Module.Basis ι F E) (f : A →ₗ[F] B) (c : ι →₀ A)
    (h : LinearMap.rTensor E f (c.sum fun i m => m ⊗ₜ[F] ℬ i) = 0) (i : ι) : f (c i) = 0 := by
  have h1 : (c.mapRange f (map_zero f)).sum (fun i m => m ⊗ₜ[F] ℬ i) = 0 := by
    rw [Finsupp.sum_mapRange_index (by intro i; simp)]
    rw [← h, Finsupp.sum, Finsupp.sum, map_sum]
    simp
  have h2 := TensorProduct.sum_tmul_basis_right_eq_zero ℬ _ h1
  simpa using DFunLike.congr_fun h2 i

theorem adele_eq_zero {F : Type} [Field F] [NumberField F] (x : AF F)
    (hi : ∀ w, evInf F w x = 0) (hf : ∀ v, evFin F v x = 0) : x = 0 := by
  refine Prod.ext (funext fun w => hi w) ?_
  exact RestrictedProduct.ext _ _ fun v => hf v

theorem tensor_eq_zero {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (a : AF F ⊗[F] E) (hi : ∀ w, compInf F E w a = 0) (hf : ∀ v, compFin F E v a = 0) : a = 0 := by
  let ℬ := Module.Basis.ofVectorSpace F E
  obtain ⟨c, rfl⟩ := TensorProduct.eq_repr_basis_right ℬ a
  have hc : c = 0 := by
    ext i
    refine adele_eq_zero _ (fun w => ?_) (fun v => ?_)
    · refine coord_zero ℬ (evInf F w).toLinearMap c ?_ i
      rw [← hi w]
      simp only [compInf, Finsupp.sum, map_sum]
      rfl
    · refine coord_zero ℬ (evFin F v).toLinearMap c ?_ i
      rw [← hf v]
      simp only [compFin, Finsupp.sum, map_sum]
      rfl
  simp [hc]

theorem eq_zero_of_comps (D : D7) (a : AE D) (hi : ∀ w, compInf D.host.F D.host.E w a = 0)
    (hf : ∀ v, cv D v a = 0) : a = 0 :=
  tensor_eq_zero a hi hf

end GlobalTheory.CompanionTheory.AdeleComp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvFinSSOneNot
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.SPartTensor

section Generic

variable {F E A R : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [Algebra F A] [CommRing R] [Algebra F R]

def tP (p : A →ₐ[F] R) : A ⊗[F] E →+* R ⊗[F] E := (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom

def tQ (s : R →ₗ[F] A) : R ⊗[F] E →+ A ⊗[F] E := (LinearMap.rTensor E s).toAddMonoidHom

@[simp] theorem rTensor_tmul₂ (p : A →ₐ[F] R) (a : A) (x : E) : tP p (a ⊗ₜ[F] x) = p a ⊗ₜ[F] x := rfl

@[simp] theorem tQ_tmul (s : R →ₗ[F] A) (r : R) (x : E) : tQ s (r ⊗ₜ[F] x) = s r ⊗ₜ[F] x := rfl

theorem rTensor_includeRight (p : A →ₐ[F] R) (x : E) : tP p (inclR (F := F) A x) = inclR (F := F) R x := by
  change tP p ((1 : A) ⊗ₜ[F] x) = (1 : R) ⊗ₜ[F] x
  rw [rTensor_tmul₂, map_one]

theorem rTensor_lTensor_comm₂ (p : A →ₐ[F] R) (σ : E →ₐ[F] E) (x : A ⊗[F] E) :
    tP p (sigR A σ x) = sigR R σ (tP p x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a y => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem tQ_sigR (s : R →ₗ[F] A) (σ : E →ₐ[F] E) (y : R ⊗[F] E) :
    tQ s (sigR R σ y) = sigR A σ (tQ s y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a y => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem rTensor_rTensor_of_rightInverse (p : A →ₐ[F] R) (s : R →ₗ[F] A) (h : ∀ r, p (s r) = r) (y : R ⊗[F] E) :
    tP p (tQ s y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a y => rw [tQ_tmul, rTensor_tmul₂, h]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem tQ_tP (p : A →ₐ[F] R) (s : R →ₗ[F] A) (b : A) (h : ∀ a, s (p a) = b * a) (x : A ⊗[F] E) :
    tQ s (tP p x) = (b ⊗ₜ[F] (1 : E)) * x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a y => rw [rTensor_tmul₂, tQ_tmul, h, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | add x y hx hy => simp only [map_add, hx, hy, mul_add]

theorem tQ_mul (s : R →ₗ[F] A) (h : ∀ r r', s (r * r') = s r * s r') (y y' : R ⊗[F] E) :
    tQ s (y * y') = tQ s y * tQ s y' := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, add_mul]
  | tmul a z =>
    induction y' using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy, mul_add]
    | tmul b w =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, tQ_tmul, tQ_tmul, tQ_tmul, h,
        Algebra.TensorProduct.tmul_mul_tmul]

end Generic

section Adelic

variable {F : Type} [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))

abbrev RS : Type := Ainf F × (∀ v : S, Fv F v.1)

def finOf (c : ∀ v : S, Fv F v.1) : Af F := ∑ v : S, singleFin v.1 (c v)

variable {S}

theorem evalV_finOf (c : ∀ v : S, Fv F v.1) (u : HeightOneSpectrum (𝓞 F)) (h : u ∈ S) :
    evalV F u (finOf S c) = c ⟨u, h⟩ := by
  unfold finOf
  rw [map_sum, Finset.sum_eq_single (⟨u, h⟩ : S)
    (fun b _ hb => evalV_singleFin_ne (fun e => hb (Subtype.ext e.symm)) _) (by simp)]
  exact evalV_singleFin_self u _

theorem evalV_finOf_not (c : ∀ v : S, Fv F v.1) (u : HeightOneSpectrum (𝓞 F)) (h : u ∉ S) :
    evalV F u (finOf S c) = 0 := by
  unfold finOf
  rw [map_sum]
  exact Finset.sum_eq_zero fun b _ => evalV_singleFin_ne (fun e => h (by rw [e]; exact b.2)) _

theorem af_ext {x y : Af F} (h : ∀ u, evalV F u x = evalV F u y) : x = y :=
  by first | exact RestrictedProduct.ext _ _ h | exact Subtype.ext (funext h)

variable (S)

def pS : AF F →ₐ[F] RS S :=
  (fstA F).prod (Pi.algHom F _ fun v : S => (evalV F v.1).comp (sndA F))

def sS : RS S →ₗ[F] AF F where
  toFun r := (r.1, finOf S r.2)
  map_add' r r' := by
    refine Prod.ext rfl ?_
    change finOf S (r.2 + r'.2) = finOf S r.2 + finOf S r'.2
    simp [finOf, Finset.sum_add_distrib]
  map_smul' a r := by
    refine Prod.ext rfl ?_
    change finOf S (a • r.2) = a • finOf S r.2
    simp [finOf, Finset.smul_sum]

variable {S}

theorem pS_sS (r : RS S) : pS S (sS S r) = r := by
  refine Prod.ext rfl (funext fun v => ?_)
  exact evalV_finOf r.2 v.1 v.2

theorem sS_mul (r r' : RS S) : sS S (r * r') = sS S r * sS S r' := by
  refine Prod.ext rfl (af_ext fun u => ?_)
  change evalV F u (finOf S (r.2 * r'.2)) = evalV F u (finOf S r.2 * finOf S r'.2)
  rw [map_mul]
  by_cases h : u ∈ S
  · rw [evalV_finOf _ u h, evalV_finOf _ u h, evalV_finOf _ u h]; rfl
  · rw [evalV_finOf_not _ u h, evalV_finOf_not _ u h, zero_mul]

theorem sS_pS (a : AF F) : sS S (pS S a) = sS S 1 * a := by
  refine Prod.ext (one_mul _).symm (af_ext fun u => ?_)
  change evalV F u (finOf S fun v : S => evalV F v.1 a.2) = evalV F u (finOf S 1 * a.2)
  rw [map_mul]
  by_cases h : u ∈ S
  · rw [evalV_finOf _ u h, evalV_finOf _ u h]; simp
  · rw [evalV_finOf_not _ u h, evalV_finOf_not _ u h, zero_mul]

theorem evInf_sS_one (w : InfinitePlace F) : evInf F w (sS S 1) = 1 := by
  change (GlobalTheory.AutFunCompare.evW w) (1 : Ainf F) = 1
  exact map_one _

theorem evFin_sS_one_mem {v : HeightOneSpectrum (𝓞 F)} (h : v ∈ S) : evFin F v (sS S 1) = 1 :=
  evalV_finOf _ v h

theorem evFin_sS_one_not {v : HeightOneSpectrum (𝓞 F)} (h : v ∉ S) : evFin F v (sS S 1) = 0 :=
  evalV_finOf_not _ v h

end Adelic

theorem sPartOf {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (e : AF F ⊗[F] E)
    (hinj : ∀ a : AF F ⊗[F] E, (∀ w, compInf F E w a = 0) → (∀ v, compFin F E v a = 0) → a = 0)
    (h1 : ∀ w, compInf F E w e = 1) (h2 : ∀ v ∈ S, compFin F E v e = 1) (h3 : ∀ v, v ∉ S → compFin F E v e = 0) :
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra F R) (_ : IsArtinianRing R) (_ : IsReduced R)
      (P : AF F ⊗[F] E →+* R ⊗[F] E) (Q : R ⊗[F] E →+ AF F ⊗[F] E),
      (∀ x, P (inclR (F := F) (AF F) x) = inclR R x) ∧ (∀ x, P (sigR (AF F) σ x) = sigR R σ (P x)) ∧
      (∀ y, Q (sigR R σ y) = sigR (AF F) σ (Q y)) ∧ (∀ y, P (Q y) = y) ∧ (∀ x, Q (P x) = e * x) ∧
      ∀ y y', Q (y * y') = Q y * Q y' := by
  have hE : e = (sS S 1 : AF F) ⊗ₜ[F] (1 : E) := by
    rw [← sub_eq_zero]
    refine hinj _ (fun w => ?_) (fun v => ?_)
    · rw [RingHom.map_sub, h1 w, sub_eq_zero]
      change (1 : _) = evInf F w (sS S 1) ⊗ₜ[F] (1 : E)
      rw [evInf_sS_one]; rfl
    · rw [RingHom.map_sub, sub_eq_zero]
      change _ = evFin F v (sS S 1) ⊗ₜ[F] (1 : E)
      by_cases h : v ∈ S
      · rw [h2 v h, evFin_sS_one_mem h]; rfl
      · rw [h3 v h, evFin_sS_one_not h, TensorProduct.zero_tmul]
  haveI : IsArtinianRing (Ainf F) := inferInstanceAs (IsArtinianRing (∀ v : InfinitePlace F, v.Completion))
  haveI : IsReduced (Ainf F) := inferInstanceAs (IsReduced (∀ v : InfinitePlace F, v.Completion))
  refine ⟨RS S, inferInstance, inferInstance, inferInstance, inferInstance, tP (pS S), tQ (sS S),
    rTensor_includeRight _, rTensor_lTensor_comm₂ _ _, tQ_sigR _ _, rTensor_rTensor_of_rightInverse _ _ pS_sS, fun x => ?_, tQ_mul _ sS_mul⟩
  rw [hE]
  exact tQ_tP _ _ _ sS_pS x

theorem sPart : (∀ (D : D7) (a : AE D), (∀ w, compInf D.host.F D.host.E w a = 0) → (∀ v, cv D v a = 0) → a = 0) →
    ∀ (D : D7) (S : Finset (Pl D)) (e : AE D), IsIdem S e →
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra D.host.F R) (_ : IsArtinianRing R) (_ : IsReduced R)
      (P : AE D →+* R ⊗[D.host.F] D.host.E) (Q : R ⊗[D.host.F] D.host.E →+ AE D),
      (∀ x, P (incA D x) = inclR R x) ∧ (∀ x, P (cA D x) = sigR R D.sp.cm.sig (P x)) ∧
      (∀ y, Q (sigR R D.sp.cm.sig y) = cA D (Q y)) ∧ (∀ y, P (Q y) = y) ∧ (∀ x, Q (P x) = e * x) ∧
      ∀ y y', Q (y * y') = Q y * Q y' := by
  intro hinj D S e he
  exact sPartOf D.sp.cm.sig S e (hinj D) he.1 (fun v h => (he.2 v).trans (if_pos h))
    (fun v h => (he.2 v).trans (if_neg h))

end GlobalTheory.CompanionTheory.SPartTensor
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFormNonvanishingOnChart
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)

namespace GlobalTheory.CompanionTheory.MixZ.ArchEq

theorem exists_form_of_mem_open : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i]
    (U : X.Opens), genericPoint X ∈ U → ∃ (j : Pol n) (a : Fin (m + 1) → ℕ), IsMultiHomog j a ∧
      j ∉ ptIdeal (i (genericPoint X)) ∧ ∀ (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (z : (Σ k, Bk n k) → ℂ),
        GlobalTheory.CompanionTheory.MixZ.ArchEq.Over i y z → eval z (map (Int.castRingHom ℂ) j) ≠ 0 → y ∈ ptsIn (i ≫ mpStr ℤ m n) σ₀ U := by
  intro m n X _ i _ U hU
  classical
  have hx : i (genericPoint X) ∈ mchart (ptChart (i (genericPoint X))) :=
    Set.mem_iInter.2 fun k => mem_ptChart _ k
  have hcl : IsClosed (i '' (U : Set X)ᶜ) :=
    i.isClosedEmbedding.isClosedMap _ U.isOpen.isClosed_compl
  let V : (MP ℤ m n).Opens := ⟨(i '' (U : Set X)ᶜ)ᶜ, hcl.isOpen_compl⟩
  have hV : i (genericPoint X) ∈ V := by
    rintro ⟨x, hxU, hxe⟩
    exact hxU (i.isClosedEmbedding.injective hxe ▸ hU)
  obtain ⟨g, hgV, hgx⟩ := (SmoothRep.gen m n (ptChart (i (genericPoint X)))).1.exists_basicOpen_le ⟨_, hV⟩ hx
  obtain ⟨F0, rfl⟩ := ExRat.dehomog_surjective _ g
  obtain ⟨a, F, hF, e⟩ := ExRat.exists_homog (ptChart (i (genericPoint X))) F0
  rw [← e] at hgV hgx
  have hm := homog_mul hF (ExRat.isMultiHomog_mono (ptChart (i (genericPoint X))) 1)
  refine ⟨F * ExRat.mono (ptChart (i (genericPoint X))) 1, _, hm, ?_, ?_⟩
  · rw [mem_ptIdeal_iff_aeval_ptCoord m n _ _ _ hm, FnForm.aeval_ptCoord_eq_mul _ _ hx hm]
    simp only [ptCoord_ptChart, one_pow, Finset.prod_const_one, one_mul, map_mul, ExRat.dehomog_mono, mul_one]
    exact (Scheme.evaluation_ne_zero_iff_mem_basicOpen _ _ hx _).2 hgx
  · intro y z hyz hne
    have hz : ∀ k, z ⟨k, ptChart (i (genericPoint X)) k⟩ ≠ 0 := by
      intro k h0
      apply hne
      have : eval z (map (Int.castRingHom ℂ) (ExRat.mono (ptChart (i (genericPoint X))) 1)) = 0 := by
        simp only [ExRat.mono, Pi.one_apply, pow_one, map_prod, map_X]
        exact Finset.prod_eq_zero (Finset.mem_univ k) ((eval_X _).trans h0)
      rw [map_mul, map_mul, this, mul_zero]
    have hF0 : eval z (map (Int.castRingHom ℂ) F) ≠ 0 := by
      intro h0
      apply hne
      rw [map_mul, map_mul, h0, zero_mul]
    have hw : PtsOver.map i rfl _ y ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart (ptChart (i (genericPoint X)))) :=
      mem_ptsIn.2 (Set.mem_iInter.2 fun k => mem_ptsIn.1 ((hyz k _).1.2 (hz k)))
    have hev : ev (mpStr ℤ m n) σ₀ _ (dehomog (ptChart (i (genericPoint X))) F) (PtsOver.map i rfl _ y) ≠ 0 := by
      rw [GlobalTheory.T.dehomogenized_eval_eq_ratio m n _ F a hF _ z hyz hw]
      exact div_ne_zero hF0 (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hz k))
    have hb := mem_ptsIn.1 ((mem_ptsIn_basicOpen hw _).2 hev)
    have hp := hgV hb
    rw [mem_ptsIn]
    by_contra h
    exact hp ⟨_, h, rfl⟩

end GlobalTheory.CompanionTheory.MixZ.ArchEq
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFrameLeftInvGram
section
open MeasureTheory Topology Filter GlobalTheory.CompanionTheory.NullFr
open scoped NNReal ENNReal Matrix
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.NullFr

theorem exists_frame_leftInv {A : Type} [CommRing A] {a r t : ℕ} (e : A) (x : Fx A a r) (v : Fx A a t)
    (P : Fx A r a) (M : Fx A t a) (hx : e • x = x) (hv : e • v = v) (hP : P * x = e • (1 : Fx A r r))
    (hM : M * (v - x * (P * v)) = e • (1 : Fx A t t)) :
    ∃ (L₁ : Fx A r a) (L₂ : Fx A t a), L₁ * x = e • (1 : Fx A r r) ∧ L₁ * v = 0 ∧ L₂ * x = 0 ∧
      L₂ * v = e • (1 : Fx A t t) := by
  have h2x : M * (1 - x * P) * x = 0 := by
    rw [Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hP, Matrix.mul_smul,
      Matrix.mul_one, hx, sub_self, Matrix.mul_zero]
  have h2v : M * (1 - x * P) * v = e • (1 : Fx A t t) := by
    rw [Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hM]
  have hPv : e • (P * v) = P * v := by
    rw [← Matrix.mul_smul, hv]
  refine ⟨P - (P * v) * (M * (1 - x * P)), M * (1 - x * P), ?_, ?_, h2x, h2v⟩
  · rw [Matrix.sub_mul, Matrix.mul_assoc, h2x, Matrix.mul_zero, sub_zero, hP]
  · rw [Matrix.sub_mul, Matrix.mul_assoc, h2v, Matrix.mul_smul, Matrix.mul_one, hPv, sub_self]

theorem exists_frame_leftInv_gram {A : Type} [CommRing A] {a r t : ℕ} (e : A) (x : Fx A a r) (v : Fx A a t)
    (B' B : Fx A r r) (C : Fx A r a) (H : Fx A a a) (M : Fx A t a) (hB : B' * B = 1)
    (hx : e • x = x) (hv : e • v = v) (hg : C * (H * x) = e • B)
    (hM : M * (v - x * (B' * (C * (H * v)))) = e • (1 : Fx A t t)) :
    ∃ (L₁ : Fx A r a) (L₂ : Fx A t a), L₁ * x = e • (1 : Fx A r r) ∧ L₁ * v = 0 ∧ L₂ * x = 0 ∧
      L₂ * v = e • (1 : Fx A t t) := by
  have hP : B' * (C * H) * x = e • (1 : Fx A r r) := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hg, Matrix.mul_smul, hB]
  have hM' : M * (v - x * (B' * (C * H) * v)) = e • (1 : Fx A t t) := by
    rw [Matrix.mul_assoc B', Matrix.mul_assoc C]
    exact hM
  exact exists_frame_leftInv e x v (B' * (C * H)) M hx hv hP hM'

theorem free_of_leftInv_orth {D : D7} {r t : ℕ} (V : HSp D) (b₀ : HermE D r) (hb : b₀.1.det ≠ 0) (e : AE D)
    (z : Mx D V.rank r × Mx D V.rank t) (hx : e • z.1 = z.1) (hv : e • z.2 = z.2)
    (hg : ip V z.1 z.1 = e • rat b₀.1)
    (M : Mx D t V.rank) (hM : mm M (z.2 - mm z.1 (yv V b₀ z)) = e • (1 : Mx D t t)) : Free e z := by
  have hB : rat b₀.1⁻¹ * rat b₀.1 = (1 : Mx D r r) := by
    have hu : IsUnit b₀.1.det := isUnit_iff_ne_zero.2 hb
    simp only [rat]
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu, Matrix.map_one _ (map_zero _) (map_one _)]
  exact exists_frame_leftInv_gram e z.1 z.2 (rat b₀.1⁻¹) (rat b₀.1) (adj z.1) (gA V) M hB hx hv hg hM

end GlobalTheory.CompanionTheory.NullFr
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInvariantHermitianForm
section
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

namespace GlobalTheory.CompanionTheory.ClozelHerm

def petersson {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (μ : Measure (GA E a))
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (π : CuspSub E a)
    (hm : ∀ φ ∈ π.V, GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ φ.1) :
    π.V →ₗ[ℂ] π.V →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun φ ψ => inner ℂ (toL2ₗ μ π.V hm ψ) (toL2ₗ μ π.V hm φ))
    (fun φ φ' ψ => by simp only [map_add, inner_add_right])
    (fun c φ ψ => by simp only [map_smul, inner_smul_right, smul_eq_mul, RingHom.id_apply])
    (fun φ ψ ψ' => by simp only [map_add, inner_add_left])
    (fun c φ ψ => by simp only [map_smul, inner_smul_left, smul_eq_mul])

theorem exists_isHerm : GlobalTheory.Published.CuspFormsBoundedGL → ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (π : CuspSub E a), GlobalTheory.DiscSpec.IsNormalised π → ∃ B : π.V →ₗ[ℂ] π.V →ₗ⋆[ℂ] ℂ, IsHerm π B := by
  intro hB E _ _ _ a μ _ _ π hπ
  have hl := GlobalTheory.T.normalised_cusp_form_L2_bounded hB E a μ π hπ
  have hm : ∀ φ ∈ π.V, GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ φ.1 := fun φ hφ => (hl φ hφ).1
  have hb : ∀ φ ∈ π.V, ∃ C : ℝ, ∀ g, ‖φ.1 g‖ ≤ C := fun φ hφ => (hl φ hφ).2
  refine ⟨petersson μ π hm, fun X φ ψ => GlobalTheory.T.lie_action_skew_adjoint_L2 E a μ π hm hb X φ ψ, ?_⟩
  obtain ⟨φ, hφ, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot π.ne_bot
  have hi : Function.Injective (toL2ₗ μ π.V hm) :=
    toL2ₗ_injective hm fun ψ hψ => ContAut.continuous_of_isOpen_stab E a ψ (π.cusp ψ hψ).1.level
  have hT : toL2ₗ μ π.V hm ⟨φ, hφ⟩ ≠ 0 := fun h =>
    hne (congrArg Subtype.val (hi (h.trans (map_zero _).symm)))
  refine ⟨⟨φ, hφ⟩, ?_⟩
  show inner ℂ (toL2ₗ μ π.V hm ⟨φ, hφ⟩) (toL2ₗ μ π.V hm ⟨φ, hφ⟩) ≠ 0
  exact inner_self_ne_zero.2 hT

end GlobalTheory.CompanionTheory.ClozelHerm

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRealCoords
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.SchwartzFib

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 2000 in

theorem exists_real_coords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n M : ℕ),
    ∃ (N : ℕ) (e : (Fin n → Fin M → Ainf F ⊗[F] E) ≃+ (Fin N → ℝ)), Continuous e ∧ Continuous e.symm := by
  intro F E _ _ _ _ _ n M
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let t := GlobalTheory.Core.Rk.RapidInt.tupEquiv F E (Module.finBasis F E) M n
  let L := (Module.finBasis ℝ (Fin n → Fin M → Fin (Module.finrank F E) → mixedEmbedding.mixedSpace F)).equivFun.toContinuousLinearEquiv
  refine ⟨_, t.toAddEquiv.trans L.toLinearEquiv.toAddEquiv, ?_, ?_⟩
  · exact L.continuous.comp t.continuous
  · exact t.symm.continuous.comp L.symm.continuous

end GlobalTheory.CompanionTheory.SW.SchwartzFib
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsTamagawaMeasureNormalization
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.WeilSiegel.Frame

theorem exists_coord_fibres : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ J → ∀ n : ℕ, ∃ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F)) (lam : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Measure (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v)) (minf : HeckeCharacterZeroLocus.SiegelWeilU.HermR (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F) σ n → Measure (Fin n → Fin M → HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E)) (m : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), HeckeCharacterZeroLocus.SiegelWeilU.HermR (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) σ n → Measure (Fin n → Fin M → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)), GlobalTheory.CompanionTheory.SW.IsStdInf laminf ∧ (∀ v, GlobalTheory.CompanionTheory.SW.IsStdV v (lam v)) ∧ IsGramFibFree (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F) σ J n (GlobalTheory.CompanionTheory.SW.coordW (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F) b laminf n M) (GlobalTheory.CompanionTheory.SW.coordHerm (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F) σ b laminf n) minf ∧ ∀ v, IsGramFibFree (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) σ J n (GlobalTheory.CompanionTheory.SW.coordW (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) b (lam v) n M) (GlobalTheory.CompanionTheory.SW.coordHerm (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) σ b (lam v) n) (m v) := by
  intro F E _ _ _ _ _ σ hCM M J hJ n
  have hfd : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  let b := Module.finBasis F E
  obtain ⟨laminf, hinf⟩ := GlobalTheory.CompanionTheory.SW.StdEx.exists_isStdInf F
  choose lam hlam using GlobalTheory.CompanionTheory.SW.StdEx.exists_isStdV F
  have hB : BorelSpace (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F) := ⟨rfl⟩
  obtain ⟨-, hWi, hHi⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hCM (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F) _ b laminf hinf.1
  obtain ⟨minf, hminf⟩ := GlobalTheory.T.exists_fibreMeasures_archimedeanGramMap F E σ hCM M n J hJ
    (GlobalTheory.CompanionTheory.SW.coordW (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F) b laminf n M)
    (GlobalTheory.CompanionTheory.SW.coordHerm (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F) σ b laminf n) (hWi n M) (hHi n)
  have hfV : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
      ∃ fib : HeckeCharacterZeroLocus.SiegelWeilU.HermR (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) σ n →
        Measure (Fin n → Fin M → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E),
      IsGramFibFree (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) σ J n (GlobalTheory.CompanionTheory.SW.coordW (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) b (lam v) n M)
        (GlobalTheory.CompanionTheory.SW.coordHerm (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) σ b (lam v) n) fib := fun v => by
    have := PI.VolStabS.secondCountable_Fv F v
    have := PI.VolStabS.locallyCompact_Fv F v
    have hBv : BorelSpace (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) := ⟨rfl⟩
    obtain ⟨-, hWv, hHv⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hCM (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) _ b (lam v) (hlam v).1
    exact PI.OmFibreUniq.W.gram_map_fibre_existence σ J v n hCM hJ _ _ (hWv n M) (hHv n)
  choose m hm using hfV
  exact ⟨_, b, laminf, lam, minf, m, hinf, hlam, hminf, hm⟩

end GlobalTheory.CompanionTheory.WeilSiegel.Frame
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinitePartOpenStatement
section
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_part_open : PositivityTheory.PfSWUS.SchInf.FinOpen := by
  first | exact @GlobalTheory.CompanionTheory.SW.FinOpenGram.finOpen | exact GlobalTheory.CompanionTheory.SW.FinOpenGram.finOpen | (intros; apply GlobalTheory.CompanionTheory.SW.FinOpenGram.finOpen <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainSplitCentreProductStatement
section
open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.CompanionTheory.CuspTransfer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamental_domain_split_centre_product : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 0 < a → ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure], IsFundamentalDomain (latticeGL E a) ((fun p : normOneGL E a × ℝ => splitCentre E a p.2 * (p.1 : GA E a)) '' (RightCosetSpace.fundamentalDomain (rationalGLOne E a) ×ˢ Set.Ico (0 : ℝ) 1)) μ := by
  first | exact @GlobalTheory.CompanionTheory.CuspTransfer.isFundamentalDomain_splitFd | exact GlobalTheory.CompanionTheory.CuspTransfer.isFundamentalDomain_splitFd | (intros; apply GlobalTheory.CompanionTheory.CuspTransfer.isFundamentalDomain_splitFd <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetLemmaHoldsStatement
section
open GlobalTheory.PRep PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_lemma_holds : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G], PositivityTheory.SphericalProduct.A4 G := by
  first | exact @GlobalTheory.CompanionTheory.Cass.sphericalProduct_A4 | exact GlobalTheory.CompanionTheory.Cass.sphericalProduct_A4 | (intros; apply GlobalTheory.CompanionTheory.Cass.sphericalProduct_A4 <;> assumption)
end

