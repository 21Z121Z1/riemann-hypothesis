import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2108
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1616
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2123
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2109
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1406
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2117
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2107
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1145
import Formalism.PieriBlockIdeals.PieriColumnMinors.RealLocalDeltaNabla
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2100
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalHeisenbergInvariantFormEqSmulDiagonalIntStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonalHeisenbergInvariant_form_eq_smul_diagonalIntegral : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (κ : Type) [Fintype κ] (l : ((κ ⊕ κ → AF D.host.F) → ℂ) →ₗ[ℂ] ℂ),
      l ∈ (GlobalTheory.WeilM.adeleClass D.host.F).adm (κ ⊕ κ) →
      (∀ x y : κ → AF D.host.F, ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (κ ⊕ κ),
        l (GlobalTheory.WeilM.schr ψ (Sum.elim x x, Sum.elim y (-y)) Φ) = l Φ) →
      ∀ μ : @MeasureTheory.Measure (κ → AF D.host.F) (borel _),
        @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
        ∃ c : ℂ, ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (κ ⊕ κ), l Φ = c * GlobalTheory.DiagSiegel.diagInt μ Φ := by
  first | exact @GlobalTheory.HostDiagUniq.eq_smul_diagInt | exact GlobalTheory.HostDiagUniq.eq_smul_diagInt | (intros; apply GlobalTheory.HostDiagUniq.eq_smul_diagInt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerRowOperatorMemDualWeylEndSubalgebra
section
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.RowDivMem
variable {O : Type} [CommRing O] {N : ℕ}

def wZ (N : ℕ) : Fin N × Fin N → (Fin N → ℤ) := fun v => Pi.single v.1 1

def δ (a b : Fin N) : Fin N → ℤ := Pi.single a 1 - Pi.single b 1

def PSh (a b : Fin N) (u : Fin N → ℤ) (P : Polynomial (MvPolynomial (Fin N × Fin N) O)) : Prop :=
  ∀ j : ℕ, IsWeightedHomogeneous (wZ N) (P.coeff j) (u + (j : ℤ) • δ a b)

theorem PSh.mul {a b : Fin N} {u u' : Fin N → ℤ} {P Q : Polynomial (MvPolynomial (Fin N × Fin N) O)}
    (hP : PSh a b u P) (hQ : PSh a b u' Q) : PSh a b (u + u') (P * Q) := by
  intro j
  rw [Polynomial.coeff_mul]
  rw [← mem_weightedHomogeneousSubmodule]
  refine Submodule.sum_mem _ fun x hx => ?_
  rw [mem_weightedHomogeneousSubmodule]
  have h := (hP x.1).mul (hQ x.2)
  have hx' : x.1 + x.2 = j := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  convert h using 1
  rw [← hx']; push_cast; rw [add_smul]; abel

theorem PSh.one (a b : Fin N) : PSh (O := O) a b 0 1 := by
  intro j
  rcases j with _ | j
  · simpa using isWeightedHomogeneous_one O (wZ N)
  · rw [Polynomial.coeff_one, if_neg (Nat.succ_ne_zero j)]
    exact isWeightedHomogeneous_zero _ _ _

theorem PSh.pow {a b : Fin N} {u : Fin N → ℤ} {P : Polynomial (MvPolynomial (Fin N × Fin N) O)}
    (hP : PSh a b u P) (n : ℕ) : PSh a b (n • u) (P ^ n) := by
  induction n with
  | zero => simpa using PSh.one (O := O) a b
  | succ n ih => rw [pow_succ, succ_nsmul]; exact ih.mul hP

theorem PSh.prod {a b : Fin N} {ι : Type} (s : Finset ι) (u : ι → Fin N → ℤ)
    (P : ι → Polynomial (MvPolynomial (Fin N × Fin N) O)) (h : ∀ i ∈ s, PSh a b (u i) (P i)) :
    PSh a b (∑ i ∈ s, u i) (∏ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PSh.one (O := O) a b
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).mul (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

theorem PSh_rowGen_X (a b : Fin N) (hab : a ≠ b) (v : Fin N × Fin N) :
    PSh a b (wZ N v) (rowGen O a b (X v)) := by
  intro j
  simp only [rowGen, aeval_X]
  rcases j with _ | _ | j
  · by_cases hv : v.1 = b
    · simp [hv]; exact isWeightedHomogeneous_X O (wZ N) v
    · simp [hv]; exact isWeightedHomogeneous_X O (wZ N) v
  · by_cases hv : v.1 = b
    · simp [hv]
      convert isWeightedHomogeneous_X O (wZ N) (a, v.2) using 1
      simp [wZ, δ, hv]
    · simp [hv]; exact isWeightedHomogeneous_zero _ _ _
  · by_cases hv : v.1 = b
    · simp [hv, Polynomial.coeff_X, Polynomial.coeff_C]
      exact isWeightedHomogeneous_zero _ _ _
    · simp [hv, Polynomial.coeff_C]; exact isWeightedHomogeneous_zero _ _ _

theorem PSh.add {a b : Fin N} {u : Fin N → ℤ} {P Q : Polynomial (MvPolynomial (Fin N × Fin N) O)}
    (hP : PSh a b u P) (hQ : PSh a b u Q) : PSh a b u (P + Q) := fun j => by
  rw [Polynomial.coeff_add]; exact (hP j).add (hQ j)

theorem PSh.zero (a b : Fin N) (u : Fin N → ℤ) : PSh (O := O) a b u 0 := fun j => by
  rw [Polynomial.coeff_zero]; exact isWeightedHomogeneous_zero _ _ _

theorem PSh_rowGen_C (a b : Fin N) (r : O) : PSh a b 0 (rowGen O a b (C r)) := by
  intro j
  rw [show (C r : MvPolynomial (Fin N × Fin N) O) = algebraMap O _ r from rfl, AlgHom.commutes,
    Polynomial.algebraMap_apply, Polynomial.coeff_C]
  split_ifs with h
  · subst h
    simp only [Nat.cast_zero, zero_smul, add_zero]
    exact isWeightedHomogeneous_C (wZ N) r
  · exact isWeightedHomogeneous_zero _ _ _

theorem PSh_rowGen (a b : Fin N) (hab : a ≠ b) (u : Fin N → ℤ) (f : MvPolynomial (Fin N × Fin N) O)
    (hf : IsWeightedHomogeneous (wZ N) f u) : PSh a b u (rowGen O a b f) := by
  classical
  rw [f.as_sum, map_sum]
  have key : ∀ d ∈ f.support, PSh a b u (rowGen O a b (monomial d (coeff d f))) := by
    intro d hd
    have hw : Finsupp.weight (wZ N) d = u := hf (mem_support_iff.mp hd)
    rw [monomial_eq, map_mul, Finsupp.prod, map_prod]
    have h1 := (PSh_rowGen_C a b (coeff d f)).mul
      (PSh.prod d.support (fun v => d v • wZ N v) (fun v => rowGen O a b (X v ^ d v)) fun v _ => by
        rw [map_pow]; exact (PSh_rowGen_X a b hab v).pow (d v))
    rw [zero_add] at h1
    convert h1 using 1
    rw [← hw, Finsupp.weight_apply, Finsupp.sum]
  exact Finset.sum_induction _ (PSh a b u) (fun _ _ => PSh.add) (PSh.zero a b u) key

theorem weight_wZ (d : Fin N × Fin N →₀ ℕ) (c : Fin N) :
    Finsupp.weight (wZ N) d c = (Finsupp.weight (rowW N N) d c : ℤ) := by
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, wZ, rowW, Nat.cast_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [Pi.single_apply]

def shiftW (a b : Fin N) (k : ℕ) (w : Fin N → ℕ) : Fin N → ℕ :=
  fun c => w c + (if c = a then k else 0) - (if c = b then k else 0)

theorem rowDiv_isWH (a b : Fin N) (hab : a ≠ b) (j : ℕ) (w : Fin N → ℕ) (f : MvPolynomial (Fin N × Fin N) O)
    (hf : IsWeightedHomogeneous (rowW N N) f w) :
    IsWeightedHomogeneous (wZ N) (rowDiv O a b j f) ((fun c => (w c : ℤ)) + (j : ℤ) • δ a b) := by
  have hf' : IsWeightedHomogeneous (wZ N) f (fun c => (w c : ℤ)) := by
    intro d hd
    funext c
    rw [weight_wZ, hf hd]
  exact PSh_rowGen a b hab _ f hf' j

theorem proj_rowDiv (a b : Fin N) (hab : a ≠ b) (j k : ℕ) (w : Fin N → ℕ) (f : MvPolynomial (Fin N × Fin N) O)
    (hf : IsWeightedHomogeneous (rowW N N) f w) :
    weightedHomogeneousComponent (rowW N N) (shiftW a b k w) (rowDiv O a b j f) =
      if j = k then rowDiv O a b k f else 0 := by
  classical
  have hg := rowDiv_isWH a b hab j w f hf
  ext d
  rw [coeff_weightedHomogeneousComponent]
  split_ifs with h1 h2 h2
  · subst h2; rfl
  · by_contra hne
    have := congrFun (hg hne) a
    rw [weight_wZ, h1] at this
    simp [shiftW, δ, hab, Pi.single_apply] at this
    omega
  · subst h2
    by_contra hne
    apply h1
    funext c
    have := congrFun (hg (Ne.symm hne)) c
    rw [weight_wZ] at this
    simp only [shiftW, δ, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.single_apply, smul_eq_mul] at this ⊢
    split_ifs at this ⊢ <;> omega
  · simp

theorem rowAct_transvection (a b : Fin N) (h : MvPolynomial (Fin N × Fin N) O) :
    rowAct O (Matrix.transvection b a (1 : O)) h = Polynomial.eval 1 (rowGen O a b h) := by
  classical
  have key : (Polynomial.evalRingHom (1 : MvPolynomial (Fin N × Fin N) O)).comp (rowGen O a b (n := N)).toRingHom =
      (rowAct O (n := N) (Matrix.transvection b a (1 : O))).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [rowGen, rowAct]
    · intro v
      simp [rowGen, rowAct, Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
        Finset.sum_add_distrib, add_mul, ite_mul]
      by_cases hv : v.1 = b
      · subst hv; simp
      · simp [hv, Ne.symm hv]
  exact (RingHom.congr_fun key h).symm

theorem proj_rowAct (a b : Fin N) (hab : a ≠ b) (k : ℕ) (w : Fin N → ℕ) (f : MvPolynomial (Fin N × Fin N) O)
    (hf : IsWeightedHomogeneous (rowW N N) f w) :
    weightedHomogeneousComponent (rowW N N) (shiftW a b k w) (rowAct O (Matrix.transvection b a (1 : O)) f) =
      rowDiv O a b k f := by
  classical
  rw [rowAct_transvection, Polynomial.eval_eq_sum_range]
  simp only [one_pow, mul_one, map_sum]
  have : ∀ j, (rowGen O a b f).coeff j = rowDiv O a b j f := fun j => rfl
  simp only [this, proj_rowDiv a b hab _ k w f hf, Finset.sum_ite_eq', Finset.mem_range]
  split_ifs with hk
  · rfl
  · exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)).symm

theorem rowW_le_total (d : Fin N × Fin N →₀ ℕ) (c : Fin N) :
    Finsupp.weight (rowW N N) d c ≤ ∑ s, Finsupp.weight (colW N N) d s := by
  classical
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, rowW, colW, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun v _ => ?_
  rw [← Finset.mul_sum]
  simp [Pi.single_apply]
  split_ifs <;> simp

def box (ν : Fin N → ℕ) : Finset (Fin N → ℕ) :=
  Fintype.piFinset fun _ : Fin N => Finset.range (∑ s, ν s + 1)

theorem decomp (ν : Fin N → ℕ) (f : MvPolynomial (Fin N × Fin N) O) (hf : f ∈ dualWeyl O N N ν) :
    f = ∑ w ∈ box ν, weightedHomogeneousComponent (rowW N N) w f := by
  classical
  have hcol : IsWeightedHomogeneous (colW N N) f ν :=
    (mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.mem_inf.mp hf).1
  ext d
  rw [coeff_sum]
  simp only [coeff_weightedHomogeneousComponent, Finset.sum_ite_eq, ]
  split_ifs with h
  · rfl
  · by_contra hne
    apply h
    have hw := hcol hne
    simp only [box, Fintype.mem_piFinset, Finset.mem_range]
    intro c
    have := rowW_le_total d c
    rw [hw] at this
    omega

end GlobalTheory.RowDivMem

namespace GlobalTheory.GenCoef
open GlobalTheory.RowDivMem

theorem rowDiv_mem_dwAlg : ∀ (O : Type) [CommRing O] (N : ℕ) (ν : Fin N → ℕ) (a b : Fin N), a ≠ b → ∀ k : ℕ,
    ∃ p ∈ dwAlg O N ν, ∀ f : dualWeyl O N N ν,
      (p f : MvPolynomial (Fin N × Fin N) O) = rowDiv O a b k (f : MvPolynomial (Fin N × Fin N) O) := by
  intro O _ N ν a b hab k
  classical
  let g : GL (Fin N) O :=
    ⟨Matrix.transvection b a (-1), Matrix.transvection b a 1,
      by rw [Matrix.transvection_mul_transvection_same b a (Ne.symm hab)]; simp,
      by rw [Matrix.transvection_mul_transvection_same b a (Ne.symm hab)]; simp⟩
  have hg : ((g⁻¹ : GL (Fin N) O) : Matrix (Fin N) (Fin N) O) = Matrix.transvection b a 1 := rfl
  refine ⟨∑ w ∈ box ν, GlobalTheory.ExpFrame.rowProj O N ν (shiftW a b k w) * Formalism.UG.dualWeylRep O N N ν g *
      GlobalTheory.ExpFrame.rowProj O N ν w, ?_, fun f => ?_⟩
  · refine Subalgebra.sum_mem _ fun w _ => Subalgebra.mul_mem _ (Subalgebra.mul_mem _ ?_ ?_) ?_
    · exact Algebra.subset_adjoin (Or.inr ⟨_, rfl⟩)
    · exact Algebra.subset_adjoin (Or.inl ⟨g, rfl⟩)
    · exact Algebra.subset_adjoin (Or.inr ⟨_, rfl⟩)
  · rw [LinearMap.sum_apply, Submodule.coe_sum]
    conv_rhs => rw [decomp ν (f : MvPolynomial (Fin N × Fin N) O) f.2]
    have hlin : ∀ (s : Finset (Fin N → ℕ)) (F : (Fin N → ℕ) → MvPolynomial (Fin N × Fin N) O),
        rowDiv O a b k (∑ w ∈ s, F w) = ∑ w ∈ s, rowDiv O a b k (F w) := by
      intro s F
      simp only [rowDiv, map_sum, Polynomial.finset_sum_coeff]
    rw [hlin]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [Module.End.mul_apply]
    change weightedHomogeneousComponent (rowW N N) (shiftW a b k w)
      (Formalism.UG.dwAct O N N g (weightedHomogeneousComponent (rowW N N) w (f : MvPolynomial (Fin N × Fin N) O))) = _
    rw [Formalism.UG.dwAct, hg]
    exact proj_rowAct a b hab k w _ (weightedHomogeneousComponent_isWeightedHomogeneous _ _)

end GlobalTheory.GenCoef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledWeilRepFixesVacuumTensorSiegelParabolicInStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledWeilRep_fixes_vacuum_tensor_siegelParabolic_inert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T → ∀ (dd : Darboux (symp (cA σ) (-1) (incM F G.V'.J) (dbl (incM F G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')))
      (omd : UG (cA σ) (dbl (incM F G.W.J)) →* Module.End ℂ ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → AF F) → ℂ)),
      IsDblCoord (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) G.M'.co dd →
      IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V'.J) (dbl (incM F G.W.J)) dd X.α (diagCols (Fin (a + a'))) omd →
    ∀ R : (Fin a' × Fin (a + a') → AF F) → ℂ, R 0 ≠ 0 → Rest (evFin F v) (G.M'.vac v) R →
    ∀ p ∈ GlobalTheory.InertDbl.ParD σ G.W v, omd p (GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R)) =
      GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R) := by
  first | exact @GlobalTheory.InertDblPar.parD_fix | exact GlobalTheory.InertDblPar.parD_fix | (intros; apply GlobalTheory.InertDblPar.parD_fix <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylTensorLiftEquivariant
section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameRead.LiftEquiv

theorem map_rowAct_eq {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {r n : ℕ}
    (M : Matrix (Fin r) (Fin r) R) (f : MvPolynomial (Fin r × Fin n) R) :
    MvPolynomial.map φ (rowAct R M f) = rowAct S (M.map φ) (MvPolynomial.map φ f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [rowAct]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    rw [map_mul, map_mul, map_mul, hp, map_X]
    congr 1
    simp [rowAct, map_sum, Matrix.map_apply]

theorem rowAct_detPol_eq {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) :
    rowAct R M (detPol R n) = MvPolynomial.C M.det * detPol R n := by
  unfold detPol
  rw [AlgHom.map_det, RingHom.map_det (MvPolynomial.C : R →+* MvPolynomial (Fin n × Fin n) R), ← Matrix.det_mul]
  congr 1
  ext1 a s
  simp [rowAct, Matrix.mul_apply]

theorem rowAct_liftPol_eq {K C : Type} [CommRing K] [CommRing C] {n : ℕ} (e0 : K →+* C) (k : ℕ)
    (M : Matrix (Fin n) (Fin n) K) (f : MvPolynomial (Fin n × Fin n) K) :
    rowAct C (M.map e0) (liftPol e0 k f) = (e0 M.det) ^ k • liftPol e0 k (rowAct K M f) := by
  unfold liftPol
  have hd : (M.map e0).det = e0 M.det := (RingHom.map_det e0 M).symm
  rw [map_mul, map_pow, rowAct_detPol_eq, map_rowAct_eq, mul_pow, smul_eq_C_mul, map_pow, mul_assoc, hd]

theorem grp_tprod_eq (C : Type) [CommRing C] {ι : Type} (n : ℕ) (lamW : ι → ℕ → ℕ) (g : ι → GL (Fin n) C)
    (y : ∀ τ, dualWeyl C n n (res n (lamW τ))) :
    grp C n lamW g (PiTensorProduct.tprod C y) =
      PiTensorProduct.tprod C (fun τ => Formalism.UG.dualWeylRep C n n (res n (lamW τ)) (g τ) (y τ)) :=
  PiTensorProduct.map_tprod _ _

theorem scalar_eq {K C : Type} [Field K] [Field C] (e0 : K →+* C) {n : ℕ} (lam : DomWeight n) (k : ℕ) (c : ℤ)
    (h : ∀ hn : 0 < n, (k : ℤ) = lam.w ⟨n - 1, by omega⟩ + c) (g : GL (Fin n) K) :
    e0 (detPow K n (inside₂ K n g) lam.detShift) =
      ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map e0 g) ^ c : Cˣ) : C) *
        e0 ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det ^ k := by
  have h1 : ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = ((g : Matrix (Fin n) (Fin n) K).det)⁻¹ := by
    rw [Matrix.coe_units_inv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  have h2 : ((inside₂ K n g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = ((g : Matrix (Fin n) (Fin n) K).det)⁻¹ := by
    rw [← h1]; exact Matrix.det_transpose _
  have h3 : ((Matrix.GeneralLinearGroup.map e0 g : GL (Fin n) C) : Matrix (Fin n) (Fin n) C).det =
      e0 (g : Matrix (Fin n) (Fin n) K).det := (RingHom.map_det e0 _).symm
  have h0 : e0 (g : Matrix (Fin n) (Fin n) K).det ≠ 0 := by
    rw [map_ne_zero]; exact g.det_ne_zero
  simp only [detPow, Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply, h1, h2, h3, map_zpow₀, map_inv₀]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have he : lam.detShift = k - c := by
      rw [h hn]; simp [DomWeight.detShift, hn]
    rw [he, inv_zpow', inv_pow, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ h0]
    congr 1
    ring

theorem phi_equivariant : ∀ (K C : Type) [Field K] [Field C] (e0 : K →+* C) (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (lam : ι → DomWeight n) (lamW : ι → ℕ → ℕ) (c : ι → ℤ) (Φ : VV K lam →ₛₗ[e0] NablaT C n lamW), Shift lam lamW c → IsPhi e0 lam lamW Φ → ∀ (g : ι → GL (Fin n) K) (v : VV K lam), Φ (rhoK lam (invTrK g) v) = lamG C n lamW c (fun τ => Matrix.GeneralLinearGroup.map e0 (g τ)) (Φ v) := by
  intro K C _ _ e0 ι _ _ n lam lamW c Φ hS hΦ g v
  obtain ⟨v, hv⟩ := v
  induction hv using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨x, hx, rfl⟩ := hP
    let M : ι → Matrix (Fin n) (Fin n) K := fun τ => ((g τ)⁻¹ : GL (Fin n) K)
    have hx' : ∀ τ, rowAct K (M τ) (x τ) ∈ nablaSq K n (lam τ) := fun τ =>
      Formalism.GradedWeylDivisibility.dualWeylRowStable K n n _ _ _ (hx τ)
    let w : VV K lam := ⟨Formalism.L2.DIV.ten fun τ => rowAct K (M τ) (x τ),
      Submodule.subset_span ⟨_, hx', rfl⟩⟩
    obtain ⟨y, hy, hyv⟩ := hΦ x ⟨_, Submodule.subset_span ⟨x, hx, rfl⟩⟩ hx rfl
    obtain ⟨y', hy', hyw⟩ := hΦ _ w hx' rfl
    have hr : rhoK lam (invTrK g) ⟨_, Submodule.subset_span ⟨x, hx, rfl⟩⟩ = detTwK lam (invTrK g) • w := by
      apply Subtype.ext
      show detTwK lam (invTrK g) • trAct (invTrK g) (∏ τ, blockEmb K τ (x τ)) =
        detTwK lam (invTrK g) • ∏ τ, blockEmb K τ (rowAct K (M τ) (x τ))
      congr 1
      rw [map_prod]
      refine Finset.prod_congr rfl fun τ _ => ?_
      exact (Formalism.GradedWeylDivisibility.blockActTensor K K ι n n M).1 τ (x τ)
    have hg : (fun τ => Formalism.UG.dualWeylRep C n n (res n (lamW τ)) (Matrix.GeneralLinearGroup.map e0 (g τ)) (y τ)) =
        fun τ => (e0 (M τ).det) ^ (lamW τ (n - 1)) • y' τ := by
      funext τ
      apply Subtype.ext
      show rowAct C (((Matrix.GeneralLinearGroup.map e0 (g τ))⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) (y τ) =
        (e0 (M τ).det) ^ (lamW τ (n - 1)) • (y' τ : MvPolynomial (Fin n × Fin n) C)
      rw [hy, hy', ← map_inv]
      exact rowAct_liftPol_eq e0 _ (M τ) (x τ)
    rw [hr, LinearMap.map_smulₛₗ, hyw, hyv, lamG_apply, grp_tprod_eq, hg, MultilinearMap.map_smul_univ, smul_smul]
    congr 1
    rw [detTwK, map_prod, Units.coe_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    exact scalar_eq e0 (lam τ) _ (c τ) (fun hn => hS τ ⟨n - 1, by omega⟩) (g τ)
  | zero =>
    show Φ (rhoK lam (invTrK g) 0) = lamG C n lamW c _ (Φ 0)
    simp only [map_zero]
  | add a b ha hb iha ihb =>
    show Φ (rhoK lam (invTrK g) (⟨a, ha⟩ + ⟨b, hb⟩)) = lamG C n lamW c _ (Φ (⟨a, ha⟩ + ⟨b, hb⟩))
    simp only [map_add]
    rw [iha, ihb]
  | smul r a ha iha =>
    show Φ (rhoK lam (invTrK g) (r • ⟨a, ha⟩)) = lamG C n lamW c _ (Φ (r • ⟨a, ha⟩))
    rw [map_smul, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, map_smul, iha]

end GlobalTheory.FrameRead.LiftEquiv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylTensorReductionIntertwinesGroupAction
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.HighWtEmb

namespace GlobalTheory.HighWtEmb

theorem blockRed_rowAct (O : Type) [CommRing O] (N : ℕ) {ι : Type} (ϖ : O) (τ : ι)
    (A : ι → Matrix (Fin N) (Fin N) (O ⧸ Ideal.span {ϖ})) (M : Matrix (Fin N) (Fin N) O)
    (hA : A τ = M.map (Ideal.Quotient.mk (Ideal.span {ϖ}))) (f : MvPolynomial (Fin N × Fin N) O) :
    blockRed O N ϖ τ (rowAct O M f) = blockSub (O ⧸ Ideal.span {ϖ}) N A (blockRed O N ϖ τ f) := by
  have h : (blockRed O N ϖ τ).comp (rowAct O M) =
      ((blockSub (O ⧸ Ideal.span {ϖ}) N A).restrictScalars O).comp (blockRed O N ϖ τ) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, rowAct, blockRed, blockSub, aeval_X, map_sum, map_mul,
      hA, Matrix.map_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    congr 1
    rw [aeval_C]
    rfl
  exact congrArg (fun φ => φ f) h

end GlobalTheory.HighWtEmb

theorem GlobalTheory.HighWtEmb.redT_grp : ∀ (O : Type) [CommRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (mu : ι → ℕ → ℕ) (ϖ : O) (g : ι → GL (Fin N) O) (y : NablaT O N mu), redT O N mu ϖ (grp O N mu g y) = blockSub (O ⧸ Ideal.span {ϖ}) N (fun τ => (((g τ)⁻¹ : GL (Fin N) O) : Matrix (Fin N) (Fin N) O).map (Ideal.Quotient.mk (Ideal.span {ϖ}))) (redT O N mu ϖ y) := by
  intro O _ N ι _ _ mu ϖ g y
  induction y using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    rw [LinearMap.map_smul, LinearMap.map_smul, LinearMap.map_smul]
    have h1 := (Formalism.CohomologicalDescent.RealLocalDeltaNabla.nabla_rep_tensor_product O ι (fun _ => N) (fun _ => N) (fun τ => res N (mu τ)) g m)
    simp only [GlobalTheory.ExpFrame.grp]
    rw [h1.1]
    simp only [redT, PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply,
      LinearMap.comp_apply, Submodule.subtype_apply, AlgHom.toLinearMap_apply]
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_prod, IsScalarTower.algebraMap_apply O (O ⧸ Ideal.span {ϖ}), AlgHom.commutes]
    congr 1
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [h1.2 τ]
    exact blockRed_rowAct O N ϖ τ _ _ rfl _
  | add a b ha hb => simp only [map_add, ha, hb]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventualL6OfLowerBoundStatement
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventual_L6_of_lower_bound : GlobalTheory.BigTop.LamLow → ∀ (𝒜 : FamClass) (σ : RawSel Part 𝒜), (∀ (eps : ℝ) (Fm : FamP eps), 𝒜 Fm → GlobalTheory.EX.DQ.Duty7 Fm) → EvW PRows 𝒜 σ → EvWC (fun _ => True) L6 𝒜 σ := by
  first | exact @GlobalTheory.Fc.Ind.eventual_L6_of_lower_scalar | exact GlobalTheory.Fc.Ind.eventual_L6_of_lower_scalar | (intros; apply GlobalTheory.Fc.Ind.eventual_L6_of_lower_scalar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventualOntoOfMorePointsStatement
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventual_onto_of_more_points : GlobalTheory.BigOn.OntoX → ∀ (𝒜 : FamClass) (σ : RawSel Part 𝒜), (∀ (eps : ℝ) (Fm : FamP eps), 𝒜 Fm → GlobalTheory.EX.DQ.Duty7 Fm) → EvW PRows 𝒜 σ → EvW (fun _ _ _ b => GlobalTheory.BigOn.More b.pt) 𝒜 σ → EvWC (fun Fm => DIVinN Fm) ON 𝒜 σ := by
  first | exact @GlobalTheory.Fc.Ind.onto_at_chosen | exact GlobalTheory.Fc.Ind.onto_at_chosen | (intros; apply GlobalTheory.Fc.Ind.onto_at_chosen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoefficientPolynomialGLFunctionNeZeroStatement
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coefficientPolynomial_GLFunction_ne_zero : ∀ {D : D7} {n : ℕ} (lam : D.what₂.Tau → DomWeight n),
    ∃ (F : VV D.what₂.LL lam) (x : GLR D n), coefFn D.what₂.embLL lam (F : Pol D.what₂.LL D.what₂.Tau n) x ≠ 0 := by
  first | exact @GlobalTheory.CoeffNonvanish.exists_coefFn_ne_zero | exact GlobalTheory.CoeffNonvanish.exists_coefFn_ne_zero | (intros; apply GlobalTheory.CoeffNonvanish.exists_coefFn_ne_zero <;> assumption)
end
end

