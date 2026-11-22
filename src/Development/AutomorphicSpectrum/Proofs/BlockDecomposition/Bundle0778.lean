import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0773
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0334
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0736
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0774
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0744
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0751
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0749
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0747
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0748
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1870
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0771
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KFiniteVectorsDense
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0775

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EventuallyMapLatLocEqLatO
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.MM

namespace GlobalTheory.CompanionTheory.MM.LatStd

open NumberField IsDedekindDomain Filter

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField E] in

theorem map_comp_apply_evalV (v : HeightOneSpectrum (𝓞 F)) (z : AF F ⊗[F] E) :
    Algebra.TensorProduct.map ((HeckeCharacterZeroLocus.SiegelWeilU.evalV F v).comp (HeckeCharacterZeroLocus.SiegelWeilU.sndA F)) (AlgHom.id F E) z =
      Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E)
        (Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.sndA F) (AlgHom.id F E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp; rfl
  | add y z hy hz => simp only [map_add, hy, hz]

theorem eventually_matV_mem_intLoc {n : ℕ} (h : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ a c, PositivityTheory.SiegelWeilFormula.Gen.matV v h a c ∈ intLoc F E v :=
  eventually_all.2 fun a => eventually_all.2 fun c => by
    filter_upwards [eventually_map_evalV_mem_intLoc
      (Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.sndA F) (AlgHom.id F E) (h a c))] with v hv
    change Algebra.TensorProduct.map ((HeckeCharacterZeroLocus.SiegelWeilU.evalV F v).comp (HeckeCharacterZeroLocus.SiegelWeilU.sndA F)) (AlgHom.id F E) (h a c) ∈ _
    rw [map_comp_apply_evalV]
    exact hv

omit [NumberField E] in

theorem matV_mul_eq_one {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) {h h' : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)}
    (hh : h * h' = 1) : PositivityTheory.SiegelWeilFormula.Gen.matV v h * PositivityTheory.SiegelWeilFormula.Gen.matV v h' = 1 := by
  have e := map_mul (AlgHom.mapMatrix (m := Fin n) (Algebra.TensorProduct.map
    ((HeckeCharacterZeroLocus.SiegelWeilU.evalV F v).comp (HeckeCharacterZeroLocus.SiegelWeilU.sndA F)) (AlgHom.id F E))) h h'
  rw [hh, map_one] at e
  exact e.symm

omit [NumberField E] in

theorem mulVec_mem_intLoc {n : ℕ} {v : HeightOneSpectrum (𝓞 F)} {M : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)}
    (hM : ∀ a c, M a c ∈ intLoc F E v) {x : Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E} (hx : ∀ c, x c ∈ intLoc F E v)
    (a : Fin n) : M.mulVec x a ∈ intLoc F E v := by
  simp only [Matrix.mulVec, dotProduct]
  exact sum_mem fun c _ => mul_mem (hM a c) (hx c)

theorem eventually_map_latLoc_eq_latO {n d : ℕ} {h h' : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)} (hh : h * h' = 1)
    (bs : Module.Basis (Fin d) F E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      (((latLoc F (stdLattice E n) v).toAddSubgroup.map
        (Matrix.mulVecLin (PositivityTheory.SiegelWeilFormula.Gen.matV v h)).toAddMonoidHom : AddSubgroup _) :
          Set (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) = PositivityTheory.PfSWUS.Loc.latO bs v := by
  filter_upwards [GlobalTheory.AdelicU.Cofinite.eventually_mem_intLoc_iff_repr bs, eventually_matV_mem_intLoc h,
    eventually_matV_mem_intLoc h'] with v hb h1 h2
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' := mem_latLoc_stdLattice.1 hx
    intro a k
    refine (hb _).1 ?_ k
    exact mulVec_mem_intLoc h1 hx' a
  · intro hy
    have hy' : ∀ a, y a ∈ intLoc F E v := fun a => (hb _).2 (hy a)
    refine ⟨(PositivityTheory.SiegelWeilFormula.Gen.matV v h').mulVec y,
      mem_latLoc_stdLattice.2 (mulVec_mem_intLoc h2 hy'), ?_⟩
    change (PositivityTheory.SiegelWeilFormula.Gen.matV v h).mulVec ((PositivityTheory.SiegelWeilFormula.Gen.matV v h').mulVec y) = y
    rw [Matrix.mulVec_mulVec, matV_mul_eq_one v hh, Matrix.one_mulVec]

theorem latAt_eq_latO : ∀ (D : D7) (n : ℕ) (h : GL (Fin n) (AE D)) (d : ℕ) (bs : Module.Basis (Fin d) D.host.F D.host.E), ∀ᶠ v in Filter.cofinite, ((latAt h.1 v : AddSubgroup _) : Set (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)) = PositivityTheory.PfSWUS.Loc.latO bs v := by
  intro D n h d bs
  have hh : h.1 * (h⁻¹).1 = 1 := by simp
  exact eventually_map_latLoc_eq_latO hh bs

end GlobalTheory.CompanionTheory.MM.LatStd
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EventuallyMulClosed
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.MM

namespace GlobalTheory.CompanionTheory.PureTwist

open IsDedekindDomain

def twistT {A : Type} [CommRing A] {n M : ℕ} (m : Matrix (Fin n) (Fin n) A) (Y : Fin n → Fin M → A) :
    Fin n → Fin M → A :=
  fun j i => ∑ k, Y k i * m k j

theorem twistT_twistT {A : Type} [CommRing A] {n M : ℕ} {m m' : Matrix (Fin n) (Fin n) A} (h : m * m' = 1)
    (Y : Fin n → Fin M → A) : twistT m' (twistT m Y) = Y := by
  funext j i
  simp only [twistT, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have hm : ∀ k, ∑ l, m k l * m' l j = (1 : Matrix (Fin n) (Fin n) A) k j := fun k => by
    rw [← h, Matrix.mul_apply]
  simp [hm, Matrix.one_apply]

def twistH {A : Type} [CommRing A] [TopologicalSpace A] [ContinuousMul A] [ContinuousAdd A] {n M : ℕ}
    {m m' : Matrix (Fin n) (Fin n) A} (h : m * m' = 1) (h' : m' * m = 1) :
    (Fin n → Fin M → A) ≃ₜ (Fin n → Fin M → A) where
  toFun := twistT m
  invFun := twistT m'
  left_inv := twistT_twistT h
  right_inv := twistT_twistT h'
  continuous_toFun := continuous_pi fun _ => continuous_pi fun i => continuous_finsetSum _ fun k _ =>
    (continuous_apply_apply k i).mul continuous_const
  continuous_invFun := continuous_pi fun _ => continuous_pi fun i => continuous_finsetSum _ fun k _ =>
    (continuous_apply_apply k i).mul continuous_const

section Int

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}

def intE (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    Set (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) :=
  {x | ∀ k, (Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) b).repr x k ∈ v.adicCompletionIntegers F}

theorem repr_tmul (b : Module.Basis (Fin d) F E) {R : Type} [CommRing R] [Algebra F R] (x : R) (e : E) (k : Fin d) :
    (Algebra.TensorProduct.basis R b).repr (x ⊗ₜ[F] e) k = x * algebraMap F R (b.repr e k) := by
  simp [Algebra.TensorProduct.basis_repr_tmul]

theorem eq_sum_tmul (b : Module.Basis (Fin d) F E) {R : Type} [CommRing R] [Algebra F R] (x : R ⊗[F] E) :
    x = ∑ k, (Algebra.TensorProduct.basis R b).repr x k ⊗ₜ[F] b k := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis R b).sum_repr x]
  simp [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul']

theorem eventually_adele (t : HeckeCharacterZeroLocus.SiegelWeilU.Af F) :
    ∀ᶠ v : HeightOneSpectrum (NumberField.RingOfIntegers F) in Filter.cofinite,
      HeckeCharacterZeroLocus.SiegelWeilU.evalV F v t ∈ v.adicCompletionIntegers F := by
  exact t.2

theorem eventually_const (c : F) :
    ∀ᶠ v : HeightOneSpectrum (NumberField.RingOfIntegers F) in Filter.cofinite,
      algebraMap F (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) c ∈ v.adicCompletionIntegers F := by
  filter_upwards [eventually_adele (F := F) (algebraMap F (HeckeCharacterZeroLocus.SiegelWeilU.Af F) c)] with v hv
  rwa [AlgHom.commutes] at hv

theorem sum_mem_intE (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (NumberField.RingOfIntegers F))
    {ι : Type} (s : Finset ι) (f : ι → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) (h : ∀ i ∈ s, f i ∈ intE b v) :
    ∑ i ∈ s, f i ∈ intE b v := by
  intro k
  rw [map_sum, Finsupp.finsetSum_apply]
  exact sum_mem fun i hi => h i hi k

theorem mul_mem_intE (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (NumberField.RingOfIntegers F))
    (hc : ∀ i j k, algebraMap F (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) (b.repr (b i * b j) k) ∈ v.adicCompletionIntegers F)
    {x y : HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E} (hx : x ∈ intE b v) (hy : y ∈ intE b v) : x * y ∈ intE b v := by
  simp only [intE, Set.mem_ofPred_eq] at hx hy ⊢
  intro k
  rw [eq_sum_tmul b x, eq_sum_tmul b y, Finset.sum_mul_sum]
  simp only [Algebra.TensorProduct.tmul_mul_tmul, map_sum, Finsupp.finsetSum_apply, repr_tmul]
  refine sum_mem fun i _ => sum_mem fun j _ => ?_
  exact mul_mem (mul_mem (hx i) (hy j)) (hc i j k)

theorem eventually_mul_closed (b : Module.Basis (Fin d) F E) :
    ∀ᶠ v : HeightOneSpectrum (NumberField.RingOfIntegers F) in Filter.cofinite,
      ∀ i j k, algebraMap F (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) (b.repr (b i * b j) k) ∈ v.adicCompletionIntegers F := by
  simp only [Filter.eventually_all]
  intro i j k
  exact eventually_const _

theorem eventually_mem_intE (b : Module.Basis (Fin d) F E) (x : HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E) :
    ∀ᶠ v : HeightOneSpectrum (NumberField.RingOfIntegers F) in Filter.cofinite,
      Algebra.TensorProduct.map ((HeckeCharacterZeroLocus.SiegelWeilU.evalV F v).comp (HeckeCharacterZeroLocus.SiegelWeilU.sndA F)) (AlgHom.id F E) x ∈ intE b v := by
  have hall : ∀ᶠ v : HeightOneSpectrum (NumberField.RingOfIntegers F) in Filter.cofinite, ∀ k,
      HeckeCharacterZeroLocus.SiegelWeilU.evalV F v (HeckeCharacterZeroLocus.SiegelWeilU.sndA F
        ((Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.AF F) b).repr x k)) ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.mpr fun k => eventually_adele _
  filter_upwards [hall] with v hv
  rw [eq_sum_tmul b x]
  simp only [map_sum, Algebra.TensorProduct.map_tmul, AlgHom.coe_comp, Function.comp_apply, AlgHom.id_apply]
  refine sum_mem_intE b v _ _ fun k _ => ?_
  intro k'
  rw [repr_tmul, Module.Basis.repr_self, Finsupp.single_apply]
  split_ifs with hk
  · subst hk
    rw [map_one, mul_one]
    exact hv _
  · rw [map_zero, mul_zero]
    exact zero_mem _

theorem eventually_matV_mem (b : Module.Basis (Fin d) F E) {n : ℕ}
    (h : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)) :
    ∀ᶠ v : HeightOneSpectrum (NumberField.RingOfIntegers F) in Filter.cofinite,
      ∀ k j, PositivityTheory.SiegelWeilFormula.Gen.matV v h k j ∈ intE b v := by
  simp only [Filter.eventually_all]
  intro k j
  filter_upwards [eventually_mem_intE b (h k j)] with v hv
  simpa [PositivityTheory.SiegelWeilFormula.Gen.matV] using hv

theorem twistT_mem_latV (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (NumberField.RingOfIntegers F))
    (hc : ∀ i j k, algebraMap F (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) (b.repr (b i * b j) k) ∈ v.adicCompletionIntegers F)
    {n M : ℕ} {m : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)} (hm : ∀ k j, m k j ∈ intE b v)
    {Y : Fin n → Fin M → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E} (hY : Y ∈ HeckeCharacterZeroLocus.SiegelWeilU.latV b v) :
    twistT m Y ∈ HeckeCharacterZeroLocus.SiegelWeilU.latV b v := by
  intro a i
  exact sum_mem_intE b v _ _ fun k _ => mul_mem_intE b v hc (hY k i) (hm k a)

theorem matV_mul_eq_one {n : ℕ} (v : HeightOneSpectrum (NumberField.RingOfIntegers F))
    {h h' : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)} (e : h * h' = 1) :
    PositivityTheory.SiegelWeilFormula.Gen.matV (E := E) v h * PositivityTheory.SiegelWeilFormula.Gen.matV v h' = 1 := by
  simp only [PositivityTheory.SiegelWeilFormula.Gen.matV]
  rw [← AlgHom.mapMatrix_apply, ← AlgHom.mapMatrix_apply, ← map_mul, e, map_one]

end Int

theorem map_evalV_finPart (D : D7) (v : HeightOneSpectrum (NumberField.RingOfIntegers D.host.F)) (x : AE D) :
    Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.evalV D.host.F v) (AlgHom.id D.host.F D.host.E) (finPart D x) =
      Algebra.TensorProduct.map ((HeckeCharacterZeroLocus.SiegelWeilU.evalV D.host.F v).comp (HeckeCharacterZeroLocus.SiegelWeilU.sndA D.host.F))
        (AlgHom.id D.host.F D.host.E) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp only [Formalism.L2.Theta.finPart, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.map_tmul, AlgHom.coe_comp, Function.comp_apply, AlgHom.id_apply]
    rfl
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

theorem isPureFin_twist : ∀ (D : D7) (n M d : ℕ) (bs : Module.Basis (Fin d) D.host.F D.host.E) (g : (Fin M → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ) (gv : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F), (Fin n → Fin M → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E) → ℂ) (a : GL (Fin n) (AE D)), HeckeCharacterZeroLocus.SiegelWeilU.IsPureFin bs (fun X => g fun i j => X j i) gv → HeckeCharacterZeroLocus.SiegelWeilU.IsPureFin bs (fun Y => g fun i j => ∑ k, Y k i * finPart D (a.1 k j)) (fun v Y => gv v (fun j i => ∑ k, Y k i * PositivityTheory.SiegelWeilFormula.Gen.matV v a.1 k j)) := by
  intro D n M d bs g gv a H
  obtain ⟨hSB, hev, hprod⟩ := H
  have e1 : a.1 * a⁻¹.1 = 1 := a.mul_inv
  have e2 : a⁻¹.1 * a.1 = 1 := a.inv_mul
  refine ⟨fun v => ?_, ?_, fun Y => ?_⟩
  · let T := twistH (M := M) (matV_mul_eq_one v e1) (matV_mul_eq_one v e2)
    obtain ⟨hlc, hcs⟩ := hSB v
    exact ⟨hlc.comp_continuous T.continuous, hcs.comp_homeomorph T⟩
  · filter_upwards [hev, eventually_mul_closed bs, eventually_matV_mem bs a.1,
      eventually_matV_mem bs a⁻¹.1] with v hv hc hm hm'
    funext Y
    rw [hv]
    show (HeckeCharacterZeroLocus.SiegelWeilU.latV bs v).indicator 1 (twistT (PositivityTheory.SiegelWeilFormula.Gen.matV v a.1) Y) = _
    have hiff : twistT (PositivityTheory.SiegelWeilFormula.Gen.matV v a.1) Y ∈ HeckeCharacterZeroLocus.SiegelWeilU.latV bs v ↔
        Y ∈ HeckeCharacterZeroLocus.SiegelWeilU.latV bs v := by
      constructor
      · intro hY
        have h1 := twistT_mem_latV bs v hc hm' hY
        rwa [twistT_twistT (matV_mul_eq_one v e1)] at h1
      · exact twistT_mem_latV bs v hc hm
    by_cases hY : Y ∈ HeckeCharacterZeroLocus.SiegelWeilU.latV bs v
    · rw [Set.indicator_of_mem hY, Set.indicator_of_mem (hiff.mpr hY)]
      simp only [Pi.one_apply]
    · rw [Set.indicator_of_notMem hY, Set.indicator_of_notMem (mt hiff.mp hY)]
  · have h3 := hprod (fun j i => ∑ k, Y k i * finPart D (a.1 k j))
    dsimp only at h3 ⊢
    rw [h3]
    refine finprod_congr fun v => ?_
    congr 1
    funext j i
    simp [HeckeCharacterZeroLocus.SiegelWeilU.projV, PositivityTheory.SiegelWeilFormula.Gen.matV, map_evalV_finPart]

end GlobalTheory.CompanionTheory.PureTwist
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FalseOfOpenParts
section
noncomputable section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.BZShell

theorem false_of_open_parts {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (d : ℕ) (hd : 0 < d) (R R' : MRep k d) (hR' : IsSmooth R'.ρ) {V V' : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [Nontrivial V]
    (X : Representation ℂ (GL (Fin d) k) V) (Y : Representation ℂ (GL (Fin d) k) V') (hX : IsSmooth X) (hY : IsSmooth Y)
    (P : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ)
    (hP : ∀ g a a', P (X g a) (Y g a') = ((dpow d (-2) g : ℂˣ) : ℂ) * P a a')
    (e : Fin d → k) (he : e ≠ 0)
    (hU : ∀ β : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ,
      (∀ g : GL (Fin d) k, (g : Matrix (Fin d) (Fin d) k).mulVec e = e → ∀ a a', β (X g a) (Y g a') =
        ((dpow d (-2) g : ℂˣ) : ℂ) * β a a') → ∃ c : ℂ, ∀ a a', β a a' = c * P a a')
    (z : GL (Fin d) k) (ϖ : k) (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k))
    (hϖ : ValuativeRel.valuation k ϖ < 1) (hϖ0 : ϖ ≠ 0) (ω ω' : ℂ) (hω : ∀ a, X z a = ω • a) (hω' : ∀ a, Y z a = ω' • a)
    (hωω : ω * ω' = ((dpow d (-2) z : ℂˣ) : ℂ))
    (B : R.V →ₗ[ℂ] R'.V →ₗ[ℂ] ℂ) (hB : ∀ p v v', B (R.ρ p v) (R'.ρ p v') = B v v')
    (hn : ∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0)
    (ι : SchF k d V →ₗ[ℂ] R.V) (hι : Function.Injective ι) (hιs : ∀ x f, ι (shiftF x f) = R.ρ (uM d x) (ι f))
    (hιg : ∀ g f, ι (actF X g f) = R.ρ (levi k d g) (ι f))
    (ι' : SchF k d V' →ₗ[ℂ] R'.V) (hιs' : ∀ x f, ι' (shiftF x f) = R'.ρ (uM d x) (ι' f))
    (hιg' : ∀ g f, ι' (actF Y g f) = R'.ρ (levi k d g) (ι' f))
    (hr : ∀ x v, R'.ρ (uM d x) v - v ∈ LinearMap.range ι') : False := by
  let c : SchF k d V →ₗ[ℂ] SchF k d V' →ₗ[ℂ] ℂ := B.compl₁₂ ι ι'
  have hcv : ∀ f f', c f f' = B (ι f) (ι' f') := fun _ _ => rfl
  have hT : ∀ x f f', c (shiftF x f) (shiftF x f') = c f f' := by
    intro x f f'
    rw [hcv, hcv, hιs, hιs']
    exact hB _ _ _
  have hG : ∀ g f f', c (actF X g f) (actF Y g f') = c f f' := by
    intro g f f'
    rw [hcv, hcv, hιg, hιg']
    exact hB _ _ _
  have hC := GlobalTheory.T.invariant_pairing_twisted_modulus d hd X Y hX hY P hP e he hU z ϖ hz hϖ hϖ0 ω ω' hω hω' hωω c hT hG
  exact GlobalTheory.T.nondegenerate_unipotent_pairing_schwartz d hd R R' hR' B (fun x v v' => hB _ v v') hn ι hι hιs ι' hιs' hr hC

theorem false_of_open_dual {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m : ℕ) (σ : IrrRep (GL (Fin (m + 1)) k)) (hc : IsCuspidal σ.ρ) (R R' : MRep k (m + 1)) (hR' : IsSmooth R'.ρ)
    (B : R.V →ₗ[ℂ] R'.V →ₗ[ℂ] ℂ) (hB : ∀ p v v', B (R.ρ p v) (R'.ρ p v') = B v v')
    (hn : ∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0)
    (ι : SchF k (m + 1) σ.V →ₗ[ℂ] R.V) (hι : Function.Injective ι) (hιs : ∀ x f, ι (shiftF x f) = R.ρ (uM (m + 1) x) (ι f))
    (hιg : ∀ g f, ι (actF ((gOf σ).tw (-1 / 2)).ρ g f) = R.ρ (levi k (m + 1) g) (ι f))
    (ι' : SchF k (m + 1) (smoothPart σ.ρ.dual) →ₗ[ℂ] R'.V) (hιs' : ∀ x f, ι' (shiftF x f) = R'.ρ (uM (m + 1) x) (ι' f))
    (hιg' : ∀ g f, ι' (actF (((gDual σ).tw (-1)).tw (-1 / 2)).ρ g f) = R'.ρ (levi k (m + 1) g) (ι' f))
    (hr : ∀ x v, R'.ρ (uM (m + 1) x) v - v ∈ LinearMap.range ι') : False := by
  obtain ⟨hci, hcc, z, ϖ, ω, hz, hϖ, hϖ0, hω0, hzσ, hzc⟩ := GlobalTheory.T.cuspidal_contragredient_central_character m σ hc
  have hsm : ∀ s : ℝ, IsSmoothChar (absPow k (s : ℂ)) := fun s => GlobalTheory.LocGL.isSmoothChar_absPow _
  have hsB' : IsSmooth ((gDual σ).tw (-1)).ρ := isSmooth_twist (isSmooth_contra _) (hsm (-1)).detChar
  let X : Representation ℂ (GL (Fin (m + 1)) k) σ.V := twist σ.ρ (dpow (m + 1) (-1 / 2))
  let Y : Representation ℂ (GL (Fin (m + 1)) k) (smoothPart σ.ρ.dual) := twist (twist (contra σ.ρ) (dpow (m + 1) (-1))) (dpow (m + 1) (-1 / 2))
  let P : σ.V →ₗ[ℂ] smoothPart σ.ρ.dual →ₗ[ℂ] ℂ := LinearMap.flip (smoothPart σ.ρ.dual).subtype
  have hadd : ∀ (s t : ℝ) (g : GL (Fin (m + 1)) k), ((dpow (m + 1) (s + t) g : ℂˣ) : ℂ) =
      ((dpow (m + 1) s g : ℂˣ) : ℂ) * ((dpow (m + 1) t g : ℂˣ) : ℂ) := by
    intro s t g
    simp only [dpow, detChar_apply, Complex.ofReal_add, absPow_add, MonoidHom.mul_apply, Units.val_mul]
  have hne : ∀ (s : ℝ) (g : GL (Fin (m + 1)) k), ((dpow (m + 1) s g : ℂˣ) : ℂ) ≠ 0 := fun s g => Units.ne_zero _
  have hXa : ∀ g a, X g a = ((dpow (m + 1) (-1 / 2) g : ℂˣ) : ℂ) • σ.ρ g a := fun g a => rfl
  have hYa : ∀ g l, Y g l = ((dpow (m + 1) (-1 / 2) g : ℂˣ) : ℂ) • ((dpow (m + 1) (-1) g : ℂˣ) : ℂ) • contra σ.ρ g l := fun g l => rfl
  have hsc : ∀ g : GL (Fin (m + 1)) k, ((dpow (m + 1) (-1 / 2) g : ℂˣ) : ℂ) * (((dpow (m + 1) (-1 / 2) g : ℂˣ) : ℂ) * ((dpow (m + 1) (-1) g : ℂˣ) : ℂ)) =
      ((dpow (m + 1) (-2) g : ℂˣ) : ℂ) := by
    intro g
    rw [← hadd, ← hadd]
    congr 3
    norm_num
  have hPinv : ∀ g a l, P (σ.ρ g a) (contra σ.ρ g l) = P a l := by
    intro g a l
    show (contra σ.ρ g l : Module.Dual ℂ σ.V) (σ.ρ g a) = (l : Module.Dual ℂ σ.V) a
    rw [contra_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hP : ∀ g a l, P (X g a) (Y g l) = ((dpow (m + 1) (-2) g : ℂˣ) : ℂ) * P a l := by
    intro g a l
    rw [hXa, hYa]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hPinv]
    rw [← hsc g]
    ring
  have hsX : IsSmooth X := isSmooth_twist σ.smooth (hsm _).detChar
  have hsY : IsSmooth Y := isSmooth_twist hsB' (hsm _).detChar
  have he : (Pi.single (Fin.last m) 1 : Fin (m + 1) → k) ≠ 0 := by
    intro h
    simpa using congrFun h (Fin.last m)
  have hU : ∀ β : σ.V →ₗ[ℂ] smoothPart σ.ρ.dual →ₗ[ℂ] ℂ,
      (∀ g : GL (Fin (m + 1)) k, (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k).mulVec (Pi.single (Fin.last m) 1) = Pi.single (Fin.last m) 1 →
        ∀ a a', β (X g a) (Y g a') = ((dpow (m + 1) (-2) g : ℂˣ) : ℂ) * β a a') →
      ∃ c : ℂ, ∀ a a', β a a' = c * P a a' := by
    intro β hβ
    refine GlobalTheory.T.cuspidal_mirabolic_invariant_pairing_scalar m σ hc β fun g hg a l => ?_
    have h := hβ g hg a l
    rw [hXa, hYa] at h
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h
    rw [← hsc g] at h
    have h2 : ((dpow (m + 1) (-1 / 2) g : ℂˣ) : ℂ) * (((dpow (m + 1) (-1 / 2) g : ℂˣ) : ℂ) * ((dpow (m + 1) (-1) g : ℂˣ) : ℂ)) ≠ 0 :=
      mul_ne_zero (hne _ _) (mul_ne_zero (hne _ _) (hne _ _))
    refine mul_left_cancel₀ h2 ?_
    rw [← h]
    ring
  have hzX : ∀ a, X z a = (((dpow (m + 1) (-1 / 2) z : ℂˣ) : ℂ) * ω) • a := by
    intro a
    rw [hXa, hzσ, smul_smul]
  have hzY : ∀ l, Y z l = (((dpow (m + 1) (-1 / 2) z : ℂˣ) : ℂ) * (((dpow (m + 1) (-1) z : ℂˣ) : ℂ) * ω⁻¹)) • l := by
    intro l
    rw [hYa, hzc, smul_smul, smul_smul, mul_assoc]
  have hωω : (((dpow (m + 1) (-1 / 2) z : ℂˣ) : ℂ) * ω) * (((dpow (m + 1) (-1 / 2) z : ℂˣ) : ℂ) * (((dpow (m + 1) (-1) z : ℂˣ) : ℂ) * ω⁻¹)) =
      ((dpow (m + 1) (-2) z : ℂˣ) : ℂ) := by
    rw [← hsc z]
    field_simp
  haveI : Nontrivial σ.V := by
    have hi := σ.irr
    by_contra hs
    rw [not_nontrivial_iff_subsingleton] at hs
    apply (bot_ne_top : (⊥ : Subrepresentation σ.ρ) ≠ ⊤)
    apply Subrepresentation.ext
    ext x
    rw [Subsingleton.elim x 0]
    exact ⟨fun _ => zero_mem _, fun _ => zero_mem _⟩
  exact false_of_open_parts (m + 1) (Nat.succ_pos m) R R' hR' X Y hsX hsY P hP _ he hU z ϖ hz hϖ hϖ0 _ _ hzX hzY hωω B hB hn ι hι hιs hιg ι' hιs' hιg' hr

theorem red_cusp_nu : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ), 0 < d →
    ∀ σ : IrrRep (GL (Fin d) k), IsCuspidal σ.ρ →
      ¬ (multiProd (GlobalTheory.Published.consecBlocks 2 d) (segTerm σ.ρ 2)).IsIrreducible := by
  intro k _ _ _ _ d hd σ hc hirr
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  obtain ⟨ψ, hψc, hψ1⟩ := GlobalTheory.LocGL.exists_continuous_addChar_ne_one k
  have hψc' : Continuous (ψ⁻¹ : AddChar k Circle) := by
    have : (⇑(ψ⁻¹ : AddChar k Circle)) = fun a => ψ (-a) := funext fun a => AddChar.inv_apply ψ a
    rw [this]
    exact hψc.comp continuous_neg
  have hψ1' : ψ⁻¹ ≠ 1 := inv_ne_one.2 hψ1
  obtain ⟨hci, hcc, -⟩ := GlobalTheory.T.cuspidal_contragredient_central_character m σ hc
  have hsm : ∀ s : ℝ, IsSmoothChar (absPow k (s : ℂ)) := fun s => GlobalTheory.LocGL.isSmoothChar_absPow _
  have hsA : IsSmooth ((gOf σ).tw 1).ρ := isSmooth_twist σ.smooth (hsm 1).detChar
  have hsB : IsSmooth (gOf σ).ρ := σ.smooth
  have hsA' : IsSmooth (gDual σ).ρ := isSmooth_contra _
  have hsB' : IsSmooth ((gDual σ).tw (-1)).ρ := isSmooth_twist (isSmooth_contra _) (hsm (-1)).detChar
  obtain ⟨B₀, hB₀, hn₀⟩ := GlobalTheory.T.invariant_pairing_segment_product m σ hc hirr
  obtain ⟨B, hB, hn⟩ := GlobalTheory.T.invariant_pairing_iterated_derivative ψ hψc hψ1 m _ _ (GlobalTheory.CompanionTheory.LeibOrd.Main.isSmooth_gcast _ (GlobalTheory.CompanionTheory.LeibOrd.Main.isSmooth_prod _ _))
    (GlobalTheory.CompanionTheory.LeibOrd.Main.isSmooth_gcast _ (GlobalTheory.CompanionTheory.LeibOrd.Main.isSmooth_prod _ _)) B₀ hB₀ hn₀
  obtain ⟨ι, hι, hιs, hιg, -⟩ := GlobalTheory.T.schwartz_functions_embed_cuspidal_derivative ψ hψc hψ1 m ((gOf σ).tw 1) (gOf σ) hsA hsB
    (GlobalTheory.LocGL.isIrreducible_twist σ.irr _) (GlobalTheory.LocGL.isCuspidal_twist hc (hsm 1))
  obtain ⟨ι', -, hιs', hιg', hr⟩ := GlobalTheory.T.schwartz_functions_embed_cuspidal_derivative ψ⁻¹ hψc' hψ1' m (gDual σ) ((gDual σ).tw (-1)) hsA' hsB' hci hcc
  exact false_of_open_dual m σ hc _ _ (GlobalTheory.CompanionTheory.LeibOrd.Main.isSmooth_iterN ψ⁻¹ m
    (isSmooth_gres (GlobalTheory.CompanionTheory.LeibOrd.Main.isSmooth_gcast _ (GlobalTheory.CompanionTheory.LeibOrd.Main.isSmooth_prod _ _))))
    B hB hn ι hι hιs hιg ι' hιs' hιg' hr

end GlobalTheory.CompanionTheory.BZShell
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralEqFundamentalDomainLatticeSumStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_eq_fundamental_domain_lattice_sum : ∀ {D : D7} {ρ p : ℕ} (m : Meas D ρ p) (P : Mx D ρ p → ℂ), Integrable P m.μ → ∫ y, P y ∂m.μ = ∫ y in m.𝓕, ∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, P (GlobalTheory.CompanionTheory.FJE.rt ξ + y) ∂m.μ := by
  first | exact @GlobalTheory.CompanionTheory.FJE.integral_fold | exact GlobalTheory.CompanionTheory.FJE.integral_fold | (intros; apply GlobalTheory.CompanionTheory.FJE.integral_fold <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubSegmentProductStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_sub_segment_product : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hZ : GlobalTheory.Published.SegmentRepresentation) (Δ : Segment k) {N : ℕ} (hd : ∑ a, (dec Δ a).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth τ) (hi : τ.IsIrreducible) (f : τ.IntertwiningMap (prodIrr (dec Δ) hd)) (hf : Function.Injective f), IsLSeg Δ τ := by
  first | exact @GlobalTheory.CompanionTheory.SegUniq.isLSeg_of_dec | exact GlobalTheory.CompanionTheory.SegUniq.isLSeg_of_dec | (intros; apply GlobalTheory.CompanionTheory.SegUniq.isLSeg_of_dec <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KFiniteVectorsDenseStatement
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.K_finite_vectors_dense : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (H : Submodule ℂ (L2 (latticeGL E a) μ)), IsSubrep (R (latticeGL E a) μ) H → H ≤ (Submodule.span ℂ {F | F ∈ H ∧ IsKFinL2 μ F}).topologicalClosure := by
  first | exact @GlobalTheory.CompanionTheory.DenseKFin.le_closure_span_K_finite | exact GlobalTheory.CompanionTheory.DenseKFin.le_closure_span_K_finite | (intros; apply GlobalTheory.CompanionTheory.DenseKFin.le_closure_span_K_finite <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeTransformInvarianceStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_transform_invariance : ∀ {D : D7} {ρ p : ℕ} (m : Meas D ρ p) (T : (Mx D ρ p × Mx D ρ p) ≃ₜ+ (Mx D ρ p × Mx D ρ p)), (∀ ξ₁ ξ₂ : Matrix (Fin ρ) (Fin p) D.host.E, ∃ ξ₁' ξ₂' : Matrix (Fin ρ) (Fin p) D.host.E, T (GlobalTheory.CompanionTheory.FJE.rt ξ₁, GlobalTheory.CompanionTheory.FJE.rt ξ₂) = (GlobalTheory.CompanionTheory.FJE.rt ξ₁', GlobalTheory.CompanionTheory.FJE.rt ξ₂')) → (∀ ξ₁ ξ₂ : Matrix (Fin ρ) (Fin p) D.host.E, ∃ ξ₁' ξ₂' : Matrix (Fin ρ) (Fin p) D.host.E, T.symm (GlobalTheory.CompanionTheory.FJE.rt ξ₁, GlobalTheory.CompanionTheory.FJE.rt ξ₂) = (GlobalTheory.CompanionTheory.FJE.rt ξ₁', GlobalTheory.CompanionTheory.FJE.rt ξ₂')) → ∀ A : Mx D ρ p × Mx D ρ p → ℂ, (∀ (ξ₁ ξ₂ : Matrix (Fin ρ) (Fin p) D.host.E) v, A (v + (GlobalTheory.CompanionTheory.FJE.rt ξ₁, GlobalTheory.CompanionTheory.FJE.rt ξ₂)) = A v) → ∫ v in m.𝓕 ×ˢ m.𝓕, A (T v) ∂(m.μ.prod m.μ) = ∫ v in m.𝓕 ×ˢ m.𝓕, A v ∂(m.μ.prod m.μ) := by
  first | exact @GlobalTheory.CompanionTheory.FJE.TransportInt.transport_int | exact GlobalTheory.CompanionTheory.FJE.TransportInt.transport_int | (intros; apply GlobalTheory.CompanionTheory.FJE.TransportInt.transport_int <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantFourierCoefficientStatement
section
open PositivityTheory.Rg.Rsw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_constant_fourier_coefficient : MapsExist → PositivityTheory.PfSWUS.FourierZero → PcFc := by
  first | exact @GlobalTheory.CompanionTheory.PcFc.target | exact GlobalTheory.CompanionTheory.PcFc.target | (intros; apply GlobalTheory.CompanionTheory.PcFc.target <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalPointsHeisenbergGroupStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_points_heisenberg_group : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn), (∀ ξ : Matrix (Fin ρ) (Fin p) D.host.E, M.sh (GlobalTheory.CompanionTheory.FJE.rt ξ) ∈ GF D n) ∧ (∀ ξ : Matrix (Fin ρ) (Fin p) D.host.E, M.nzx 0 (GlobalTheory.CompanionTheory.FJE.rt ξ) ∈ GF D n) ∧ ∀ z ∈ ratHerm D ρ, M.nzx z 0 ∈ GF D n := by
  first | exact @GlobalTheory.CompanionTheory.FJE.rat_maps_mem_GF | exact GlobalTheory.CompanionTheory.FJE.rat_maps_mem_GF | (intros; apply GlobalTheory.CompanionTheory.FJE.rat_maps_mem_GF <;> assumption)
end

