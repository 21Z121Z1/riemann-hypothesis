import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0239
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0236
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0240
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPrimeHeckeTransferCompositeLift
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteClass
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0225
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0216
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0778
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0070
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0001
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0197
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0223
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0215
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChiIdemMulLvlIdemBaseNeZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0170
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0053
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0228
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0138
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimPartsAtIffBadAndOff

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalComponentEigenvectorAtSplitPlaceIsotyStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localComponent_eigenvector_at_splitPlace_isotypic : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S → ∀ (s : SplitPlace L) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS S s σ → ∀ c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L, Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → ∀ (K : Subgroup (GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)))) (θ : K →* ℂˣ), (∀ g ∈ K, g ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring) → IsOpen (θ.ker : Set K) → ∀ f ∈ NG.isoTyp a.ρ S, f ≠ 0 → (∀ κ, TrivOutside {s.v} κ → ∀ h : s.loc n κ ∈ K, NG.rt L n κ f = ((θ ⟨s.loc n κ, h⟩ : ℂˣ) : ℂ) • f) → ∃ u : σ.V, u ≠ 0 ∧ ∀ g (h : g ∈ K), σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom g) u = ((θ ⟨g, h⟩ : ℂˣ) : ℂ) • u := by
  first | exact @GlobalTheory.LocVec.main | exact GlobalTheory.LocVec.main | (intros; apply GlobalTheory.LocVec.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSatakeParameterAtInertPlaceOfSphericalStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_satakeParameter_at_inertPlace_of_spherical : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.AutRep L n) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → π.SphAt v → ∀ Dv : InertDatum L n v w, ∃ α, NG.SatAt π Dv α := by
  first | exact @GlobalTheory.SatExists.exists_satAt | exact GlobalTheory.SatExists.exists_satAt | (intros; apply GlobalTheory.SatExists.exists_satAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPrimeHeckeTransferCompositeLiftStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_splitPrime_heckeTransfer_compositeLift : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Chain.LiftInteg D → Core R F → SchurAll R → ∀ t (P : A.ok t), ∃ z : ℕ → ℕ → ℂ, (∀ k, k ≤ D.sp.X'.rank → MatchE R t (R.pl P) (Finsupp.single (splitLab D.sp.X'.rank k) 1) (splitC (Yc D 0).rank (z k))) ∧ ∀ a : ℕ → ℂ, Formalism.L2.Col.heckePolyOf D.sp.X'.rank (A.q P) (fun k => ∑ j ∈ Finset.range ((Yc D 0).rank + 1), z k j * a j) = (Formalism.L2.Col.heckePolyOf (Yc D 0).rank (A.q P) a).comp (C ((A.q P : ℂ) ^ (D.R.m / 2 * D.R.t)) * X) * ((A.fam.R t).blockProd P).map D.what₂.embLL := by
  first | exact @GlobalTheory.Hk3.SplitChain.exists_transfer | exact GlobalTheory.Hk3.SplitChain.exists_transfer | (intros; apply GlobalTheory.Hk3.SplitChain.exists_transfer <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTrueReadingWithLawsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_true_reading_with_laws : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), (∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i))) → ∃ S : Reading P.T, IsTrue P S ∧ Laws S ∧ SuppLaws S := by
  first | exact @GlobalTheory.TrueReading.exists_true_reading | exact GlobalTheory.TrueReading.exists_true_reading | (intros; apply GlobalTheory.TrueReading.exists_true_reading <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteAdelicGLInductionOverPlaces
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open TensorProduct

namespace GlobalTheory.PlaceInd

open GlobalTheory.IdemSplit GlobalTheory.CongSplit GlobalTheory.InertUmax

variable (L : Type) [Field L] [NumberField L] [IsCMField L]

def epsOff (T : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))) : AL L :=
  ∏ v ∈ T, (1 - idemAt L v)

theorem compAt_epsOff_of_mem {T : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))}
    {w : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} (hw : w ∈ T) :
    compAt L w (epsOff L T) = 0 := by
  rw [epsOff, map_prod]
  exact Finset.prod_eq_zero hw (by rw [map_sub, map_one, compAt_idemAt_self, sub_self])

theorem epsOff_mem (T : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))) :
    epsOff L T ∈ ALint L :=
  Subring.prod_mem _ fun v _ => Subring.sub_mem _ (one_mem _) (idemAt_mem L v)

theorem epsOff_insert [DecidableEq (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))]
    {T : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))}
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} (hv : v ∉ T) :
    epsOff L (insert v T) = (1 - idemAt L v) * epsOff L T := by
  rw [epsOff, Finset.prod_insert hv, epsOff]

theorem epsOff_mono {T T' : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} (h : T ⊆ T') :
    ∃ c ∈ ALint L, epsOff L T' = c * epsOff L T := by
  classical
  exact ⟨epsOff L (T' \ T), epsOff_mem L _, (Finset.prod_sdiff h).symm⟩

theorem exists_epsOff_mul_mem (z : AL L) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield L))), epsOff L T * z ∈ ALint L := by
  classical
  obtain ⟨S, Y, hY, h⟩ := GlobalTheory.FormInner.exists_int_off z
  refine ⟨S, ?_⟩
  have e : epsOff L S * z = epsOff L S * Y := by
    apply sub_eq_zero.1
    apply eq_zero_of_compAt
    intro w
    rw [map_sub, map_mul, map_mul]
    by_cases hw : w ∈ S
    · rw [compAt_epsOff_of_mem L hw]; ring
    · rw [h w hw]; ring
  rw [e]
  exact Subring.mul_mem _ (epsOff_mem L S) hY

theorem gaFold_split {n : ℕ} (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (g : GAf L n)
    (he : idemAt L v * idemAt L v = idemAt L v) (hσ : conjAL L (idemAt L v) = idemAt L v)
    (he' : (1 - idemAt L v) * (1 - idemAt L v) = 1 - idemAt L v)
    (hσ' : conjAL L (1 - idemAt L v) = 1 - idemAt L v) :
    g = gaFold he hσ g * gaFold he' hσ' g := by
  apply Subtype.ext; apply Units.ext
  show (g.1 : Matrix (Fin n) (Fin n) (AL L)) = fold (idemAt L v) _ * fold (1 - idemAt L v) _
  rw [fold_mul_fold he, ← add_smul, add_sub_cancel, one_smul]

theorem ind_epsOff (n N : ℕ) (p : GAf L n → Prop) (hC : ∀ κ, NG.Cong L n N κ → p κ)
    (hstep : ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (x y : GAf L n),
      TrivOutside {v} x → TrivOutside {v}ᶜ y → p y → p (x * y))
    (T : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))) :
    ∀ g : GAf L n, (∀ i j, ∃ y ∈ ALint L, epsOff L T * ((g.1 : Matrix (Fin n) (Fin n) (AL L)) i j -
      (1 : Matrix (Fin n) (Fin n) (AL L)) i j) = (N : AL L) * y) → p g := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro g hg
    have hg' : ∀ i j, ∃ y ∈ ALint L, (g.1 : Matrix (Fin n) (Fin n) (AL L)) i j -
        (1 : Matrix (Fin n) (Fin n) (AL L)) i j = (N : AL L) * y := by
      intro i j
      obtain ⟨y, hy, e⟩ := hg i j
      rw [epsOff, Finset.prod_empty, one_mul] at e
      exact ⟨y, hy, e⟩
    apply hC
    refine ⟨fun i j => ?_, hg'⟩
    obtain ⟨y, hy, e⟩ := hg' i j
    have h1 : (g.1 : Matrix (Fin n) (Fin n) (AL L)) i j =
        (1 : Matrix (Fin n) (Fin n) (AL L)) i j + (N : AL L) * y := by rw [← e]; ring
    rw [h1]
    exact Subring.add_mem _ (one_apply_mem L i j) (Subring.mul_mem _ (natCast_mem _ _) hy)
  | @insert v T hv ih =>
    intro g hg
    have he : idemAt L v * idemAt L v = idemAt L v := idemAt_mul_self L v
    have he' : (1 - idemAt L v) * (1 - idemAt L v) = 1 - idemAt L v := by
      rw [sub_mul, one_mul, mul_sub, mul_one, he, sub_self, sub_zero]
    have hσ : conjAL L (idemAt L v) = idemAt L v := conjAL_idemAt L v
    have hσ' : conjAL L (1 - idemAt L v) = 1 - idemAt L v := by rw [map_sub, map_one, hσ]
    have hx : TrivOutside {v} (gaFold he hσ g) := by
      intro w hw
      have hw' : w ≠ v := by simpa using hw
      ext i j
      rw [Matrix.map_apply, gaFold_val, fold_apply, map_add, map_mul, map_mul, map_sub, map_one,
        compAt_idemAt_ne L v hw', compAt_one_apply]
      simp
    have hy : TrivOutside {v}ᶜ (gaFold he' hσ' g) := by
      intro w hw
      have hw' : w = v := by simpa using hw
      rw [hw']
      ext i j
      simp only [Matrix.map_apply, gaFold_val, fold_apply, map_add, map_mul, map_sub, map_one,
        compAt_idemAt_self, compAt_one_apply]
      simp
    have hp : p (gaFold he' hσ' g) := by
      apply ih
      intro i j
      obtain ⟨y, hy, eq⟩ := hg i j
      refine ⟨y, hy, ?_⟩
      rw [epsOff_insert L hv] at eq
      rw [gaFold_val, fold_apply]
      linear_combination eq
    have := hstep v _ _ hx hy hp
    rwa [← gaFold_split L v g he hσ he' hσ'] at this

theorem induction_places : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (N : ℕ), 0 < N → ∀ p : GAf L n → Prop, (∀ κ, NG.Cong L n N κ → p κ) → (∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (x y : GAf L n), TrivOutside {v} x → TrivOutside {v}ᶜ y → p y → p (x * y)) → ∀ g, p g := by
  intro L _ _ _ n N hN p hC hstep g
  classical
  have hN' : (N : L) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  obtain ⟨u, hu⟩ : ∃ u : AL L, (N : AL L) * u = 1 :=
    ⟨algebraMap L (AL L) (N : L)⁻¹, by
      rw [← map_natCast (algebraMap L (AL L)), ← map_mul, mul_inv_cancel₀ hN', map_one]⟩
  have hT : ∀ q : Fin n × Fin n, ∃ T : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield L))),
      epsOff L T * (u * ((g.1 : Matrix (Fin n) (Fin n) (AL L)) q.1 q.2 -
        (1 : Matrix (Fin n) (Fin n) (AL L)) q.1 q.2)) ∈ ALint L :=
    fun q => exists_epsOff_mul_mem L _
  choose T hT using hT
  refine ind_epsOff L n N p hC hstep (Finset.univ.biUnion T) g fun i j => ?_
  obtain ⟨c, hc, e⟩ := epsOff_mono L (Finset.subset_biUnion_of_mem T (Finset.mem_univ (i, j)))
  refine ⟨c * (epsOff L (T (i, j)) * (u * ((g.1 : Matrix (Fin n) (Fin n) (AL L)) i j -
    (1 : Matrix (Fin n) (Fin n) (AL L)) i j))), Subring.mul_mem _ hc (hT (i, j)), ?_⟩
  rw [e]
  linear_combination (-(c * epsOff L (T (i, j)) * ((g.1 : Matrix (Fin n) (Fin n) (AL L)) i j -
    (1 : Matrix (Fin n) (Fin n) (AL L)) i j))) * hu

end GlobalTheory.PlaceInd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineParameterTwistPotentiallySemistable
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.TwistParamAbove

theorem wdPst_twist_one_field : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (ι : Om l ≃+* ℂ) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) {L : FinExt l} {a : ℕ} (s : ↥(Dec (F := E) A) →* GL (Fin a) ↥L.1) (m : ↥(Dec (F := E) A) →* GL (Fin 1) ↥L.1), IsPst P (Bw.repE L s) → IsPst P (Bw.repE L m) → IsPst P (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) → wdPst P ι Bw h hj (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) = (wdPst P ι Bw h hj (Bw.repE L s)).lpChar (wdPst P ι Bw h hj (Bw.repE L m)) := by
  intro l _ P AI hT ι E Ω _ _ _ _ _ A w O _ _ _ Bw h hj L a s m hs hm ht
  haveI := hs.finite
  haveI := hm.finite
  haveI := ht.finite
  obtain ⟨e, he1, he2⟩ := GlobalTheory.T.dpstLetter_twist_tensor_equiv P AI hT ι Bw h hj s m hs hm ht
  have f1 := isFrobSS_wdRep P ι Bw h hj (Bw.repE L s)
  have f2 := isFrobSS_wdRep P ι Bw h hj (Bw.repE L m)
  have f3 := isFrobSS_wdRep P ι Bw h hj (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m)))
  have f12 := GlobalTheory.T.tensor_frobeniusSemisimplification f1 f2
  have hI := IsFrobSS.iso f12 f3 e (fun g v => he1 g v) (fun v => he2 v)
  rw [wdPst_of_isPst ι Bw h hj hs, wdPst_of_isPst ι Bw h hj hm, wdPst_of_isPst ι Bw h hj ht, WD.lpChar_mk]
  exact (WD.sound hI).symm

theorem wdAt_twist : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (ι : Loc.Om l ≃+* ℂ) (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver (F := E) A w) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : GlobalTheory.Pst.Induces Bw) (a : ℕ) (r : ↥(Dec (F := E) A) →* GL (Fin a) (Loc.Om l)) (c : ↥(Dec (F := E) A) →* GL (Fin 1) (Loc.Om l)), Continuous (fun g => ((r g : GL (Fin a) (Loc.Om l)) : Matrix (Fin a) (Fin a) (Loc.Om l))) → Continuous (fun g => ((c g : GL (Fin 1) (Loc.Om l)) : Matrix (Fin 1) (Fin 1) (Loc.Om l))) → GlobalTheory.Pst.IsPstAt P Bw r → GlobalTheory.Pst.IsPstAt P Bw c → GlobalTheory.Pst.IsPstAt P Bw (Formalism.MainNotions.SumRepresentations.At.twGL r (Matrix.GeneralLinearGroup.det.comp c)) → GlobalTheory.Pst.wdAt P ι Bw h hj (Formalism.MainNotions.SumRepresentations.At.twGL r (Matrix.GeneralLinearGroup.det.comp c)) = (GlobalTheory.Pst.wdAt P ι Bw h hj r).lpChar (GlobalTheory.Pst.wdAt P ι Bw h hj c) := by
  intro l _ P AI hT ι E Ω _ _ _ _ _ A w h O _ _ _ Bw hj a r c _ _ hr hc ht
  obtain ⟨L₁, r₁, hm₁, hp₁, e₁⟩ := wdAt_of_isPstAt ι Bw h hj hr
  obtain ⟨L₂, c₂, hm₂, hp₂, e₂⟩ := wdAt_of_isPstAt ι Bw h hj hc
  obtain ⟨L₃, t₃, hm₃, hp₃, e₃⟩ := wdAt_of_isPstAt ι Bw h hj ht
  have l₁ : L₁.1 ≤ (supExt (supExt L₁ L₂) L₃).1 := le_sup_left.trans le_sup_left
  have l₂ : L₂.1 ≤ (supExt (supExt L₁ L₂) L₃).1 := le_sup_right.trans le_sup_left
  have l₃ : L₃.1 ≤ (supExt (supExt L₁ L₂) L₃).1 := le_sup_right
  have hmt := isModel_twist (hm₁.enlarge l₁) (hm₂.enlarge l₂)
  have hu := IsModel.unique Bw (r := Formalism.MainNotions.SumRepresentations.At.twGL r (Matrix.GeneralLinearGroup.det.comp c)) (hm₃.enlarge l₃) hmt
  have q₃ := GlobalTheory.PstExt.isPst_enlarge P Bw l₃ t₃ hp₃
  rw [hu] at q₃
  rw [e₁, e₂, e₃, ← GlobalTheory.T.potSemistableParameter_coefficientField_enlarge P ι Bw h hj l₃ t₃ hp₃, hu, ← GlobalTheory.T.potSemistableParameter_coefficientField_enlarge P ι Bw h hj l₁ r₁ hp₁, ← GlobalTheory.T.potSemistableParameter_coefficientField_enlarge P ι Bw h hj l₂ c₂ hp₂]
  exact wdPst_twist_one_field P AI hT ι Bw h hj _ _ (GlobalTheory.PstExt.isPst_enlarge P Bw l₁ r₁ hp₁)
    (GlobalTheory.PstExt.isPst_enlarge P Bw l₂ c₂ hp₂) q₃

end GlobalTheory.TwistParamAbove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GenericLevelCharacterAlternatingSignConjInv
section
noncomputable section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Links NumberField Matrix Formalism.DivisionValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GoodGenericInv

theorem typeSum_inv_eq {K G : Type} [Field K] [Group G] (P : Subgroup G) [Fintype P] (ψ : P →* Kˣ) (χ : G → K)
    (hχ : ∀ g h, χ (g * h * g⁻¹) = χ h) (t : G) (ht : ∀ h ∈ P, t * h * t⁻¹ ∈ P)
    (hψ : ∀ (h : G) (hh : h ∈ P), ψ ⟨t * h * t⁻¹, ht h hh⟩ = (ψ ⟨h, hh⟩)⁻¹) :
    ∑ h : P, χ (h : G) * ((((ψ⁻¹) h)⁻¹ : Kˣ) : K) = ∑ h : P, χ (h : G) * (((ψ h)⁻¹ : Kˣ) : K) := by
  have hinj : Function.Injective (fun h : P => (⟨t * h * t⁻¹, ht h h.2⟩ : P)) := by
    intro a b e
    apply Subtype.ext
    have := congrArg Subtype.val e
    simpa using this
  have hbij : Function.Bijective (fun h : P => (⟨t * h * t⁻¹, ht h h.2⟩ : P)) :=
    (Finite.injective_iff_bijective).1 hinj
  rw [← (Equiv.ofBijective _ hbij).sum_comp]
  refine Finset.sum_congr rfl fun h _ => ?_
  simp only [Equiv.ofBijective_apply, MonoidHom.inv_apply, inv_inv]
  rw [hχ, hψ h h.2]

def sgnDiag (κ : Type) [CommRing κ] (r : ℕ) : GL (Fin r) κ where
  val := Matrix.diagonal fun i => (-1) ^ i.val
  inv := Matrix.diagonal fun i => (-1) ^ i.val
  val_inv := by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; rw [← pow_add, ← two_mul, pow_mul]; simp
  inv_val := by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; rw [← pow_add, ← two_mul, pow_mul]; simp

theorem sgnDiag_conj_apply {κ : Type} [CommRing κ] {r : ℕ} (u : GL (Fin r) κ) (i j : Fin r) :
    ((sgnDiag κ r * u * (sgnDiag κ r)⁻¹ : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) i j =
      (-1) ^ i.val * (-1) ^ j.val * (u : Matrix (Fin r) (Fin r) κ) i j := by
  show (Matrix.diagonal (fun i : Fin r => ((-1 : κ)) ^ i.val) * (u : Matrix (Fin r) (Fin r) κ) *
    Matrix.diagonal (fun i : Fin r => ((-1 : κ)) ^ i.val)) i j = _
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  ring

end GlobalTheory.GoodGenericInv

namespace GlobalTheory.GoodGenericInv

variable {κ : Type} [CommRing κ] {r : ℕ}

theorem sgnDiag_conj_mem_unip {u : GL (Fin r) κ} (hu : u ∈ unip κ r) :
    sgnDiag κ r * u * (sgnDiag κ r)⁻¹ ∈ unip κ r := by
  refine ⟨?_, fun i => ?_⟩
  · intro i j h
    rw [sgnDiag_conj_apply, unip_lower hu (show j < i from h), mul_zero]
  · rw [sgnDiag_conj_apply, unip_diag hu i, ← pow_add, ← two_mul, pow_mul]
    simp

theorem edgeSum_sup_conj (u : GL (Fin r) κ) :
    edgeSum supEdge (sgnDiag κ r * u * (sgnDiag κ r)⁻¹) = - edgeSum supEdge u := by
  unfold edgeSum
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · rw [sgnDiag_conj_apply]
    unfold supEdge at h
    have hs : ((-1 : κ)) ^ (i : ℕ) * (-1) ^ (i : ℕ) = 1 := by rw [← mul_pow]; simp
    rw [h, pow_succ]
    linear_combination (-(u : Matrix (Fin r) (Fin r) κ) i j) * hs
  · simp

end GlobalTheory.GoodGenericInv

namespace GlobalTheory.GoodGenericInv

variable {E : Type} [Field E] [NumberField E] {Pg : Finset (Pl E)} {r : ℕ}

def alternatingSignDiagonalLevelGroup (Pg : Finset (Pl E)) (r : ℕ) : G0 Pg r := fun PP => sgnDiag (kP PP.1) r

theorem alternatingSignDiagonal_conj_mem_genericLevel (ψ : ∀ PP : Pl E, AddChar (kP PP) ℂ) {x : G0 Pg r} (hx : x ∈ (P0 Pg r ψ).H) :
    alternatingSignDiagonalLevelGroup Pg r * x * (alternatingSignDiagonalLevelGroup Pg r)⁻¹ ∈ (P0 Pg r ψ).H := by
  intro PP _
  exact sgnDiag_conj_mem_unip (hx PP (Set.mem_univ _))

theorem genericLevelCharacter_alternatingSign_conj_inv (ψ : ∀ PP : Pl E, AddChar (kP PP) ℂ) {x : G0 Pg r} (hx : x ∈ (P0 Pg r ψ).H) :
    (P0 Pg r ψ).chi ⟨alternatingSignDiagonalLevelGroup Pg r * x * (alternatingSignDiagonalLevelGroup Pg r)⁻¹, alternatingSignDiagonal_conj_mem_genericLevel ψ hx⟩ = ((P0 Pg r ψ).chi ⟨x, hx⟩)⁻¹ := by
  show (∏ PP : ↥Pg, (addCharHom (ψ PP.1) (supHom (kP PP.1) r)).comp (LevelP.prj (fun PP => unip (kP PP.1) r) PP))
      ⟨alternatingSignDiagonalLevelGroup Pg r * x * (alternatingSignDiagonalLevelGroup Pg r)⁻¹, alternatingSignDiagonal_conj_mem_genericLevel ψ hx⟩ =
    ((∏ PP : ↥Pg, (addCharHom (ψ PP.1) (supHom (kP PP.1) r)).comp (LevelP.prj (fun PP => unip (kP PP.1) r) PP)) ⟨x, hx⟩)⁻¹
  rw [MonoidHom.finset_prod_apply, MonoidHom.finset_prod_apply, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun PP _ => ?_
  apply Units.ext
  simp only [MonoidHom.comp_apply, addCharHom, MonoidHom.coe_toHomUnits, Units.val_inv_eq_inv_val]
  show ψ PP.1 (Multiplicative.toAdd (Multiplicative.ofAdd (edgeSum supEdge (sgnDiag (kP PP.1) r * x PP * (sgnDiag (kP PP.1) r)⁻¹)))) =
    (ψ PP.1 (Multiplicative.toAdd (Multiplicative.ofAdd (edgeSum supEdge (x PP)))))⁻¹
  rw [toAdd_ofAdd, toAdd_ofAdd, edgeSum_sup_conj, AddChar.map_neg_eq_inv]

end GlobalTheory.GoodGenericInv

namespace GlobalTheory.GoodGenericInv

theorem level_character_eq_of_eq {E : Type} [Field E] [NumberField E] {Pg : Finset (Pl E)} {r : ℕ} {LL : Type} [CommRing LL]
    {L L' : LevelP Pg r LL} (h : L = L') (x : G0 Pg r) (hx : x ∈ L.H) (hx' : x ∈ L'.H) :
    L.chi ⟨x, hx⟩ = L'.chi ⟨x, hx'⟩ := by
  subst h; rfl

end GlobalTheory.GoodGenericInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IrreducibleSplitExactTwistCountProduct
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.BlockSplitProd

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem unrChar_mul (α β : ℂˣ) : unrChar k (α * β) = unrChar k α * unrChar k β := by
  refine MonoidHom.ext fun x => ?_
  simp [unrChar_apply, mul_zpow]

theorem twist_detRep (n : Type) [Fintype n] [DecidableEq n] (ψ φ : kˣ →* ℂˣ) :
    twist (detRep n ψ) (detChar n φ) = detRep n (ψ * φ) := by
  refine MonoidHom.ext fun g => LinearMap.ext fun x => ?_
  simp [detRep, ofChar_apply, twist_apply, mul_comm, mul_left_comm, mul_assoc]

theorem nonempty_equiv_of_cast {n m : ℕ} (h : n = m) (x : Irr k n) (ψ : kˣ →* ℂˣ)
    (e : Nonempty ((h ▸ x : Irr k m).π.Equiv (detRep (Fin m) ψ))) :
    Nonempty (x.π.Equiv (detRep (Fin n) ψ)) := by
  subst h; exact e

theorem eq_one_of_inSupport {m : ℕ} (τ : Irr k m) (hc : IsCuspidal τ.π) {ψ : kˣ →* ℂˣ}
    (h : InSupport τ.π ψ) : m = 1 ∧ Nonempty (τ.π.Equiv (detRep (Fin m) ψ)) := by
  rcases m with _ | _ | m
  · exact absurd h (Model.not_inSupport_zero _ _)
  · obtain ⟨ω, hω, ⟨φ⟩⟩ := RankLeOne.exists_equiv_detRep k (Fin 1) _ τ.π τ.smooth τ.irr
    have h1 : InSupport (detRep (Fin 1) ω) ψ :=
      JacquetExact.inSupport_of_isSubquotient k _ _ _ τ.π _ ψ ((isSmooth_ofChar_iff _).2 hω.detChar)
        (IsSubquotient.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective) h
    obtain rfl := (Model.inSupport_one_iff ω ψ).1 h1
    exact ⟨rfl, ⟨φ⟩⟩
  · exact absurd h (Model.not_inSupport_of_isCuspidal hc ψ)

theorem exists_eq_of_inSupport (hG : GlobalTheory.Published.GeometricLemma) {n s : ℕ} {V : Type} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a))
    (ψ : kˣ →* ℂˣ) (hc : IsCuspSupport π d (fun a => (σ a).π)) (h : InSupport π ψ) :
    ∃ a, d a = 1 ∧ Nonempty ((σ a).π.Equiv (detRep (Fin (d a)) ψ)) := by
  obtain ⟨-, hσ, e, hsub⟩ := hc
  have h1 := JacquetExact.inSupport_of_isSubquotient k _ _ _ π _ ψ (isSmooth_parInd _ _) hsub h
  obtain ⟨a, ha⟩ := ProdSupport.exists_inSupport_of_multiProd hG k (Fin s) (fun a => Fin (d a)) (Fin n) e _
    (fun a => (σ a).π) ψ (fun a => (σ a).smooth) (fun a => (σ a).irr) h1
  exact ⟨a, eq_one_of_inSupport (σ a) (hσ a).2.2 ha⟩

theorem reorder : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma →
    GlobalTheory.Published.UnlinkedProductIrreducible →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (r t s : ℕ) (π : Irr k (r + t)) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)) (S : Finset (Fin s)),
      IsCuspSupport π.π d (fun a => (σ a).π) → (∀ b ∈ S, d b = 1) →
      (∀ a b, a ∉ S → b ∈ S → ∀ (h : d a = d b) (α : ℂˣ),
        ¬ Nonempty ((h ▸ σ a : Irr k (d b)).π.Equiv (twist (σ b).π (detChar (Fin (d b)) (unrChar k α))))) →
      ∑ a ∈ Sᶜ, d a = r → ∑ a ∈ S, d a = t →
      ∃ (π₁ : Irr k r) (π₂ : Irr k t) (s₁ s₂ : ℕ) (ι₁ : Fin s₁ → Fin s) (ι₂ : Fin s₂ → Fin s),
        (∀ a, ι₁ a ∉ S) ∧ (∀ b, ι₂ b ∈ S) ∧
        IsCuspSupport π₁.π (fun a => d (ι₁ a)) (fun a => (σ (ι₁ a)).π) ∧
        IsCuspSupport π₂.π (fun b => d (ι₂ b)) (fun b => (σ (ι₂ b)).π) ∧
        IsSubquotient π.π (prod₂ π₁.π π₂.π) := by
  intro hB hG hU k _ _ _ _ r t s π d σ S hc hS1 hlink hr ht
  have hσ := hc.2.1
  obtain ⟨s₁, s₂, ι₁, ι₂, e₁, e₂, V₁, V₂, _, _, _, _, ρ₁, ρ₂, m1, m2, sm1, sm2, ⟨φ₁⟩, ⟨φ₂⟩, hsub⟩ :=
    GlobalTheory.T.isSubquotient_prod_reordered_cuspSupport hB hG hU k r t s π d σ S hc hS1 hlink hr ht
  obtain ⟨π₁, π₂, h1, h2, h3⟩ := GlobalTheory.T.irreducibleSubquotient_parabolicProductTwo_finiteLength hB k r t V₁ V₂ ρ₁ ρ₂ π sm1 sm2
    ((GlobalTheory.T.parabolicInductionTensorProduct_hasFiniteLength hB k s₁ r (fun a => d (ι₁ a)) (fun a => σ (ι₁ a)) e₁).of_equiv φ₁.symm)
    ((GlobalTheory.T.parabolicInductionTensorProduct_hasFiniteLength hB k s₂ t (fun b => d (ι₂ b)) (fun b => σ (ι₂ b)) e₂).of_equiv φ₂.symm) hsub
  exact ⟨π₁, π₂, s₁, s₂, ι₁, ι₂, m1, m2,
    ⟨π₁.irr, fun a => hσ (ι₁ a), e₁, h1.trans (IsSubquotient.of_injective φ₁.toIntertwiningMap φ₁.toLinearEquiv.injective)⟩,
    ⟨π₂.irr, fun b => hσ (ι₂ b), e₂, h2.trans (IsSubquotient.of_injective φ₂.toIntertwiningMap φ₂.toLinearEquiv.injective)⟩, h3⟩

end GlobalTheory.BlockSplitProd

open GlobalTheory.BlockSplitProd in
theorem GlobalTheory.BlockSplitProd.main : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.UnlinkedProductIrreducible → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ) (π : Irr k (r + t)) (s : ℕ) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)), IsSmoothChar χ → IsCuspSupport π.π d (fun a => (σ a).π) → Set.ncard {a | d a = 1 ∧ ∃ α : ℂˣ, Nonempty ((σ a).π.Equiv (detRep (Fin (d a)) (χ * unrChar k α)))} = t → ∃ (π₁ : Irr k r) (π₂ : Irr k t), Nonempty (π.π.Equiv (prod₂ π₁.π π₂.π)) ∧ ∀ α : ℂˣ, ¬ InSupport π₁.π (χ * unrChar k α) := by
  intro hB hG hU k _ _ _ _ r t χ π s d σ _ hc hcard
  classical
  let S : Finset (Fin s) := Finset.univ.filter fun a =>
    d a = 1 ∧ ∃ α : ℂˣ, Nonempty ((σ a).π.Equiv (detRep (Fin (d a)) (χ * unrChar k α)))
  have hS : S.card = t := by
    rw [← hcard, ← Set.ncard_coe_finset]
    congr 1
    ext a
    simp [S]
  have hS1 : ∀ b ∈ S, d b = 1 := fun b hb => (Finset.mem_filter.1 hb).2.1
  have htot : ∑ a, d a = r + t := by
    obtain ⟨e, -⟩ := hc.2.2
    simpa using Fintype.card_congr e
  have ht : ∑ a ∈ S, d a = t := by
    rw [Finset.sum_congr rfl hS1]
    simp [hS]
  have hr : ∑ a ∈ Sᶜ, d a = r := by
    have := Finset.sum_add_sum_compl S d
    omega
  have hlink : ∀ a b, a ∉ S → b ∈ S → ∀ (h : d a = d b) (α : ℂˣ),
      ¬ Nonempty ((h ▸ σ a : Irr k (d b)).π.Equiv (twist (σ b).π (detChar (Fin (d b)) (unrChar k α)))) := by
    intro a b ha hb h α ⟨φ⟩
    obtain ⟨hb1, β, ⟨ψ⟩⟩ := (Finset.mem_filter.1 hb).2
    have e1 : twist (detRep (Fin (d b)) (χ * unrChar k β)) (detChar (Fin (d b)) (unrChar k α)) =
        detRep (Fin (d b)) (χ * unrChar k (β * α)) := by
      rw [twist_detRep, unrChar_mul, mul_assoc]
    have ψ' := LocGL.twistEquiv ψ (detChar (Fin (d b)) (unrChar k α))
    rw [e1] at ψ'
    exact ha (Finset.mem_filter.2 ⟨Finset.mem_univ _, h.trans hb1, β * α,
      nonempty_equiv_of_cast h (σ a) _ ⟨φ.trans ψ'⟩⟩)
  obtain ⟨π₁, π₂, s₁, s₂, ι₁, ι₂, m1, m2, hc1, hc2, hsub⟩ :=
    reorder hB hG hU k r t s π d σ S hc hS1 hlink hr ht
  have hirr := hU k r t s₁ s₂ π₁ π₂ (fun a => d (ι₁ a)) (fun b => d (ι₂ b)) (fun a => σ (ι₁ a))
    (fun b => σ (ι₂ b)) hc1 hc2 fun a b h α => hlink _ _ (m1 a) (m2 b) h α
  obtain ⟨φ⟩ := IsSubquotient.nonempty_equiv hsub π.irr hirr
  refine ⟨π₁, π₂, ⟨φ.symm⟩, fun α hα => ?_⟩
  obtain ⟨a, ha1, hψ⟩ := exists_eq_of_inSupport hG π₁.π (fun a => d (ι₁ a)) (fun a => σ (ι₁ a)) _ hc1 hα
  exact m1 a (Finset.mem_filter.2 ⟨Finset.mem_univ _, ha1, α, hψ⟩)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalIrreducibleFixedVectorsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_irreducible_fixed_vectors : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S → ∀ (s : SplitPlace L) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS S s σ → ∀ c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L, Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → ∀ (K : Subgroup (GL (Fin n) (s.w.adicCompletion L))) (θ : GL (Fin n) (s.w.adicCompletion L) → ℂ), K ≤ KO (s.w.adicCompletion L) (Fin n) → (∀ h ∈ KOne (s.w.adicCompletion L) (Fin n), h ∈ K ∧ θ h = 1) → ∀ f ∈ NG.isoTyp a.ρ S, f ≠ 0 → (∀ x : GAf L n, TrivOutside {s.v} x → Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x) ∈ K → NG.rt L n x f = θ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) • f) → ∃ y : σ.V, y ≠ 0 ∧ ∀ h ∈ K, σ.ρ h y = θ h • y := by
  first | exact @GlobalTheory.EigLocal.exists_eigen_local | exact GlobalTheory.EigLocal.exists_eigen_local | (intros; apply GlobalTheory.EigLocal.exists_eigen_local <;> assumption)
end

