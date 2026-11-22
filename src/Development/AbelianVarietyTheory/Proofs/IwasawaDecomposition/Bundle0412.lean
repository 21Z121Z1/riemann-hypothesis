import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0397
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0255
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0021
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0149
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0008
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SignAtBasePlaceEqEmbedding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockFrameConjugationIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1098
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0939
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0919
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0986
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0404
import Formalism.LocalToGlobal.Divisibility.QLocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0390
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0389
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0399
import Formalism.LocalToGlobal.Columns.Bundle0009

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemParLevOfQ
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.Mem.R3.LiftBrg.ActQ

variable (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (U : Set I.ι)
  (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U))

theorem mem_parLev_of_Q (i : Fin X.toD7.R.m) (t : TupU I U) (q : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q) :
    Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _) ∈
      Formalism.L2.DIV.parLev X.toD7.sp.cm (Vc X.toD7 i).gram (L.βV i) (L.datVt i t) := q.2.1

def rV (i : Fin X.toD7.R.m) (t : TupU I U) (x : GL (Fin (Vc X.toD7 i).rank) (Formalism.IndefR.Lev.EAf X.toD7)) : G0 L.Pg X.toD7.R.r :=
  rTup (L.βV i) (L.datVt i t) x

theorem rV_one (i : Fin X.toD7.R.m) (t : TupU I U) : rV X I U L i t 1 = 1 := rTup_one

theorem rV_mul (i : Fin X.toD7.R.m) (t : TupU I U) {x y : GL (Fin (Vc X.toD7 i).rank) (Formalism.IndefR.Lev.EAf X.toD7)}
    (hx : x ∈ Formalism.L2.DIV.parLev X.toD7.sp.cm (Vc X.toD7 i).gram (L.βV i) (L.datVt i t))
    (hy : y ∈ Formalism.L2.DIV.parLev X.toD7.sp.cm (Vc X.toD7 i).gram (L.βV i) (L.datVt i t)) :
    rV X I U L i t (x * y) = rV X I U L i t x * rV X I U L i t y := rTup_mul hx hy

def redQ (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r) (i : Fin X.toD7.R.m) (t : TupU I U) :
    (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q →* Gc X.B px where
  toFun q := eG.symm (rV X I U L i t
    (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _)))
  map_one' := by
    simp only [OneMemClass.coe_one, map_one]
    rw [rV_one, map_one]
  map_mul' a b := by
    simp only [Subgroup.coe_mul, map_mul]
    rw [rV_mul X I U L i t (mem_parLev_of_Q X I U L i t a) (mem_parLev_of_Q X I U L i t b), map_mul]

theorem redQ_apply (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r) (i : Fin X.toD7.R.m) (t : TupU I U)
    (q : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q) :
    redQ X I U L eG i t q = eG.symm (rV X I U L i t
      (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _))) := rfl

theorem eG_redQ (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r) (i : Fin X.toD7.R.m) (t : TupU I U)
    (q : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q) :
    eG (redQ X I U L eG i t q) = rV X I U L i t
      (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _)) := by
  rw [redQ_apply]
  exact eG.apply_symm_apply _

theorem redQ_eq_one_iff (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r) (i : Fin X.toD7.R.m) (t : TupU I U)
    (q : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q) :
    redQ X I U L eG i t q = 1 ↔ (q : Bridge.Gf (Vc X.toD7 i)) ∈ (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).J := by
  rw [redQ_apply, MulEquiv.map_eq_one_iff]
  constructor
  · intro h
    exact ⟨mem_parLev_of_Q X I U L i t q, Subgroup.mem_bot.2 h⟩
  · intro h
    exact Subgroup.mem_bot.1 h.2

def ptS (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (EA X)) (g : Bridge.Gf (Vc X.toD7 i)) :
    Formalism.L2.Col.DecoSet X.B.fields.E X.B.R.nV ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) :=
  ptL X I U i t A k g

def redZ (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (EA X))
    (κ : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q) :
    Formalism.L2.Col.GLG X.B.fields.E X.B.R.nV (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) :=
  fun w => Formalism.L2.DIV.redFn (1 : GL (Fin X.B.R.nV) (EA X)) w.1
    ((A * k)⁻¹ * castGL (rkEq X i).symm
      (Formalism.UG.bc (swapAE X.toD7) ((κ : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _)) * (A * k))

end GlobalTheory.Mem.R3.LiftBrg.ActQ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemRationalGLOfUnitaryGroupGramUnitGram
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MtInRat

variable {D : D7}

theorem toGf_injective {V : HSp D} (P : principalLevelFrame.RowPsi V V.rank) (hU : UnitFr P) : Function.Injective (toGf P) := by
  intro a b h
  have h1 : finHom V (P.ψ a) = finHom V (P.ψ b) := congrArg Subtype.val h
  have h2 : Formalism.IndefR.Lev.finE V (P.ψ a) = Formalism.IndefR.Lev.finE V (P.ψ b) := by
    simp only [Formalism.IndefR.Lev.finE, MonoidHom.comp_apply, h1]
  rw [hU, hU] at h2
  exact Subtype.ext h2

theorem toGf_surjective {V : HSp D} (P : principalLevelFrame.RowPsi V V.rank) : Function.Surjective (toGf P) := by
  rintro ⟨_, x, rfl⟩
  obtain ⟨k, k1, k2⟩ := GlobalTheory.UnitarySplit.ga_glue V 1 _ (one_mem _) (GlobalTheory.UnitarySplit.finHom_mem V x)
  obtain ⟨h, hh⟩ := P.onto k k1
  refine ⟨h, Subtype.ext ?_⟩
  show finHom V (P.ψ h) = finHom V x
  rw [hh, k2]

theorem af_nontrivial : Nontrivial (ReciprocityTheory.Aut.AFplus D.host.E) := by
  obtain ⟨I, hbot, htop⟩ := Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top.mp
    (NumberField.RingOfIntegers.not_isField (maximalRealSubfield D.host.E))
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I htop.ne
  let v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) := ⟨M, hM.isPrime, fun h => by
    rw [h] at hIM
    exact hbot.ne' (le_bot_iff.mp hIM)⟩
  refine ⟨⟨0, 1, fun h => ?_⟩⟩
  have := congrArg (ReciprocityTheory.Aut.evalAt D.host.E v) h
  rw [map_zero, map_one] at this
  exact zero_ne_one this

theorem inclL_injective :
    Function.Injective (Algebra.TensorProduct.includeLeftRingHom : D.host.E →+* ReciprocityTheory.Aut.AL D.host.E) := by
  haveI := af_nontrivial (D := D)
  haveI : Nontrivial (ReciprocityTheory.Aut.AL D.host.E) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left _ _ _
      (algebraMap (maximalRealSubfield D.host.E) (ReciprocityTheory.Aut.AFplus D.host.E)).injective
  exact (Algebra.TensorProduct.includeLeftRingHom : D.host.E →+* ReciprocityTheory.Aut.AL D.host.E).injective

theorem inclA_injective : Function.Injective (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) :=
  Algebra.TensorProduct.includeRight_injective (NumberField.AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)

def glL (n : ℕ) : GL (Fin n) D.host.E →* GL (Fin n) (ReciprocityTheory.Aut.AL D.host.E) :=
  Matrix.GeneralLinearGroup.map Algebra.TensorProduct.includeLeftRingHom

theorem glL_injective (n : ℕ) : Function.Injective (glL (D := D) n) := fun a b h =>
  Units.ext (Matrix.map_injective inclL_injective (congrArg Units.val h))

theorem glL_mem (n : ℕ) (x : GL (Fin n) D.host.E) (hx : x ∈ ReciprocityTheory.Aut.GQ0 D.host.E n) :
    glL n x ∈ ReciprocityTheory.Aut.GA D.host.E n := by
  have h : (x : Matrix (Fin n) (Fin n) D.host.E) *
      ReciprocityTheory.Aut.conjT (IsCMField.complexConj D.host.E : D.host.E →+* D.host.E) x = 1 := hx
  have h2 := congrArg (fun M => Matrix.map M
    (Algebra.TensorProduct.includeLeftRingHom : D.host.E →+* ReciprocityTheory.Aut.AL D.host.E)) h
  simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h2
  show (x : Matrix (Fin n) (Fin n) D.host.E).map _ * ReciprocityTheory.Aut.conjT (ReciprocityTheory.Aut.conjAL D.host.E)
    ((x : Matrix (Fin n) (Fin n) D.host.E).map _) = 1
  rw [← h2]
  congr 1

def toStd (n : ℕ) : ReciprocityTheory.Aut.GQ0 D.host.E n →* ReciprocityTheory.Aut.GQ D.host.E n where
  toFun x := ⟨⟨glL n x.1, glL_mem n x.1 x.2⟩, Subgroup.mem_subgroupOf.2 ⟨x.1, x.2, rfl⟩⟩
  map_one' := by ext1; ext1; exact map_one _
  map_mul' a b := by ext1; ext1; exact map_mul _ _ _

theorem toStd_bij (n : ℕ) : Function.Bijective (toStd (D := D) n) := by
  refine ⟨fun a b h => Subtype.ext (glL_injective n (congrArg (fun y => y.1.1) h)), fun γ => ?_⟩
  obtain ⟨x, hx, he⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 γ.2)
  exact ⟨⟨x, hx⟩, Subtype.ext (Subtype.ext he)⟩

section V

variable {V : HSp D}

theorem cT_eq {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) :
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) M =
      ReciprocityTheory.Aut.conjT (IsCMField.complexConj D.host.E : D.host.E →+* D.host.E) M := rfl

theorem mem_UJ (hV : V.gram = 1) (x : GL (Fin V.rank) D.host.E) (hx : x ∈ ReciprocityTheory.Aut.GQ0 D.host.E V.rank) :
    x ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram := by
  have h : (x : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *
      ReciprocityTheory.Aut.conjT (IsCMField.complexConj D.host.E : D.host.E →+* D.host.E) x = 1 := hx
  show Formalism.UG.cT _ (x : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram * x = V.gram
  rw [hV, Matrix.mul_one, cT_eq]
  exact mul_eq_one_comm.1 h

theorem mem_rationalGL_of_unitaryGroupGram_unitGram (hV : V.gram = 1) (x : GL (Fin V.rank) D.host.E)
    (hx : x ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram) : x ∈ ReciprocityTheory.Aut.GQ0 D.host.E V.rank := by
  have h : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (x : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram * x =
    V.gram := hx
  rw [hV, Matrix.mul_one, cT_eq] at h
  exact mul_eq_one_comm.1 h

theorem mem_HR (x : GL (Fin V.rank) D.host.E) (hx : x ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram) :
    Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) x ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
  have h : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (x : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram * x =
    V.gram := hx
  have h2 := GlobalTheory.UnitarySplit.map_cond (inclR (F := D.host.F) (AF D.host.F)) (D.sp.cm.sig : D.host.E →+* D.host.E)
    (sigR (AF D.host.F) D.sp.cm.sig) (fun y => rfl) V.gram x.1
  rw [h] at h2
  exact h2.symm

def toV (hV : V.gram = 1) : ReciprocityTheory.Aut.GQ0 D.host.E V.rank →* Formalism.L2.Theta.GQ V where
  toFun x := ⟨⟨Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) x.1, mem_HR x.1 (mem_UJ hV x.1 x.2)⟩,
    Subgroup.mem_subgroupOf.2 ⟨x.1, mem_UJ hV x.1 x.2, rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext (p := fun g => g ∈ HR (AF D.host.F) D.sp.cm.sig V.gram)
    exact map_one _
  map_mul' a b := by
    apply Subtype.ext
    apply Subtype.ext (p := fun g => g ∈ HR (AF D.host.F) D.sp.cm.sig V.gram)
    exact map_mul _ _ _

theorem toV_bij (hV : V.gram = 1) : Function.Bijective (toV hV) := by
  refine ⟨fun a b h => Subtype.ext (Units.ext (Matrix.map_injective inclA_injective
    (congrArg (fun y : Formalism.L2.Theta.GQ V => Units.val (y.1 : HR (AF D.host.F) D.sp.cm.sig V.gram).1) h))), fun δ => ?_⟩
  obtain ⟨x, hx, he⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 δ.2)
  exact ⟨⟨x, mem_rationalGL_of_unitaryGroupGram_unitGram hV x hx⟩, Subtype.ext (Subtype.ext he)⟩

def ratE (hV : V.gram = 1) : ReciprocityTheory.Aut.GQ D.host.E V.rank ≃* Formalism.L2.Theta.GQ V :=
  (MulEquiv.ofBijective (toStd (D := D) V.rank) (toStd_bij V.rank)).symm.trans (MulEquiv.ofBijective (toV hV) (toV_bij hV))

theorem ratE_toStd (hV : V.gram = 1) (x : ReciprocityTheory.Aut.GQ0 D.host.E V.rank) : ratE hV (toStd V.rank x) = toV hV x :=
  congrArg (toV hV) ((MulEquiv.ofBijective (toStd (D := D) V.rank) (toStd_bij V.rank)).symm_apply_apply x)

theorem swapAE_injective : Function.Injective (swapAE D) :=
  (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective

theorem finHom_eq_of_finE {g h : GA D V} (e : Formalism.IndefR.Lev.finE V g = Formalism.IndefR.Lev.finE V h) :
    finHom V g = finHom V h :=
  Units.ext (Matrix.map_injective swapAE_injective (congrArg Units.val e))

theorem finE_toV (hV : V.gram = 1) (x : ReciprocityTheory.Aut.GQ0 D.host.E V.rank) :
    Formalism.IndefR.Lev.finE V ((toV hV x : Formalism.L2.Theta.GQ V) : GA D V) = km D V.rank (toStd V.rank x).1 := by
  apply Units.ext
  ext i j
  show swapAE D ((Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E))
    ((1 : AF D.host.F) ⊗ₜ[D.host.F] (x.1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E) i j)) = _
  simp [Algebra.TensorProduct.map_tmul, swapAE, glL]
  rfl

theorem ratIso_ratE (hV : V.gram = 1) (P : principalLevelFrame.RowPsi V V.rank) (hU : UnitFr P) : RatIso P (ratE hV) := by
  intro γ
  obtain ⟨x, rfl⟩ := (toStd_bij (D := D) V.rank).2 γ
  have hr := ratE_toStd hV x
  refine ⟨(congrArg (Bridge.ratF V) hr).trans (Subtype.ext ?_), fun γ₀ h => ?_⟩
  · exact finHom_eq_of_finE ((finE_toV hV x).trans (hU (toStd V.rank x).1).symm)
  · have hx : x.1 = γ₀ := glL_injective V.rank (Units.ext h)
    have key : Bridge.IsRatMat V (toV hV x) γ₀ := by
      show Formalism.L2.Theta.matHom V ((toV hV x : Formalism.L2.Theta.GQ V) : GA D V) = Formalism.UG.bc (incA D) γ₀
      rw [← hx]
      rfl
    exact hr ▸ key

end V

theorem toGf_bij_ratIso : ∀ (D : D7) (V : HSp D) (P : principalLevelFrame.RowPsi V V.rank), V.gram = 1 → UnitFr P →
    Function.Bijective (toGf P) ∧ ∃ e, RatIso P e := by
  intro D V P hV hU
  exact ⟨⟨toGf_injective P hU, toGf_surjective P⟩, ratE hV, ratIso_ratE hV P hU⟩

end GlobalTheory.MtInRat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NatPrimeNotMem
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.TwistPlaces

theorem natPrime_not_mem {A : Type} [CommRing A] (P : Ideal A) [hP : P.IsPrime] {p l : ℕ} (hp : p.Prime) (hl : l.Prime)
    (hne : l ≠ p) (hpP : (p : A) ∈ P) : (l : A) ∉ P :=
  _root_.GlobalTheory.NatCastNotMemPrime.natCast_notMem_of_prime_ne P hp hl hne hpP

theorem twistPlaces : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px), I.Ok → ∀ a : I.ι,
    (∀ PP ∈ I.Q a, ¬ (I.xi a).UnrAt PP) → Formalism.IndefR.Lev.IsTwistPlaces (D := X.toD7) X.toD7.host.g (I.Q a) ∧
    ∀ PP ∈ I.Q a, ((X.toD7.host.QS * X.toD7.host.q * X.toD7.host.d * X.toD7.sp.T : ℕ) : 𝓞 X.toD7.host.E) ∉ PP.asIdeal ∧
      ∀ u : X.toD7.what₂.Word, (((X.toD7.mem u).A.T : ℕ) : 𝓞 X.toD7.host.E) ∉ PP.asIdeal := by
  intro X px I hI a hU
  have htw := (GlobalTheory.Mem.ReadTwist.isTwist_of_reads X.B.R X.B.host _ X.B.embLL I.S (I.tup a) (I.xi a) (hI.xi_reads a)).1
  have key := fun PP (hPP : PP ∈ I.Q a) => htw.2.2.2 PP (hU PP hPP)
  have hstar : ∀ x : X.B.host.E, star x = X.B.host.conj x := bridge_star_holds X.B.R X.B.host

  have off : ∀ PP ∈ I.Q a, ∀ l : ℕ, l.Prime → l ∈ I.S → ((l : ℕ) : 𝓞 X.B.host.E) ∉ PP.asIdeal := by
    intro PP hPP l hl hS
    obtain ⟨-, hp, -, hpS⟩ := key PP hPP
    exact natPrime_not_mem PP.asIdeal hp hl (fun e => hpS (e ▸ hS)) (Ideal.absNorm_mem PP.asIdeal)
  refine ⟨fun PP hPP => ⟨?_, fun PP' hPP' hc => ?_⟩, fun PP hPP => ⟨?_, fun u => ?_⟩⟩
  · obtain ⟨-, hp, hsq, hpS⟩ := key PP hPP
    refine ⟨Ideal.absNorm PP.asIdeal, hp, ?_, hsq, fun i e => hpS (e ▸ hI.g_mem i)⟩
    show Nat.card (𝓞 X.B.host.E ⧸ PP.asIdeal) = Ideal.absNorm PP.asIdeal
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  · obtain ⟨v, -, rfl, -⟩ := I.exists_of_mem_Q hPP
    obtain ⟨v', -, rfl, -⟩ := I.exists_of_mem_Q hPP'
    have hle : v.asIdeal ≤ v'.asIdeal := by
      intro c hc'
      have h1 : algebraMap (𝓞 X.B.host.F) (𝓞 X.B.host.E) c ∈ (I.sel v).asIdeal := by
        have := hI.sel_ok v
        rw [← this] at hc'
        exact hc'
      obtain ⟨c', h2, h3⟩ := hc _ h1
      have h4 : c' = algebraMap (𝓞 X.B.host.F) (𝓞 X.B.host.E) c := by
        apply RingOfIntegers.ext
        rw [h3]
        show star (algebraMap X.B.host.F X.B.host.E (c : X.B.host.F)) = algebraMap X.B.host.F X.B.host.E (c : X.B.host.F)
        rw [hstar, ← X.B.conjF_eq, AlgHom.commutes]
      rw [h4] at h2
      rw [← hI.sel_ok v']
      exact h2
    have hv : v = v' := HeightOneSpectrum.ext (v.isMaximal.eq_of_le v'.isPrime.ne_top hle)
    subst hv
    obtain ⟨⟨x, hx, hy⟩, -⟩ := key _ hPP
    obtain ⟨c', h2, h3⟩ := hc x hx
    exact hy c' (h3.trans (hstar _)) h2
  · have hp2 : ((X.B.host.QS : ℕ) : 𝓞 X.B.host.E) ∉ PP.asIdeal := fun h => by
      rw [← Nat.prod_primeFactorsList X.B.host.QS_pos.ne', Nat.cast_list_prod] at h
      have := PP.isPrime
      obtain ⟨a, ha, h'⟩ := (Ideal.IsPrime.multiset_prod_mem_iff_exists_mem PP.isPrime
        ((X.B.host.QS.primeFactorsList.map Nat.cast : List (𝓞 X.B.host.E)) : Multiset _)).1 (by simpa using h)
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 (Multiset.mem_coe.1 ha)
      exact off PP hPP l (Nat.prime_of_mem_primeFactorsList hl)
        (hI.mem_of_dvd_QS (Nat.prime_of_mem_primeFactorsList hl) (Nat.dvd_of_mem_primeFactorsList hl)) h'
    have hq : ((X.B.host.q : ℕ) : 𝓞 X.B.host.E) ∉ PP.asIdeal := off PP hPP _ X.B.host.hyp.1 hI.two_q_d_mem.2.1
    have hd : ((X.B.host.d : ℕ) : 𝓞 X.B.host.E) ∉ PP.asIdeal := off PP hPP _ X.B.host.hyp.2.1 hI.two_q_d_mem.2.2
    have hT : ((X.B.T X.B.u₀ : ℕ) : 𝓞 X.B.host.E) ∉ PP.asIdeal :=
      off PP hPP _ (X.B.T_prime X.B.u₀) (hI.T_mem X.B.u₀)
    have hsp : X.toD7.sp.T = X.B.T X.B.u₀ := X.B.sp_T
    rw [hsp]
    show ((X.B.host.QS * X.B.host.q * X.B.host.d * X.B.T X.B.u₀ : ℕ) : 𝓞 X.B.host.E) ∉ PP.asIdeal
    have hPr := PP.isPrime
    push_cast
    intro h
    rcases hPr.mem_or_mem h with h | h
    · rcases hPr.mem_or_mem h with h | h
      · rcases hPr.mem_or_mem h with h | h
        · exact hp2 (by exact_mod_cast h)
        · exact hq h
      · exact hd h
    · exact hT h
  · have hA : (X.toD7.mem u).A.T = X.B.T u := X.C.A_T u
    rw [hA]
    exact off PP hPP _ (X.B.T_prime u) (hI.T_mem u)

end GlobalTheory.Mem.TwistPlaces
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyIsoOfEquivariantHomIntoIsotypicSum
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.CuspMult

namespace GlobalTheory.IsoRankMult

open GlobalTheory.RepCount in
theorem iso_of_hom_into_sum : ∀ (H S0 S X : Type) [Group H] [AddCommGroup S0] [Module ℂ S0] [AddCommGroup S] [Module ℂ S] [AddCommGroup X] [Module ℂ X] (σ0 : Representation ℂ H S0) (σ : Representation ℂ H S) (ρ : Representation ℂ H X) (C : Submodule ℂ X), σ0.IsIrreducible → σ.IsIrreducible → ∀ f ∈ homInto σ ρ (⨆ g ∈ homInto σ0 ρ C, LinearMap.range g), f ≠ 0 → Nonempty (σ.asModule ≃ₗ[MonoidAlgebra ℂ H] σ0.asModule) := by
  intro H S0 S X _ _ _ _ _ _ _ σ0 σ ρ C h0 h1 f hf hne
  let R := MonoidAlgebra ℂ H
  haveI : IsSimpleModule R σ0.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule σ0).mp h0
  haveI : IsSimpleModule R σ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule σ).mp h1

  let N' : Submodule R ρ.asModule :=
    ⨆ (g : S0 →ₗ[ℂ] X) (hg : g ∈ homInto σ0 ρ C), LinearMap.range (modMap g hg.2)
  have hN'iso : N' ≤ isotypicComponent R ρ.asModule σ0.asModule := by
    refine iSup₂_le fun g hg => ?_
    rcases LinearMap.injective_or_eq_zero (modMap (σ := σ0) (ρ := ρ) g hg.2) with hi | hz
    · exact le_sSup ⟨(LinearEquiv.ofInjective _ hi).symm⟩
    · rw [hz, LinearMap.range_zero]; exact bot_le
  have hsub : (⨆ g ∈ homInto σ0 ρ C, LinearMap.range g) ≤
      (N'.restrictScalars ℂ).comap ρ.asModuleEquiv.symm.toLinearMap := by
    refine iSup₂_le fun g hg => ?_
    rintro _ ⟨s, rfl⟩
    have hmem : modMap (σ := σ0) (ρ := ρ) g hg.2 (σ0.asModuleEquiv.symm s) ∈ N' :=
      (le_iSup₂_of_le (f := fun (g : S0 →ₗ[ℂ] X) (hg : g ∈ homInto σ0 ρ C) =>
        LinearMap.range (modMap (σ := σ0) (ρ := ρ) g hg.2)) g hg le_rfl) ⟨_, rfl⟩
    show ρ.asModuleEquiv.symm (g s) ∈ N'
    convert hmem using 1
    apply ρ.asModuleEquiv.injective
    rw [modMap_apply]; simp
  let F := modMap (σ := σ) (ρ := ρ) f hf.2
  have hFi : Function.Injective F := by
    rcases LinearMap.injective_or_eq_zero F with hi | hz
    · exact hi
    · exfalso; apply hne
      ext s
      have := congrArg (fun φ => ρ.asModuleEquiv (φ (σ.asModuleEquiv.symm s))) hz
      simp only [F, modMap_apply, LinearMap.zero_apply, map_zero] at this
      simpa using this
  have hle : LinearMap.range F ≤ isotypicComponent R ρ.asModule σ0.asModule := by
    refine le_trans ?_ hN'iso
    rintro _ ⟨x, rfl⟩
    have hx := hsub (hf.1 (σ.asModuleEquiv x))
    have : ρ.asModuleEquiv.symm (f (σ.asModuleEquiv x)) = F x := by
      apply ρ.asModuleEquiv.injective; simp [F, modMap_apply]
    rw [← this]; exact hx
  let e := LinearEquiv.ofInjective F hFi
  haveI : IsSimpleModule R (LinearMap.range F) := IsSimpleModule.congr e.symm
  obtain ⟨e'⟩ := isIsotypicOfType_submodule_iff.mp
    (IsIsotypicOfType.isotypicComponent R ρ.asModule σ0.asModule) (LinearMap.range F) hle
  exact ⟨e.trans e'⟩

end GlobalTheory.IsoRankMult
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ParahoricTypeRCMulInvMemStatement
section
open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parahoricTypeRC_mul_inv_mem : ∀ (F : Type) [Field F] (O : Subring F) (ϖ : F), ϖ ∈ O → ∀ (r c : ℕ) (k k' : GL (Fin (r + c)) F), k ∈ parJ O ϖ r c → k' ∈ parJ O ϖ r c → k * k' ∈ parJ O ϖ r c ∧ k⁻¹ ∈ parJ O ϖ r c := by
  first | exact @GlobalTheory.ParGroup.parJ_mul_inv | exact GlobalTheory.ParGroup.parJ_mul_inv | (intros; apply GlobalTheory.ParGroup.parJ_mul_inv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlacesUnder
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MtIn.Under

theorem not_both {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : q ≠ p) (h1 : (p : 𝓞 E) ∈ P.asIdeal) (h2 : (q : 𝓞 E) ∈ P.asIdeal) : False := by
  have hc : IsCoprime (q : 𝓞 E) (p : 𝓞 E) := Nat.Coprime.cast ((Nat.coprime_primes hq hp).2 hne)
  obtain ⟨x, y, hxy⟩ := hc
  exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hxy ▸ P.asIdeal.add_mem (P.asIdeal.mul_mem_left _ h2) (P.asIdeal.mul_mem_left _ h1)))

theorem q_mem {D : D7} {P : Pl D.host.E} {q : ℕ} (h : Nat.card (kP P) = q) : (q : 𝓞 D.host.E) ∈ P.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← h]
  have := card_nsmul_eq_zero' (G := kP P) (x := 1)
  rwa [nsmul_one] at this

theorem places_under : ∀ (D : D7) (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 → (∀ PP, PP ∈ L.Pg ↔ ∃ k v, PP = D.naut.plGw k v) → ∀ (i : Fin D.R.m) (t : T) (PP : Pl D.host.E), PP ∈ L.Pg ∨ PP ∈ L.Q t → ∀ v, NG.OverPl PP v → v ∈ gPl D ∪ qPl D (L.C.mu0 i * L.xiH t) := by
  intro D T L μ0 hL hPg i t PP hPP v hv
  by_cases hg : v ∈ gPl D
  · exact Or.inl hg
  rcases hPP with hP | hQ
  · obtain ⟨k, w, rfl⟩ := (hPg _).1 hP
    exact absurd ⟨_, hv, k, D.naut.plGw_over k w⟩ hg
  · refine Or.inr ⟨hg, PP, hv, fun hu => ?_⟩
    obtain ⟨⟨q, hq1, hq2, -, hq4⟩, -⟩ := hL.Q_pl t PP hQ
    have hm : (L.C.mu0 i).UnrAt PP := (L.C.isMu0 i).unr PP fun l hl =>
      not_both (D.host.g_prime l) hq1 (hq4 l) hl (q_mem hq2)
    have hx : (L.xiH t).UnrAt PP := by
      intro x hx
      have h1 : (L.C.mu0 i).loc PP x * (L.xiH t).loc PP x = 1 := hu x hx
      rwa [hm x hx, one_mul] at h1
    exact (hL.Q_ram t PP).2 (Or.inl hQ) hx

end GlobalTheory.MtIn.Under

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PsiLevelPairCompatibleOfColumnLevelsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psiLevelPairCompatible_of_columnLevels : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r) (cG : G0 L.Pg X.toD7.R.r ≃* G0g X.toD7.nd) (plg : (Σ k : Fin 2, X.toD7.nd.PlG k) ≃ L.Pg) (iso : ∀ kv : (Σ k : Fin 2, X.toD7.nd.PlG k), ZMod (X.toD7.host.g kv.1) ≃+* kP (plg kv).1), I.Ok → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → (∀ kv, ((plg kv : L.Pg) : Pl X.toD7.host.E) = X.toD7.naut.plGw kv.1 kv.2) → (∀ g kv, eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (X.toD7.host.g kv.1) →+* kP (plg kv).1) ((eG.trans cG) g kv)) → PsiPPTie X.toD7 (lev0 I) (chr0 I) (lev1 I) (chr1 I) (eG.trans cG) := by
  first | exact @GlobalTheory.Mem.PsiTie.psiPPTie_of_levOf | exact GlobalTheory.Mem.PsiTie.psiPPTie_of_levOf | (intros; apply GlobalTheory.Mem.PsiTie.psiPPTie_of_levOf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFormClassSumPrincipalEqCardMulLevel
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.R3 GlobalTheory.Mem.ColTie

namespace GlobalTheory.Mem.ColTie

theorem ipK_eq_card_mul_ipLev {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
    (P : LevFam X.E X.K R.r Pr.vGs) (hX : X.Ok) (z z' : MtildeV W Ch sel mu P) :
    ipK W Ch sel mu P hX z z' = (Nat.card P.grp : X.K) * ipLev W Ch sel mu P hX z z' := by
  have h0 : (Nat.card P.grp : X.K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have h1 := levelSumX W Ch sel mu P (mtildeOk W Ch sel mu hX P) (mtildeKOk W Ch sel mu hX) z.1 z'.1 z.2 z'.2
  unfold ipLev ipK
  rw [h1, mul_inv_cancel_left₀ h0]

end GlobalTheory.Mem.ColTie
end

