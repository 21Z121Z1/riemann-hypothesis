import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0894
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOfBalanced
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1795
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1879
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1473
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1731
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0220
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0370
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1872
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1866
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1867
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1870
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1845
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1869
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1896
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthCond
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceLatticeLeThetaLatticeAtPlace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0325
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0193
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LeafDataOfOnTieOfIntegral
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0082
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharEqOfFinitePartPowerInverse
section
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

noncomputable section

namespace GlobalTheory.NormRatio.ChrFin

open Formalism.L2.JoinChr

theorem toFinE_inc (D : D7) (a : D.host.E) :
    GlobalTheory.BotFormula.toFinE D (Formalism.MainNotions.StandardLatticesGL3.inc D a) = algebraMap D.host.E _ a :=
  (GlobalTheory.LFun.toFinAd_tmul 1 a).trans (by rw [map_one, one_mul])

theorem toFinE_int (D : D7) {r : Formalism.MainNotions.StandardLatticesGL3.AE D} (hr : r ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D) (P : HeightOneSpectrum (𝓞 D.host.E)) :
    Valued.v (GlobalTheory.BotFormula.toFinE D r P) ≤ 1 := by
  let S : Subring (Formalism.MainNotions.StandardLatticesGL3.AE D) := (Formalism.UG.intAd D.host.E).comap (GlobalTheory.BotFormula.toFinE D).toRingHom
  have hS : Formalism.MainNotions.StandardLatticesGL3.OhE D ≤ S := by
    refine Subring.closure_le.2 ?_
    rintro z (⟨⟨x, hx⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · obtain ⟨x', rfl⟩ := hx
      intro Q
      change GlobalTheory.BotFormula.toFinE D (Formalism.MainNotions.StandardLatticesGL3.inc D _) Q ∈ _
      rw [toFinE_inc, HeightOneSpectrum.mem_adicCompletionIntegers]
      change Valued.v ((algebraMap D.host.E (Q.adicCompletion D.host.E)) _) ≤ 1
      exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' Q _).trans_le (Q.valuation_le_one x')
    · intro Q
      have h := (GlobalTheory.LFun.mem_int_iff (F := ℚ) (E := D.host.E) (y ⊗ₜ[ℚ] ((1 : 𝓞 D.host.E) : D.host.E))).1
        (AddSubgroup.subset_closure ⟨y, fun v => hy v, 1, rfl⟩) Q
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      exact h
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hS hr P)

theorem adEquiv_eq (D : D7) (z : Formalism.MainNotions.StandardLatticesGL3.AE D) :
    GlobalTheory.Mem.Col2.SplitChar.adEquiv D z = GlobalTheory.BotFormula.toFinE D z := by
  refine GlobalTheory.PlaceIdem.adele_ext fun P => ?_
  let f1 : Formalism.MainNotions.StandardLatticesGL3.AE D →+* P.adicCompletion D.host.E :=
    (RestrictedProduct.evalRingHom _ P).comp (GlobalTheory.Mem.Col2.SplitChar.adEquiv D).toRingHom
  let f2 : Formalism.MainNotions.StandardLatticesGL3.AE D →+* P.adicCompletion D.host.E :=
    (RestrictedProduct.evalRingHom _ P).comp (GlobalTheory.BotFormula.toFinE D).toRingHom
  change f1 z = f2 z
  by_contra hne
  have hd : Valued.v (f1 z - f2 z) ≠ 0 := (Valuation.ne_zero_iff _).2 (sub_ne_zero.2 hne)
  obtain ⟨n, hn, hv⟩ := GlobalTheory.Mem.Col2.SplitChar.exists_nat_val_lt P hd
  obtain ⟨a, r, hr, hz⟩ := GlobalTheory.Mem.Col2.SplitChar.exists_approx z hn
  have ha : f1 (Formalism.MainNotions.StandardLatticesGL3.inc D a) = f2 (Formalism.MainNotions.StandardLatticesGL3.inc D a) := by
    change GlobalTheory.Mem.Col2.SplitChar.adEquiv D (Formalism.MainNotions.StandardLatticesGL3.inc D a) P = GlobalTheory.BotFormula.toFinE D (Formalism.MainNotions.StandardLatticesGL3.inc D a) P
    rw [GlobalTheory.Mem.Col2.SplitChar.adEquiv_inc, toFinE_inc]
  have e1 : f1 z - f2 z = (n : P.adicCompletion D.host.E) * (f1 r - f2 r) := by
    rw [hz, map_add, map_add, map_mul, map_mul, map_natCast, map_natCast, ha]
    ring
  have h1 : Valued.v (f1 r) ≤ 1 := GlobalTheory.Mem.Col2.SplitChar.vl_le hr P
  have h2 : Valued.v (f2 r) ≤ 1 := toFinE_int D hr P
  have h3 : Valued.v (f1 r - f2 r) ≤ 1 := Valuation.map_sub_le _ h1 h2
  have h4 : Valued.v ((n : P.adicCompletion D.host.E)) = P.valuation D.host.E (n : D.host.E) := by
    rw [← map_natCast (algebraMap D.host.E (P.adicCompletion D.host.E)) n]
    exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P _
  have h5 : Valued.v (f1 z - f2 z) ≤ P.valuation D.host.E (n : D.host.E) := by
    rw [e1, map_mul, h4]
    exact mul_le_of_le_one_right' h3
  exact absurd (h5.trans_lt hv) (lt_irrefl _)

theorem chrEq_of_finPart : ∀ {D : D7} (χ : (AE D)ˣ →* Circle) {N : ℕ} (c : Formalism.MainNotions.StandardLatticesGL3.HeckeU D N) (e : ℤ)
    (ν : Formalism.L2.Host.HChar D.host.E),
    IsHeckeChar D χ → HasFinPart χ c (-e) → (∀ x, c.f x ^ e = (ν⁻¹).1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D x)) →
      ChrEq χ ν := by
  intro D χ N c e ν hχ hf hν
  refine ⟨hχ, fun P ε hε k x hx => ?_⟩
  have hι : ∀ x : D.host.E, GlobalTheory.LFun.finAdEquiv D.host.F D.host.E ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) =
      algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x :=
    fun x => (GlobalTheory.LFun.toFinAd_tmul 1 x).trans (by rw [map_one, one_mul])
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.HeckeTensorRead.isPlIdem_parts D (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E) hι
    GlobalTheory.LFun.mem_int_iff hε
  have hinf : infPart D (x : AE D) = 1 := by
    rw [hx, locE, GlobalTheory.HeckeTensorRead.map_loc (infPart D), h1, zero_mul, add_zero]
  have hfin : GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D (x : AE D)) =
      Neutral.B1.finiteSingle D.host.E P (algebraMap D.host.E _ (k : D.host.E)) := by
    have h4 : GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D (incA D (k : D.host.E))) =
        algebraMap D.host.E _ (k : D.host.E) := hι _
    have h5 : GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D (locE D ε (k : D.host.E))) =
        1 + GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D ε) *
          (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D (incA D (k : D.host.E))) - 1) :=
      GlobalTheory.HeckeTensorRead.map_loc ((GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).toRingHom.comp (finPart D)) ε _
    rw [hx, h5]
    exact GlobalTheory.HeckeTensorRead.loc_eq_finSingle P _ _ _ h4 h2 h3
  let u : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ :=
    Units.map ((GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).toRingHom.comp (finPart D)).toMonoidHom x
  let y : (Formalism.MainNotions.StandardLatticesGL3.AE D)ˣ := Units.map (GlobalTheory.BotFormula.toFinE D).symm.toRingHom.toMonoidHom u
  have hy1 : GlobalTheory.BotFormula.toFinE D (y : Formalism.MainNotions.StandardLatticesGL3.AE D) =
      GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D (x : AE D)) :=
    (GlobalTheory.BotFormula.toFinE D).apply_symm_apply _
  have hxy : IsFinIdl x y := ⟨hinf, hy1.symm⟩
  have hval := hf x y hxy
  have hy : GlobalTheory.Mem.Col2.SplitChar.finIdl D y = Neutral.B1.localIdele D.host.E P (Formalism.L2.Host.atFin P k) := by
    refine Units.ext (Prod.ext rfl ?_)
    rw [GlobalTheory.Mem.Col2.SplitChar.finIdl_snd, adEquiv_eq, hy1, hfin]
    rfl
  have hc : c.f y ^ (-e) = ν.1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D y) := by
    rw [zpow_neg, hν y]
    rfl
  rw [hval, hc, hy]
  rfl

end GlobalTheory.NormRatio.ChrFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IpEqZeroOfHeisEigen
section
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.CosetOrth

section General

variable {E : Type} [Field E] [NumberField E]

def InHat (I : FractionalIdeal (𝓞 E)⁰ E) (x : FiniteAdeleRing (𝓞 E) E) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 E), Valued.v (x w) ≤ WithZero.exp (-(FractionalIdeal.count E w I))

theorem inHat_one_iff (x : FiniteAdeleRing (𝓞 E) E) : InHat 1 x ↔ ∀ w, Valued.v (x w) ≤ 1 := by
  simp only [InHat, FractionalIdeal.count_one, neg_zero, WithZero.exp_zero]

theorem inHat_zero (I : FractionalIdeal (𝓞 E)⁰ E) : InHat I 0 := fun w => by
  have : (0 : FiniteAdeleRing (𝓞 E) E) w = 0 := rfl
  rw [this, map_zero]; exact zero_le

theorem InHat.mul_left {I : FractionalIdeal (𝓞 E)⁰ E} {t x : FiniteAdeleRing (𝓞 E) E} (ht : InHat 1 t) (hx : InHat I x) :
    InHat I (t * x) := fun w => by
  have : (t * x) w = t w * x w := rfl
  rw [this, map_mul]
  exact (mul_le_of_le_one_left' ((inHat_one_iff t).1 ht w)).trans (hx w)

theorem InHat.add {I : FractionalIdeal (𝓞 E)⁰ E} {x y : FiniteAdeleRing (𝓞 E) E} (hx : InHat I x) (hy : InHat I y) :
    InHat I (x + y) := fun w => by
  have : (x + y) w = x w + y w := rfl
  rw [this]
  exact (Valued.v.map_add _ _).trans (max_le (hx w) (hy w))

theorem InHat.neg {I : FractionalIdeal (𝓞 E)⁰ E} {x : FiniteAdeleRing (𝓞 E) E} (hx : InHat I x) : InHat I (-x) := fun w => by
  have : (-x) w = -x w := rfl
  rw [this, Valuation.map_neg]
  exact hx w

end General

variable {D : D7}

abbrev FA (D : D7) : Type := FiniteAdeleRing (𝓞 D.host.E) D.host.E

def fe (D : D7) : AE D →+* FA D := (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).toRingHom.comp (finPart D)

theorem fe_apply (x : AE D) : fe D x = GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D x) := rfl

def skewId (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E :=
  (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) /
    ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)

def HatPt {S T : HSp D} (r : D.host.E) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (u : WO S T) : Prop :=
  u.map (infPart D) = 0 ∧ ∀ i j, InHat I (algebraMap D.host.E (FA D) r * fe D (u i j))

def finMat {n : ℕ} (y : Formalism.MainNotions.StandardLatticesGL3.GA D n) : Matrix (Fin n) (Fin n) (FA D) :=
  ((y : GL (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin n) (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)).map (GlobalTheory.BotFormula.toFinE D)

theorem exists_fe (s : FA D) : ∃ σ : AE D, infPart D σ = 0 ∧ fe D σ = s := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  refine ⟨e.symm (0, (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm s), ?_, ?_⟩
  · exact (he _).1.symm.trans (by rw [e.apply_symm_apply])
  · have : finPart D (e.symm (0, (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm s)) =
        (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm s := (he _).2.symm.trans (by rw [e.apply_symm_apply])
    rw [fe_apply, this, RingEquiv.apply_symm_apply]

theorem ip_eq_zero_of_heis_eigen {A B : HSp D} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    {ν : Measure (WO A B)} {𝓕 : Set (WO A B)} (hν : IsCovolOne (ratL B A) ν 𝓕) {f₁ f₂ : WO A B → ℂ}
    (h₁ : IsThetaFunO ψ A B f₁) (h₂ : IsThetaFunO ψ A B f₂) (v : WO A B) {α β : ℂ}
    (e₁ : heisO ψ A B v f₁ = α • f₁) (e₂ : heisO ψ A B v f₂ = β • f₂) (hβ : ‖β‖ = 1) (hne : α ≠ β) :
    ip A B ν 𝓕 f₁ f₂ = 0 := by
  have key := GlobalTheory.Size.ipO_heisO hψ hν.1 hν.2.1 h₁ h₂ v
  rw [e₁, e₂] at key
  have e : GlobalTheory.Ker.ipO ν 𝓕 (α • f₁) (β • f₂) = (α * starRingEnd ℂ β) * ip A B ν 𝓕 f₁ f₂ := by
    unfold GlobalTheory.Ker.ipO ip
    rw [← integral_const_mul]
    refine integral_congr_ae (.of_forall fun w => ?_)
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    ring
  have e' : GlobalTheory.Ker.ipO ν 𝓕 f₁ f₂ = ip A B ν 𝓕 f₁ f₂ := rfl
  rw [e, e'] at key
  have hb : starRingEnd ℂ β * β = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hβ]; simp
  have hne' : α * starRingEnd ℂ β ≠ 1 := fun h => hne (by
    have := congrArg (· * β) h
    simp only [one_mul, mul_assoc, hb, mul_one] at this
    exact this)
  have : (α * starRingEnd ℂ β - 1) * ip A B ν 𝓕 f₁ f₂ = 0 := by rw [sub_mul, key, one_mul, sub_self]
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne')

end GlobalTheory.CosetOrth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHermNDNegGram
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.SWLit
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (UA incM ratU)
open GlobalTheory.WeilM (Darboux symp schA thetaSum UG)
open GlobalTheory.SiegelFormula (coord)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SWLink

variable {D : D7} {n : ℕ} {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D}
  {μ : Measure (Mx D V.rank n)} {ω : StdUnn.G D n →* Module.End ℂ (schwartzA θ V.rank n)}
  {J : Matrix (Fin n) (Fin n) D.host.E} {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E}
  {T : GL (Fin (n + n)) D.host.E} {κ : UD D J₂ ≃* StdUnn.G D n} {ι : UD D (-V.gram) ≃ₜ* GA D V} {d : ℕ}
  {ε : Module.Basis (Fin d) D.host.F D.host.E} {co : Dbx V J₂ d}
  {om : UD D (-V.gram) × UD D J₂ →* Module.End ℂ ((Fin V.rank × Fin n × Fin d → AF D.host.F) → ℂ)}

theorem unramified_host (D : D7) : Algebra.Unramified (𝓞 D.host.F) (𝓞 D.host.E) := by
  haveI := D.host.isCMField_hostE
  exact Formalism.L2.Pj.unramBridge_holds D.host.E fun P hP => by
    obtain ⟨θ, t, ht, hθ⟩ := D.sp.cm.cmUnram.2.2 P hP
    refine ⟨θ, ?_⟩
    have : RingOfIntegers.mapRingEquiv (IsCMField.complexConj D.host.E : D.host.E ≃+* D.host.E) θ = t :=
      RingOfIntegers.ext ht.symm
    rwa [this]

theorem isHermND_neg_gram (V : HSp D) : IsHermND D.sp.cm.sig ((1 : D.host.E) • -V.gram) := by
  rw [one_smul]
  refine ⟨fun i j => ?_, ?_⟩
  · rw [Matrix.neg_apply, Matrix.neg_apply, map_neg]
    exact congrArg Neg.neg (congrFun (congrFun (gram_conjTranspose V) i) j)
  · rw [Matrix.det_neg]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (gram_isUnit_det V).ne_zero

theorem aniso_neg_gram (hV : IsAniso V) (x : Fin V.rank → D.host.E)
    (hx : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form D.sp.cm.sig (-V.gram) x x = 0) : x = 0 := by
  by_contra h0
  refine hV 1 (Matrix.of fun i _ => star (x i)) ⟨one_pos, ?_, ?_⟩
  · refine linearIndependent_unique_iff.2 fun h => h0 (funext fun i => ?_)
    exact star_eq_zero.1 (congrFun h i)
  · funext a b
    rw [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, Matrix.neg_mulVec, dotProduct_neg, neg_eq_zero] at hx
    rw [cT_sig, Matrix.mul_assoc, Matrix.zero_apply, ← hx]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, star_star, dotProduct, Matrix.mulVec]
    rfl

theorem height {K : Subgroup (UD D J₂)} {H : StdUnn.G D n → ℝ≥0} (hH : StdUnn.IsHeight H)
    (hP : ∀ g : UD D J₂, g ∈ siegelOf finSumFinEquiv (uinc D J₂) ↔ κ g ∈ StdUnn.P D n)
    (ha : ∀ p : siegelOf finSumFinEquiv (uinc D J₂),
      StdUnn.blkA (StdUnn.mat (κ p)) = (leviOf finSumFinEquiv (uinc D J₂) p).1)
    (hK : ∀ g : UD D J₂, g ∈ K ↔ κ g ∈ StdUnn.K D n) :
    IwasawaOf finSumFinEquiv (uinc D J₂) (absA D) K ∧ ∀ g, hgtOf finSumFinEquiv (uinc D J₂) (absA D) K g = H (κ g) := by
  have h1 : ∀ (p : siegelOf finSumFinEquiv (uinc D J₂)), ∀ k ∈ K,
      H (κ (p * k)) = absA D (aOf finSumFinEquiv (uinc D J₂) p) := fun p k hk => by
    rw [map_mul]
    exact hH _ ((hP p).1 p.2) _ (ha p) _ ((hK k).1 hk)
  have h2 : IwasawaOf finSumFinEquiv (uinc D J₂) (absA D) K := by
    refine ⟨fun g => ?_, fun p hp => ?_⟩
    · obtain ⟨p, hp, k, hk, e⟩ := GlobalTheory.StdUnn.Iwasawa.exists_mul D n (κ g)
      refine ⟨⟨κ.symm p, (hP _).2 (by rwa [κ.apply_symm_apply])⟩, κ.symm k, (hK _).2 (by rwa [κ.apply_symm_apply]), ?_⟩
      rw [← map_mul, ← e, κ.symm_apply_apply]
    · have e1 := h1 p 1 (one_mem K)
      have e2 := h1 1 p hp
      rw [mul_one] at e1
      rw [OneMemClass.coe_one, one_mul, map_one, map_one] at e2
      exact e1.symm.trans e2
  refine ⟨h2, fun g => ?_⟩
  obtain ⟨p, k, hk, rfl⟩ := h2.1 g
  rw [h2.hgtOf_mul p hk, h1 p k hk]

theorem kfin (hom : IsTrans ε ι κ ω om) {K : Subgroup (UD D J₂)} (hK : ∀ g : UD D J₂, g ∈ K ↔ κ g ∈ StdUnn.K D n)
    {φ : (Fin V.rank × Fin n × Fin d → AF D.host.F) → ℂ}
    (hφ : φ ∈ schA D.host.F (Fin V.rank × Fin n × Fin d)) (Φ : schwartzA θ V.rank n) (e : φ ∘ coord ε = Φ.1)
    (hΦ : RegSch.KFin ω Φ) : FiniteDimensional ℂ (Submodule.span ℂ {Ψ | ∃ k ∈ K, Ψ = om (1, k) φ}) := by
  let L : schwartzA θ V.rank n →ₗ[ℂ] ((Fin V.rank × Fin n × Fin d → AF D.host.F) → ℂ) :=
    (LinearMap.funLeft ℂ ℂ (coordL ε V.rank n).symm).comp (schwartzA θ V.rank n).subtype
  haveI : FiniteDimensional ℂ (Submodule.span ℂ {Ψ : schwartzA θ V.rank n | ∃ k ∈ StdUnn.K D n, Ψ = ω k Φ}) := hΦ
  refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ
    {Ψ : schwartzA θ V.rank n | ∃ k ∈ StdUnn.K D n, Ψ = ω k Φ}).map L) (Submodule.span_le.2 ?_)
  rintro _ ⟨k, hk, rfl⟩
  refine ⟨ω (κ k) Φ, Submodule.subset_span ⟨κ k, (hK k).1 hk, rfl⟩, funext fun y => ?_⟩
  obtain ⟨x, rfl⟩ := (coordL ε V.rank n).surjective y
  rw [coordL_apply, hom.right k hφ Φ e]
  exact congrArg (ω (κ k) Φ).1 ((coordL ε V.rank n).symm_apply_apply x)

theorem skew_xi (D : D7) : ∃ δ : D.host.E, δ ≠ 0 ∧ D.sp.cm.sig δ = -δ := by
  refine ⟨D.host.xi0, GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D, D.host.φ₀.injective ?_⟩
  have hd : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  rw [(GlobalTheory.AdelicU.isCMExt_host D).2.2.2, map_neg]
  unfold Host.xi0
  rw [map_div₀, map_neg, map_one, map_mul, map_natCast, hd]
  simp [div_neg]

end GlobalTheory.SWLink

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeavesSupSpanData
section
set_option autoImplicit false

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn

theorem lat_span_of_hypC {D : D7} {T : Top D} (h : LawsP T) {j : ℕ} (hj : InR D j) {large₂ : SizeData₂ D} {H : WeightAlgebra.KHyp}
    {C2 A2 CR Bx CT : ℝ} {S : WeightAlgebra.Scal (recB h.toLawsCore)} {ka wL wF : WeightFamilies.Wt D j} {Tn nP nW : ℕ} {h0 : ℝ}
    {nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ}
    (hyp : Formalism.MainNotions.Gaps.EtaleWeightGaps.HypC large₂ (recPJ h j hj) H C2 A2 CR Bx CT S ka wL wF Tn nP nW h0 nus) :
    Formalism.MainNotions.Gaps.EtaleWeightGaps.LatAt (recB h.toLawsCore) j ka ∧ ReciprocityTheory.ChartRestriction.G.PullbackSections.SpanAt (recPJ h j hj) ka ∧
      WeightAlgebra.H2 (recPJ h j hj) S ka wL wF := by
  obtain ⟨hA, -, hB, -, hH2, -⟩ := hyp
  obtain ⟨-, -, -, hK, -, po, -, -, PLam, -, -, -, -, hka⟩ := hB
  have sK := GlobalTheory.RunLat.spanAt_of_shortG _ _ _ _ hka
  exact ⟨GlobalTheory.latAt_record D _ h.toLawsCore (GlobalTheory.RunIn.gamAt_of_lawsCore' D _ h.toLawsCore) large₂ H.CA hA j ka _
    (recPJ h j hj) S wL wF hK sK hH2, sK, hH2⟩

theorem ownAt_pos (D : D7) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) : 0 < ownAt D v := by
  unfold ownAt
  split_ifs
  · exact D.host.pde'_prime.pos
  · exact D.host.pde_prime.pos

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem leaves_sup_span_data : ∀ CK : ℝ, ∃ x₁ : ℝ, ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie J R κ v₀) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (EX : ErrX D) (r : TwoRuns J G) (c : OnConst) (O : OnObj ((R.toCx F).data F.cr false) (Mir R) c), IsRec Tp hK EX F fw r O → CoreTies L EX J R → OwnPin r → PageNum Tp x₁ → RunsHold Tp hK EX CK r → R.IsGrp F → R.tup_mu_conj → R.tup_mu_off → R.tup_mu_ne → LeafSup O ∧ LeafSpan O ∧ LeafLemmaS O ∧ LeafData O := by
  intro CK
  refine ⟨0, ?_⟩
  intro D G _ _ Pl0 T0 A J inst R F κ v₀ fw L Pm Tp hK EX r c O hrec _ _ _ hrun hgrp _ _ _
  obtain rfl : κ = fun i : Fin D.R.m => kaR Tp hK ((i : ℕ) + 1) := funext hrec.kap
  obtain ⟨hc, hinj, z, act, y, ht⟩ := hrec.tied
  have hok := hrec.ok
  have h3 : LeafSup O ∧ LeafSpan O ∧ LeafLemmaS O := by
    refine leaves_sup_span_lemmaS_of_formTieK GlobalTheory.chartIndependence_unconditional D L Pm Tp hK hinj EX _ _ _ _ _ c O
      fun v i => ?_
    letI : Algebra (r.used v).full.J.Q.c.F D.what₂.LL := inst
    obtain ⟨a1, a2, a3⟩ := lat_span_of_hypC _ _ (hrun v (hok.laws v).p hinj _ (inR_succ i)).1
    exact ⟨(r.used v).full, (hok.laws v).p, _, inR_succ i, ownAt D v, inst, z i, act i, fun g => r.lev i (mirIncl R g),
      (ht v i).1.toFormTieK, (ht v i).1.act_eq, hok.laws v, hok.xiRat v i, hok.cover v i, ownAt_pos D v, a1, a2, a3⟩
  refine ⟨h3.1, h3.2.1, h3.2.2, ?_⟩
  have hU : ∀ g, g ∈ F.P0 ↔ ∀ PP : R.Pg, R.eG g PP ∈ unip (kP PP.1) D.R.r := fun g => by
    rw [GlobalTheory.OntoChain.mem_base_iff hgrp.levels]
    refine Iff.trans ?_ ((mem_pi_unip_iff R (R.eG g)).symm.trans ⟨fun H PP => H PP (Set.mem_univ _), fun H PP _ => H PP⟩)
    refine exists_congr fun u => and_congr_right fun _ => ?_
    rw [← eG_mirIncl, R.eG.injective.eq_iff]
  have key : ∀ v (i : Fin D.R.m), GlobalTheory.TraceLattice.TiedAt A hinj EX O (mirIncl R) F.P0 F.ψ0⁻¹
      (fun _ _ _ _ _ _ _ _ _ => True) v i := fun v i =>
    ⟨(r.used v).full, inst, R, _, v₀, (hok.laws v).p, fw, ownAt D v, i, _, _, _, z i, act i, r.lev i, 1, y v i,
      (ht v i).1, hok.laws v, hok.xiRat v i, kaWt_n _ _ _ _, GlobalTheory.TraceLattice.kaR_lastPos Tp hK (inR_succ i),
      @GlobalTheory.TraceLattice.detOneOn_of_pins D G _ _ _ _ A (r.used v).full inst R i (hok.laws v) _ (hok.level v i) hok.half _ hU,
      trivial⟩
  exact GlobalTheory.TraceLattice.leafData_of_onTie_of_leafSpan h3.2.1 fun w _ => ⟨key w, key _⟩

end GlobalTheory.BigOn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftFormsFramesMajorantNormEqPetersson
section
open NumberField Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Cx GlobalTheory.CovTop

noncomputable section

namespace GlobalTheory.FrameRead

theorem normAt_eq_sqrt {K : Type} [Field K] [NumberField K] {n : ℕ} (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)
    (v : InfinitePlace K) (x : Fin n → K) :
    Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) X v x = Real.sqrt (Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v x x).re := by
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.majAt Formalism.HermitianLatticesTheory.cnorm
  congr 1
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show star (Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K (Fin n)) X v x i) = (starRingEnd ℂ) (Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K (Fin n)) X v x i) from rfl,
    Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

theorem frames_read : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (b : Bool)
    (i : Fin D.R.m), (R.toCx3 F).KForm b →
    (∀ v, IsUnit ((R.toCx3 F).XW b i v).det) ∧
      ∀ v (c : Fin (Module.finrank D.what₂.LL (R.toRealDat.WL F.lv2 b i)) → D.what₂.LL),
        Formalism.HermitianLatticesTheory.normAt (Pi.basisFun D.what₂.LL _) ((R.toCx3 F).XW b i) v c =
          (Real.sqrt (RealDat.nP F.lv2 b))⁻¹ * nrmR R.toRealDat i v.embedding (∑ k, c k • R.toRealDat.bL F.lv2 b i k) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F b i hK
  refine ⟨fun v => frame_gram_unit _ (hK i v).1, fun v c => ?_⟩
  have h1 := normAt_eq_sqrt (n := (R.toCx3 F).dW b i) ((R.toCx3 F).XW b i) v c
  have h2 := majAt_gram ((R.toCx3 F).XW b i) v ((R.toCx3 F).bW b i v) (hK i v).1 rfl c c
  refine h1.trans ?_
  have h3 : ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (z : E), Real.sqrt (inner ℂ z z).re = ‖z‖ := by
    intro E _ _ z
    rw [show (inner ℂ z z).re = ‖z‖ ^ 2 from inner_self_eq_norm_sq (𝕜 := ℂ) z, Real.sqrt_sq (norm_nonneg _)]
  rw [h2, h3]
  set s := twAt D.what₂.embLL v
  set σ := sgAt D.what₂.embLL v
  have hl : lin ((R.toCx3 F).bW b i v) (cpt v.embedding c) =
      Tw.mk s (∑ k, σ (c k) • (⟨R.toRealDat.bC F.lv2 b i σ k, Submodule.subset_span ⟨k, rfl⟩⟩ :
        R.toRealDat.WS F.lv2 b i σ)) := by
    rw [lin_apply]
    have e : ∀ x : ↥(R.toRealDat.WS F.lv2 b i σ), Tw.mk s x = Tw.mkL s ↥(R.toRealDat.WS F.lv2 b i σ) x := fun _ => rfl
    rw [e, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smulₛₗ]
    show v.embedding (c k) • _ = _
    rw [emb_eq D.what₂.embLL v (c k)]
    rfl
  rw [hl]
  have hc : (((∑ k, σ (c k) • (⟨R.toRealDat.bC F.lv2 b i σ k, Submodule.subset_span ⟨k, rfl⟩⟩ :
        R.toRealDat.WS F.lv2 b i σ)) : R.toRealDat.WS F.lv2 b i σ) : (R.HW i σ).H) =
      (((Real.sqrt (RealDat.nP F.lv2 b))⁻¹ : ℝ) : ℂ) • (R.FW i).j σ (∑ k, c k • R.toRealDat.bL F.lv2 b i k) := by
    rw [Submodule.coe_sum]
    simp only [Submodule.coe_smul, RealDat.bC]
    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smulₛₗ, smul_comm]
  calc ‖Tw.mk s (∑ k, σ (c k) • (⟨R.toRealDat.bC F.lv2 b i σ k, Submodule.subset_span ⟨k, rfl⟩⟩ :
        R.toRealDat.WS F.lv2 b i σ))‖
      = ‖(((∑ k, σ (c k) • (⟨R.toRealDat.bC F.lv2 b i σ k, Submodule.subset_span ⟨k, rfl⟩⟩ :
        R.toRealDat.WS F.lv2 b i σ)) : R.toRealDat.WS F.lv2 b i σ) : (R.HW i σ).H)‖ := rfl
    _ = _ := by
      rw [hc, norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
      unfold nrmR
      rw [InfinitePlace.mk_embedding]

end GlobalTheory.FrameRead
end
end

