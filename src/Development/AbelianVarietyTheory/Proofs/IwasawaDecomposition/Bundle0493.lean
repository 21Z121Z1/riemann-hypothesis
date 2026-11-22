import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeLayerTrueColumnsSizeFree
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0028
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0471
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiAtCongInvariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0481
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0158
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0106
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ExistsIntegralMulOrderElement
import Formalism.LocalToGlobal.Columns.Bundle0016
import Formalism.LocalToGlobal.Columns.DecoFin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0397
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0453
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0421
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0424
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0482
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0473
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
import Formalism.LocalToGlobal.Columns.Bundle0035
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0027
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0475
import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
import Formalism.UnipotentAdelicQuotients.Bundle0002
import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0082
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0122
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0483
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCutQGrp
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0021
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0404
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryFiniteAdelicPointAsMatrixMemFlagIwahori
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0484
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeLayerTrueColumnsParametersFreeStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeLayer_trueColumns_intrinsic : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    (∃ c : ℕ, (∀ u, Formalism.L2.G.CloudBound (w.D Z) u c) ∧
      ∀ L : SizeData₂ (w.D Z), L.sc = K.s → Val K.C K.cD K.ch L → (c : ℝ) ≤ G.cG L) →
    ∃ (vOf : ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
        G.HH (w.D Z) → Fin ((w.D Z).gat u v hg).P.nV)
      (Fl : ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
        G.Fills ((w.D Z).gat u v hg)),
      (∀ u v hg, (Fl u v hg).t = (w.D Z).R.t ∧ (Fl u v hg).mm = (w.D Z).R.m) ∧
      (∀ u v hg (x : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' x)), ∀ j ∈ SizeData₂.lifts (w.D Z),
        ((Fl u v hg).w x j s : ℝ) = wj (w.D Z) j (t.Gt.gat_pos u v hg ⟨x, s⟩) - G.kaJ (w.D Z) j) ∧
      ∀ (Lv : ∀ u v hg, G.Levels (Fl u v hg)) (Ch : ∀ u v hg, G.Chain (Lv u v hg))
        (Vram : ∀ u v hg, Submodule ((w.D Z).gat u v hg).O ((w.D Z).gat u v hg).Fn)
        (L : SizeData₂ (w.D Z)), L.sc = K.s → WtEq L K.a K.b → Val K.C K.cD K.ch L → ∀ X : G.Inst (w.D Z) L, CanonInst X →
        G.EpDef X K.C.cX.Ce → G.KapIDef X K.C.GK → (∀ v, G.ParametersFill X K.C.GK v) →
        G.LatTied t.Gt X ⟨vOf, Fl, Lv, Ch, Vram⟩ := by
  first | exact @GlobalTheory.Mem.Top.Bl.latLayer_free | exact GlobalTheory.Mem.Top.Bl.latLayer_free | (intros; apply GlobalTheory.Mem.Top.Bl.latLayer_free <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevQOfCongE
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT

theorem levQ_of_congE {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
    {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
    {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}
    (hL : L.Ok Ch sel mu cst G m2) (j : ℕ) (hj : j < R.m) (b : L.β j) (P : rowSG Pr sel mu)
    (hP : P.1 ∈ QE sel (mu : Chr X.F X.E X.K)) (g : Formalism.L2.Col.GLint X.E (R.N j) P.1)
    (h1 : ∀ x ∈ stdAt X.E (R.N j) P.1, ((qOf P.1 ^ cst.D P : ℕ) : X.E)⁻¹ • (g.1 x - x) ∈ stdAt X.E (R.N j) P.1) :
    ∃ h : g ∈ (L.levQ j b ⟨P.1, hP⟩).H, (L.levQ j b ⟨P.1, hP⟩).lam ⟨g, h⟩ = 1 := by
  have m := GlobalTheory.TwU.MidIndep.extE_cong_mem hL j hj b P g.1 h1
    (GlobalTheory.TwU.MidIndep.cong_inv P.1 _ _ (hL.cst_ok.D_pos P) g.1 h1)
  have hx := GlobalTheory.CongLevel.extE_inX (cOf R j) g.1
  have hmem : g ∈ (L.levQ j b ⟨P.1, hP⟩).H := by
    rw [hL.grpQ j b ⟨P.1, hP⟩, Subgroup.mem_subgroupOf]
    exact ⟨_, m.1, hx⟩
  refine ⟨hmem, Units.ext ?_⟩
  rw [hL.chrQ j b ⟨P.1, hP⟩ ⟨g, hmem⟩ _ m.1 hx]
  exact m.2

theorem levQ_deep : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (a : I.ι) (j : ℕ), j < B.R.m → ∀ (b : (I.idx a).β j) (P : SBof I a) (hP : P.1 ∈ I.Q a) (g : Formalism.L2.Col.GLint B.fields.E (B.R.N j) P.1), CongE P.1 ((I.cst a).D P) g.1 1 → ∃ h : g ∈ ((I.idx a).levQ j b ⟨P.1, hP⟩).H, ((I.idx a).levQ j b ⟨P.1, hP⟩).lam ⟨g, h⟩ = 1 := by
  intro B X I hOk a j hj b P hP g hg
  refine levQ_of_congE (hOk.idx_ok a) j hj b P hP g fun x hx => ?_
  rw [Nat.cast_pow]
  exact hg x hx

end GlobalTheory.Mem.Col2.AdT

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimePrimesNotOverBadPrimePlaceStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelPrime_primes_not_over_bad_prime_place : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (a : I.ι) (P : SBof I a) (v : HeightOneSpectrum (𝓞 B.host.F)), Formalism.L2.Col.IsOver v P.1 → ∀ (u : B.Word), ∀ P' ∈ (B.primes X).vT u, ¬ Formalism.L2.Col.IsOver v P' := by
  first | exact @GlobalTheory.Mem.Col2.AdT.vT_notOver_SBof | exact GlobalTheory.Mem.Col2.AdT.vT_notOver_SBof | (intros; apply GlobalTheory.Mem.Col2.AdT.vT_notOver_SBof <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelUnipotentGenericCharTypePlace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TypeLevelUni

@[reducible] def unitsDiv : DivisibleBy (Additive ℂˣ) ℤ where
  div a n := if n = 0 then 0 else
    Additive.ofMul (Units.mk0 (Complex.exp (Complex.log ((Additive.toMul a : ℂˣ) : ℂ) / n)) (Complex.exp_ne_zero _))
  div_zero a := if_pos rfl
  div_cancel {n} a hn := by
    rw [if_neg hn]
    apply Additive.toMul.injective
    rw [toMul_zsmul, toMul_ofMul]
    ext
    rw [Units.val_zpow_eq_zpow_val, Units.val_mk0, ← Complex.exp_int_mul,
      mul_div_cancel₀ _ (Int.cast_ne_zero.mpr hn), Complex.exp_log (Units.ne_zero _)]

def charUnit {A : Type} [AddCommGroup A] (ψ : AddChar A ℂ) (x : A) : ℂˣ :=
  ⟨ψ x, ψ (-x), by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one],
    by rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]⟩

theorem addChar_extend {K : Type} [Ring K] (S : Subring K) (ψ : AddChar S ℂ) :
    ∃ ψ₀ : AddChar K ℂ, ∀ x : S, ψ₀ x = ψ x := by
  let _ := unitsDiv
  let g : S →ₗ[ℤ] Additive ℂˣ := AddMonoidHom.toIntLinearMap
    { toFun := fun x => Additive.ofMul (charUnit ψ x)
      map_zero' := by
        apply Additive.toMul.injective
        ext
        simp [charUnit, AddChar.map_zero_eq_one]
      map_add' := fun x y => by
        apply Additive.toMul.injective
        ext
        simp [charUnit, AddChar.map_add_eq_mul] }
  let f : S →ₗ[ℤ] K := (S.subtype : S →+* K).toAddMonoidHom.toIntLinearMap
  obtain ⟨h, hh⟩ := (Module.Baer.of_divisible (Additive ℂˣ)).extension_property f Subtype.val_injective g
  refine ⟨{ toFun := fun x => ((Additive.toMul (h x) : ℂˣ) : ℂ)
            map_zero_eq_one' := by simp
            map_add_eq_mul' := fun x y => by simp [map_add] }, fun x => ?_⟩
  have e := congrArg (fun φ => ((Additive.toMul (φ x) : ℂˣ) : ℂ)) hh
  simpa [f, g, charUnit] using e

theorem exists_localAddChar_lifting_residueChar : ∀ (D : D7) (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (φ : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* kP s.w), Function.Surjective φ → (∀ x, φ x = 0 ↔ Valued.v (x : s.v.adicCompletion (maximalRealSubfield D.host.E)) < 1) → ∀ ψ' : AddChar (kP s.w) ℂ, ψ' ≠ 1 → ∃ ψ₀ : AddChar (s.v.adicCompletion (maximalRealSubfield D.host.E)) ℂ, NG.IsPsi0 s ψ₀ ∧ ∀ x : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E), ψ₀ (x : s.v.adicCompletion (maximalRealSubfield D.host.E)) = ψ' (φ x) := by
  intro D s φ hφs hφ0 ψ' hne
  obtain ⟨ψ₀, h⟩ := addChar_extend (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)).toSubring
    (ψ'.compAddMonoidHom φ.toAddMonoidHom)
  refine ⟨ψ₀, ⟨fun x hx => ?_, ?_⟩, fun x => h x⟩
  · have hx1 : x ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) :=
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hx.le
    have e1 := h ⟨x, hx1⟩
    have e2 : φ ⟨x, hx1⟩ = 0 := (hφ0 ⟨x, hx1⟩).2 hx
    rw [show ψ₀ x = ψ₀ ((⟨x, hx1⟩ : (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)).toSubring) :
      s.v.adicCompletion (maximalRealSubfield D.host.E)) from rfl, e1]
    show ψ' (φ ⟨x, hx1⟩) = 1
    rw [e2, AddChar.map_zero_eq_one]
  · obtain ⟨y, hy⟩ : ∃ y, ψ' y ≠ 1 := by
      by_contra hc
      push_neg at hc
      apply hne
      ext y
      rw [hc y, AddChar.one_apply]
    obtain ⟨x, rfl⟩ := hφs y
    refine ⟨x, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 x.2, ?_⟩
    have e1 := h x
    rw [show ψ₀ (x : s.v.adicCompletion (maximalRealSubfield D.host.E)) =
      ψ₀ ((x : (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)).toSubring) :
        s.v.adicCompletion (maximalRealSubfield D.host.E)) from rfl, e1]
    exact hy

theorem levelUni_typePlace : ∀ (D : D7) (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 → (∀ PP, PP ∈ L.Pg ↔ ∃ k v, PP = D.naut.plGw k v) → ∀ (i : Fin D.R.m) (t : T) (hr : D.R.r ≤ D.R.nV) (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ), IsGenericPsi L.Pg ψ → ∀ s : ReciprocityTheory.Aut.SplitPlace D.host.E, s.w ∈ L.Pg → ∃ (ψ₀ : AddChar (s.v.adicCompletion (maximalRealSubfield D.host.E)) ℂ) (ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), NG.IsPsi0 s ψ₀ ∧ NG.IsCompAt (L.C.mu0 i * L.xiH t) s ξ ∧ NG.LevelUni (stdJ (datV D D.R.nV hr L.Pg (L.Q t) (P0 L.Pg D.R.r ψ) (L.chi ((i : ℕ) + 1)) (L.xiR t))) (stdX (datV D D.R.nV hr L.Pg (L.Q t) (P0 L.Pg D.R.r ψ) (L.chi ((i : ℕ) + 1)) (L.xiR t))) s D.R.r ψ₀ ξ := by
  intro D T L μ0 hL hPg i t hr ψ hψ s hs
  obtain ⟨-, -, -, h4⟩ := GlobalTheory.T.stdMaximalCompact_reduction_properties D D.R.nV
  obtain ⟨φ, hφs, hφ0, hφa, hφk⟩ := h4 s
  obtain ⟨hoffG, hoffQ, -, hunr⟩ := GlobalTheory.T.typePlace_levelPlaces_distinct_underlying D T L μ0 hL hPg t s hs
  let ψ' : AddChar (kP s.w) ℂ := (ψ s.w).compAddMonoidHom (negAddMonoidHom)
  have hne : ψ' ≠ 1 := by
    intro h1
    apply hψ s.w hs
    ext y
    have := congrArg (fun f : AddChar (kP s.w) ℂ => f (-y)) h1
    simpa [ψ'] using this
  obtain ⟨ψ₀, hP0, hψ₀⟩ := exists_localAddChar_lifting_residueChar D s φ hφs hφ0 ψ' hne
  have hres : IsRes (L.C.mu0 i * L.xiH t) s.w (L.chi ((i : ℕ) + 1) s.w)⁻¹ := by
    intro a k u hk hu
    have h1 := hL.chi i s.w hs a k u hk hu
    have ha : a ∉ s.w.asIdeal := by
      intro hm
      have : (u : kP s.w) = 0 := by rw [hu]; exact Ideal.Quotient.eq_zero_iff_mem.2 hm
      exact u.ne_zero this
    have hunit : IsUnitAt s.w (atFin s.w k) := by
      have e := GlobalTheory.ChainOnto.TameRes.val_alg s.w (k : D.host.E)
      show Valued.v (algebraMap D.host.E (s.w.adicCompletion D.host.E) (k : D.host.E)) = 1
      rw [e, hk]
      exact GlobalTheory.ChainOnto.TameRes.valuation_eq_one_of_not_mem s.w a ha
    have h2 : (L.xiH t).locK s.w k = 1 := hunr _ hunit
    have e : (L.C.mu0 i * L.xiH t).locK s.w k = (L.C.mu0 i).locK s.w k * (L.xiH t).locK s.w k := rfl
    rw [e, h2, mul_one]
    exact h1
  obtain ⟨ξ, hξc, hξr⟩ := GlobalTheory.T.exists_splitPlaceComponent_heckeChar_residue D s φ hφs hφ0 hφa _ _ hres
  refine ⟨ψ₀, ξ, hP0, hξc, ⟨GlobalTheory.T.split_place_residue_map_unit_character D hr L.Pg (L.Q t) ψ (L.chi ((i : ℕ) + 1)) (L.xiR t) s φ hφ0 hφk hs hoffG hoffQ, ?_⟩⟩
  intro κ h hκ u hu
  refine GlobalTheory.T.stdFrameLevelCharacter_at_typePlace_eq D hr L.Pg (L.Q t) ψ (L.chi ((i : ℕ) + 1)) (L.xiR t) s φ hφ0 hφk hs hoffG hoffQ ψ₀ ξ ?_ hξr κ h hκ u hu
  intro x
  rw [hψ₀ x]
  rfl

end GlobalTheory.TypeLevelUni

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftLevelTypeTrivialSplitPlaceSupportStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftLevelType_trivial_splitPlaceSupport : ∀ (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (hI : I.Ok) (hV : ValsIn I) (hL : LevOf X I U L) (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (x : (famR X I hX U Xg tr).A.ok t × ℕ) (j : (envL X I hX U Xg tr L cV i t).lev.J) (hj : (envL X I hX U Xg tr L cV i t).isLoc x j),
    (envL X I hX U Xg tr L cV i t).lev.χ j = 1 := by
  first | exact @GlobalTheory.Mem.R3.LiftBrg.SplitChi.chi_loc_lift | exact GlobalTheory.Mem.R3.LiftBrg.SplitChi.chi_loc_lift | (intros; apply GlobalTheory.Mem.R3.LiftBrg.SplitChi.chi_loc_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalBasisAndEmbeddedBasisDifferByUnimodularInte
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.LocBasisBasR

open Matrix

theorem norm_det_le_one {K : Type*} [NormedField K] [IsUltrametricDist K] {N : ℕ}
    (g : Matrix (Fin N) (Fin N) K) (hg : ∀ a b, ‖g a b‖ ≤ 1) : ‖g.det‖ ≤ 1 := by
  rw [Matrix.det_apply']
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_
  have hs : ‖(((Equiv.Perm.sign σ : ℤˣ) : ℤ) : K)‖ ≤ 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  rw [norm_mul, norm_prod]
  exact mul_le_one₀ hs (Finset.prod_nonneg fun _ _ => norm_nonneg _) (Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => hg _ _)

theorem main : ∀ (D : D7) {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (Bm : GL (Fin N) D.host.E) (M : Matrix (Fin N) (Fin N) ℂ_[p]), Formalism.L2.Forms.IsLocBasis p (L : Set (Fin N → D.host.E)) Bm → GL3Columns.BasR D lam τ L M → ∃ g : Matrix (Fin N) (Fin N) ℂ_[p], (∀ a b, ‖g a b‖ ≤ 1) ∧ ‖g.det‖ = 1 ∧ M = (Bm : Matrix (Fin N) (Fin N) D.host.E).map (TaylorLogMetric.tauEmb D lam τ) * g := by
  intro D p _ lam τ N L Bm M hL hM
  obtain ⟨ρ, hρ⟩ := GlobalTheory.JetTieCompare.exists_tauHom D lam τ
  have hp : p.Prime := Fact.out
  have hns : ∀ s : ℕ, ¬ p ∣ s → ‖ρ (s : D.host.E)‖ = 1 := fun s hs => by
    rw [map_natCast]; exact GlobalTheory.KapSplitNorm.norm_natCast_eq_one p s hs
  set A : Matrix (Fin N) (Fin N) ℂ_[p] := (Bm : Matrix (Fin N) (Fin N) D.host.E).map ρ with hAdef
  set Ai : Matrix (Fin N) (Fin N) ℂ_[p] := ((Bm⁻¹ : GL (Fin N) D.host.E) : Matrix (Fin N) (Fin N) D.host.E).map ρ with hAidef
  have hAAi : A * Ai = 1 := by
    rw [hAdef, hAidef, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero ρ) (map_one ρ)]
  have hAiA : Ai * A = 1 := by
    rw [hAdef, hAidef, ← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero ρ) (map_one ρ)]
  have hMu : IsUnit M.det := Ne.isUnit hM.1

  have hcoord : ∀ x ∈ L, ∀ a, ‖(Ai *ᵥ fun i => ρ (x i)) a‖ ≤ 1 := by
    intro x hx a
    obtain ⟨s, hs, hint⟩ := (hL x).1 ⟨1, hp.not_dvd_one, by simpa using hx⟩
    obtain ⟨c, hc⟩ := hint a
    have e : (Ai *ᵥ fun i => ρ (x i)) a = ρ ((((Bm⁻¹ : GL (Fin N) D.host.E) : Matrix (Fin N) (Fin N) D.host.E) *ᵥ x) a) := by
      rw [RingHom.map_mulVec]; rfl
    have hs1 := hns s hs
    have hs0 : ρ (s : D.host.E) ≠ 0 := by intro h; rw [h, norm_zero] at hs1; exact zero_ne_one hs1
    have e2 : ρ ((((Bm⁻¹ : GL (Fin N) D.host.E) : Matrix (Fin N) (Fin N) D.host.E) *ᵥ x) a) =
        (ρ (s : D.host.E))⁻¹ * ρ (algebraMap (𝓞 D.host.E) D.host.E c) := by
      rw [hc, map_mul]; field_simp
    rw [e, e2, norm_mul, norm_inv, hs1, inv_one, one_mul]
    exact GlobalTheory.JetTieCompare.norm_int_le ρ c
  have hg : ∀ a b, ‖(Ai * M) a b‖ ≤ 1 := by
    intro a b
    obtain ⟨n, r, x, hr, hx, hcol⟩ := hM.2.2 b
    have : (Ai * M) a b = ∑ k, r k * (Ai *ᵥ fun i => ρ (x k i)) a := by
      simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, hcol, hρ, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring
    rw [this]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
    rw [norm_mul]
    exact mul_le_one₀ (hr k) (norm_nonneg _) (hcoord _ (hx k) a)
  refine ⟨Ai * M, hg, ?_, ?_⟩
  · have hh : ∀ b a, ‖(M⁻¹ * A) b a‖ ≤ 1 := by
      intro b a
      let x : Fin N → D.host.E := fun j => (Bm : Matrix (Fin N) (Fin N) D.host.E) j a
      have hxe : x = (Bm : Matrix (Fin N) (Fin N) D.host.E) *ᵥ Pi.single a 1 := by
        funext j; simp [x, Matrix.mulVec_single]
      have hrhs : ∃ s : ℕ, ¬ p ∣ s ∧ ∀ c, (s : D.host.E) *
          (((Bm⁻¹ : GL (Fin N) D.host.E) : Matrix (Fin N) (Fin N) D.host.E) *ᵥ x) c ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
        refine ⟨1, hp.not_dvd_one, fun c => ?_⟩
        rw [hxe, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec,
          Nat.cast_one, one_mul, Pi.single_apply]
        split_ifs
        · exact ⟨1, map_one _⟩
        · exact ⟨0, map_zero _⟩
      obtain ⟨s, hs, hmem⟩ := (hL x).2 hrhs
      have h := hM.2.1 _ hmem b
      rw [hρ] at h
      have e : (fun j => ρ (((s : D.host.E) • x) j)) = ρ (s : D.host.E) • fun j => ρ (x j) := by
        funext j
        change ρ ((s : D.host.E) * x j) = ρ (s : D.host.E) * ρ (x j)
        rw [map_mul]
      rw [e, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, norm_mul, hns s hs, one_mul] at h
      convert h using 2
      simp [A, x, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    have hprod : (Ai * M) * (M⁻¹ * A) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc M, Matrix.mul_nonsing_inv _ hMu, Matrix.one_mul, hAiA]
    have hd := congrArg Matrix.det hprod
    rw [Matrix.det_mul, Matrix.det_one] at hd
    have hn := congrArg norm hd
    rw [norm_mul, norm_one] at hn
    have h1 := norm_det_le_one _ hg
    have h2 := norm_det_le_one _ (fun b a => hh b a)
    by_contra hne
    have hlt : ‖(Ai * M).det‖ < 1 := lt_of_le_of_ne h1 hne
    have : ‖(Ai * M).det‖ * ‖(M⁻¹ * A).det‖ < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) h2) hlt
    linarith
  · rw [hρ, ← Matrix.mul_assoc]
    change M = A * Ai * M
    rw [hAAi, Matrix.one_mul]

end GlobalTheory.LocBasisBasR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalConstantWeilCharacterValuesIsIntegralStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localConstantWeilCharacter_values_isIntegral : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → I.IsTw → ∀ (a : I.ι) (P : SBof I a) (x : B.fields.E), IsIntegral ℤ ((I.cst a).psi P x) := by
  first | exact @GlobalTheory.Mem.Col2.AdT.psi_isIntegral | exact GlobalTheory.Mem.Col2.AdT.psi_isIntegral | (intros; apply GlobalTheory.Mem.Col2.AdT.psi_isIntegral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalLevelCharacterFiniteOrderStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localLevelCharacter_finiteOrder : ∀ {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} [NeZero n] {Q : Finset (Pl E)} (Θ : LevQFam E K n Q) (hQ : ∀ P : Q, conjPrime₂ P.1 ≠ P.1) (hΘ : ThetaOpen Θ) (P : Q), ∃ m : ℕ, 0 < m ∧ ∀ k, (qbLoc hc Θ hQ hΘ).chr P k ^ m = 1 := by
  first | exact @GlobalTheory.Mem.Col2.ChEx.qbLoc_chr_exp | exact GlobalTheory.Mem.Col2.ChEx.qbLoc_chr_exp | (intros; apply GlobalTheory.Mem.Col2.ChEx.qbLoc_chr_exp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemRowLevelOfReductionMemLevelGroup
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.RowDeco
open GlobalTheory.Mem.R3.RowAd

theorem reindex_symm_reindex {κ : Type} [CommRing κ] {a b : ℕ} (e : Fin a ≃ Fin b) (y : GL (Fin a) κ) :
    Units.map (Matrix.reindexAlgEquiv κ κ e.symm).toMonoidHom (Units.map (Matrix.reindexAlgEquiv κ κ e).toMonoidHom y) = y := by
  apply Units.ext
  ext i j
  simp [Matrix.reindexAlgEquiv_apply]

theorem of_reindex_mem_HK {κ : Type} [CommRing κ] {a n r t m : ℕ} (h : a = n) (hn : n = r + m * t) (hra : r ≤ a)
    (y : GL (Fin a) κ)
    (hy : Units.map (Matrix.reindexAlgEquiv κ κ (finCongr h)).toMonoidHom y ∈ Formalism.L2.Col.HK n κ r (List.replicate m t)) :
    y ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) ∧ Formalism.L2.DIV.upperLeftBlock hra y = 1 := by
  subst h
  rw [reindex_finCongr_rfl] at hy
  obtain ⟨hUT, h1⟩ := Formalism.L2.Col.mem_HK.1 hy
  have hb : y ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) := by
    intro i j hij
    refine hUT (show Formalism.L2.Col.coarse r (List.replicate m t) j.val < Formalism.L2.Col.coarse r (List.replicate m t) i.val from ?_)
    rw [coarse_eq_blkOf hn, coarse_eq_blkOf hn]
    exact hij
  refine ⟨hb, ?_⟩
  apply Units.ext
  rw [Formalism.L2.DIV.upper_block_val_submatrix hra (Formalism.L2.DIV.blockTri_blkOf_le r t hb), Units.val_one]
  ext i j
  rw [Matrix.submatrix_apply, h1 _ _ i.2 j.2]
  simp [Matrix.one_apply, Fin.ext_iff]

theorem of_reindex_mem_HQ {κ : Type} [CommRing κ] {a n r b : ℕ} (h : a = n) (hn : n = r + b) (y : GL (Fin a) κ)
    (hy : Units.map (Matrix.reindexAlgEquiv κ κ (finCongr h)).toMonoidHom y ∈ Formalism.L2.Col.blockUT n κ r [b]) :
    y ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) := by
  subst h
  rw [reindex_finCongr_rfl] at hy
  intro i j hij
  refine hy (show Formalism.L2.Col.coarse r [b] j.val < Formalism.L2.Col.coarse r [b] i.val from ?_)
  rw [coarseBlockIndex_eq_twoBlock hn, coarseBlockIndex_eq_twoBlock hn]
  exact hij

theorem redG_ptE_of (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) {U : Set I.ι}
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (hL : LevOf X I U L) (t : TupU I U) (h : Bridge.Gf X.toD7.sp.X')
    (hSt : Formalism.UG.bc (swapAE X.toD7) ((h : Bridge.Gf X.toD7.sp.X') : GL _ _) ∈ Formalism.L2.DIV.St L.βX)
    (hz : ptE X h ∈ Formalism.L2.Col.J0 X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅)
    (w : Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) :
    Formalism.L2.Col.redG X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ⟨_, hz⟩ w =
      Units.map (Matrix.reindexAlgEquiv (Formalism.L2.DIV.kP w.1) (Formalism.L2.DIV.kP w.1) (finCongr (rank_X' X))).toMonoidHom
        (Formalism.L2.DIV.redFn L.βX w.1 (Formalism.UG.bc (swapAE X.toD7) ((h : Bridge.Gf X.toD7.sp.X') : GL _ _))) :=
  redAt_reindex (finCongr (rank_X' X)) L.βX hL.beta.2 _ hSt (Formalism.L2.Col.congruence_subgroup_le_stabilizer _ _ _ hz) w.1

set_option maxHeartbeats 1000000 in

theorem mem_J_of_redG_mem_grp : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)), I.Ok → LevOf X I U L →
    ∀ (t : TupU I U) (h : Bridge.Gf X.toD7.sp.X') (hz : RowAd.ptE X h ∈ Formalism.L2.Col.J0 X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅),
      Formalism.L2.Col.redG X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ⟨_, hz⟩ ∈
        ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp →
      h ∈ (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J := by
  intro X px I U L hI hL t h hz hred
  have hβ : L.βX = 1 := hL.beta.2
  have hSt : Formalism.UG.bc (swapAE X.toD7) ((h : Bridge.Gf X.toD7.sp.X') : GL _ _) ∈ Formalism.L2.DIV.St L.βX := by
    have h1 := reindex_mem_St_one (finCongr (rank_X' X)).symm (Formalism.L2.Col.congruence_subgroup_le_stabilizer _ _ _ hz)
    have e2 : Units.map (Matrix.reindexAlgEquiv (Formalism.IndefR.Lev.EAf X.toD7) (Formalism.IndefR.Lev.EAf X.toD7)
        (finCongr (rank_X' X)).symm).toMonoidHom (ptE X h) = Formalism.UG.bc (swapAE X.toD7) ((h : Bridge.Gf X.toD7.sp.X') : GL _ _) :=
      reindex_symm_reindex _ _
    rw [hβ]
    exact e2 ▸ h1
  have hUA : Formalism.UG.bc (swapAE X.toD7) ((h : Bridge.Gf X.toD7.sp.X') : GL _ _) ∈
      Formalism.L2.DIV.UA X.toD7.sp.cm X.toD7.sp.X'.gram := by
    obtain ⟨g, hg⟩ := h.2
    rw [← hg]
    exact GlobalTheory.LevSplit.finE_mem_UA X.toD7.sp.X' g
  have hw : ∀ w : Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1,
      Units.map (Matrix.reindexAlgEquiv (Formalism.L2.DIV.kP w.1) (Formalism.L2.DIV.kP w.1) (finCongr (rank_X' X))).toMonoidHom
        (Formalism.L2.DIV.redFn L.βX w.1 (Formalism.UG.bc (swapAE X.toD7) ((h : Bridge.Gf X.toD7.sp.X') : GL _ _))) ∈
        (Formalism.L2.Col.rowTyKK I.Ch I.sel t.1 w).H := fun w => by
    rw [← redG_ptE_of X I L hL t h hSt hz w]
    exact hred w (Set.mem_univ _)
  have hG : ∀ PP ∈ (L.datXt t).Pg,
      Formalism.L2.DIV.redFn L.βX PP (Formalism.UG.bc (swapAE X.toD7) ((h : Bridge.Gf X.toD7.sp.X') : GL _ _)) ∈
                Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf (L.datXt t).r (L.datXt t).t) ∧
        Formalism.L2.DIV.upperLeftBlock (L.datXt t).hr
          (Formalism.L2.DIV.redFn L.βX PP (Formalism.UG.bc (swapAE X.toD7) ((h : Bridge.Gf X.toD7.sp.X') : GL _ _))) = 1 := by
    intro PP hPP
    have hP : PP ∈ (X.B.primes px).vGs := by
      have hP' : PP ∈ L.Pg := hPP
      rw [hL.Pg] at hP'
      exact hP'
    have hm := hw ⟨PP, by classical exact Finset.mem_union_left _ hP⟩
    rw [Formalism.L2.Col.rowTyKK, Formalism.L2.Col.LevFam.glue_of_mem _ _ _ hP] at hm
    exact of_reindex_mem_HK (rank_X' X) (Formalism.L2.Col.rank_X'_eq X.B.R) (L.datXt t).hr _ hm
  have hQ : ∀ PP ∈ (L.datXt t).Q,
      Formalism.L2.DIV.redFn L.βX PP (Formalism.UG.bc (swapAE X.toD7) ((h : Bridge.Gf X.toD7.sp.X') : GL _ _)) ∈
        Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 (L.datXt t).r) := by
    intro PP hPP
    have hq : PP ∈ Formalism.L2.Col.QE I.sel (t.1 : Formalism.L2.DIV.Chr _ _ _) := by
      have hP' : PP ∈ L.Q t := hPP
      have e : I.Q (ixOf I U t) = Formalism.L2.Col.QE I.sel (t.1 : Formalism.L2.DIV.Chr _ _ _) := by
        simp only [ColIn.Q, tup_ixOf]
      rw [hL.Q t, e] at hP'
      exact hP'
    have hm := hw ⟨PP, by classical exact Finset.mem_union_right _ hq⟩
    by_cases hP : PP ∈ (X.B.primes px).vGs
    · rw [Formalism.L2.Col.rowTyKK, Formalism.L2.Col.LevFam.glue_of_mem _ _ _ hP] at hm
      exact Formalism.L2.DIV.blockTri_blkOf_le _ _
        (of_reindex_mem_HK (rank_X' X) (Formalism.L2.Col.rank_X'_eq X.B.R) (L.datXt t).hr _ hm).1
    · rw [Formalism.L2.Col.rowTyKK, Formalism.L2.Col.LevFam.glue_of_not _ _ _ hP] at hm
      exact of_reindex_mem_HQ (rank_X' X) (Formalism.L2.Col.rank_X'_eq X.B.R) _ hm
  exact ⟨Formalism.L2.DIV.mem_parLev.2 ⟨hUA, hSt, fun PP hP => (hG PP hP).1, hQ⟩,
    Subgroup.mem_bot.2 (funext fun PP => (hG PP.1 PP.2).2)⟩

end GlobalTheory.Mem.R3.RowDeco
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemberLevelPrimeNotUnderTwistPrimeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.memberLevelPrime_not_under_twistPrime : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → (B.primes X).Ok → ∀ (u : B.Word) (a : I.ι) (P : I.Q a), (B.T u : 𝓞 B.host.F) ∉ (qv B.host.F P.1).asIdeal := by
  first | exact @GlobalTheory.Mem.Col2.ChEx.T_notMem_qv | exact GlobalTheory.Mem.Col2.ChEx.T_notMem_qv | (intros; apply GlobalTheory.Mem.Col2.ChEx.T_notMem_qv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormalisedFamilySatisfiesEquivarianceLawsStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedFamily_satisfies_equivarianceLaws : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → B.EqP χ := by
  first | exact @GlobalTheory.Mem.NatEqui.eqP | exact GlobalTheory.Mem.NatEqui.eqP | (intros; apply GlobalTheory.Mem.NatEqui.eqP <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NumberFieldGLDenseInCompletionGLTwoSidedStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.numberFieldGL_dense_in_completionGL_two_sided : ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (n N : ℕ) (A : GL (Fin n) (P.adicCompletion E)), ∃ γ : GL (Fin n) E, ∀ r s, Valued.v (((A⁻¹).1 * γ.1.map (algebraMap E (P.adicCompletion E)) - 1) r s) ≤ WithZero.exp (-(N : ℤ)) ∧ Valued.v (((γ⁻¹).1.map (algebraMap E (P.adicCompletion E)) * A.1 - 1) r s) ≤ WithZero.exp (-(N : ℤ)) := by
  first | exact @GlobalTheory.DenseGL.dense_two_sided | exact GlobalTheory.DenseGL.dense_two_sided | (intros; apply GlobalTheory.DenseGL.dense_two_sided <;> assumption)
end

