import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVecMemOfFrame
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1702
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0101
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1680
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1703
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsGermGIffExistsFrame
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBTransport
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1583
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1623
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1688
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1681
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLevelCharacterEqProdSuperdiagonalSum
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level)
open GlobalTheory.LevDesc (TypeFrame IsTypeLevel typeRed)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters (Sq LevelGroup levelU psiU)
open GlobalTheory.LevPull (CongMod)
open scoped TensorProduct Matrix
noncomputable section

namespace GlobalTheory.TypeBase

def piCongrLeftMul {α β : Type} (P : β → Type) [∀ b, Mul (P b)] (e : α ≃ β) : (∀ a, P (e a)) ≃* ∀ b, P b :=
  { Equiv.piCongrLeft P e with
    map_mul' := fun f g => by
      funext b
      obtain ⟨a, rfl⟩ := e.surjective b
      simp only [Equiv.toFun_as_coe, Pi.mul_apply, Equiv.piCongrLeft_apply_apply] }

theorem piCongrLeftMul_apply {α β : Type} (P : β → Type) [∀ b, Mul (P b)] (e : α ≃ β) (f : ∀ a, P (e a)) (a : α) :
    piCongrLeftMul P e f (e a) = f a :=
  Equiv.piCongrLeft_apply_apply P e f a

def bcEquiv {A B : Type} [CommRing A] [CommRing B] {n : Type} [Fintype n] [DecidableEq n] (f : A ≃+* B) :
    GL n A ≃* GL n B :=
  MonoidHom.toMulEquiv (Formalism.UG.bc (f : A →+* B)) (Formalism.UG.bc (f.symm : B →+* A))
    (by ext g i j; simp [Formalism.UG.bc]) (by ext g i j; simp [Formalism.UG.bc])

theorem bc_apply {A B : Type} [CommRing A] [CommRing B] {n : Type} [Fintype n] [DecidableEq n] (f : A →+* B)
    (g : GL n A) (i j : n) : ((Formalism.UG.bc f g : GL n B) : Matrix n n B) i j = f ((g : Matrix n n A) i j) := rfl

theorem bc_mem_unip_iff {A B : Type} [Field A] [CommRing B] {r : ℕ} (f : A ≃+* B) (g : GL (Fin r) A) :
    Formalism.UG.bc (f : A →+* B) g ∈ unip B r ↔ g ∈ GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.unitri r A := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · have h := h1 (show j.val < i.val from hij)
      rw [bc_apply] at h
      exact f.injective (h.trans (map_zero f).symm)
    · have h := h2 i
      rw [bc_apply] at h
      exact f.injective (h.trans (map_one f).symm)
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [bc_apply, h1 (show id j < id i from hij), map_zero]
    · rw [bc_apply, h2 i, map_one]

theorem edgeSum_bc {A B : Type} [Field A] [CommRing B] {r : ℕ} (f : A →+* B) (g : GL (Fin r) A) :
    edgeSum supEdge (Formalism.UG.bc f g) = f (GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.superDiag (g : Matrix (Fin r) (Fin r) A)) := by
  simp only [edgeSum, GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.superDiag, supEdge, bc_apply, map_sum, apply_ite f, map_zero]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr

theorem det_unip {κ : Type} [CommRing κ] {r : ℕ} {g : GL (Fin r) κ} (hg : g ∈ unip κ r) :
    Matrix.GeneralLinearGroup.det g = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one,
    Matrix.det_of_upperTriangular (fun i j hij => hg.1 hij)]
  exact Finset.prod_eq_one fun i _ => hg.2 i

theorem exists_char {Ks : Type} [Field Ks] (σ : Ks →+* ℂ) (p : ℕ) [Fact p.Prime] {ζ : Ks} (hζ : IsPrimitiveRoot ζ p)
    {k : Type} [CommRing k] (f : ZMod p ≃+* k) (χ : AddChar k ℂ) :
    ∃ ψ : AddChar (ZMod p) Ks, ∀ x, σ (ψ x) = χ (f x) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hz : χ (f 1) ^ p = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, ← map_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_self, map_zero,
      AddChar.map_zero_eq_one]
  obtain ⟨k, -, hk⟩ := (hζ.map_of_injective σ.injective).eq_pow_of_pow_eq_one hz
  have hc : (ζ ^ k) ^ p = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  refine ⟨AddChar.zmodChar p hc, fun x => ?_⟩
  rw [AddChar.zmodChar_apply, map_pow, map_pow, hk, ← AddChar.map_nsmul_eq_pow, ← map_nsmul, nsmul_eq_mul, mul_one,
    ZMod.natCast_zmod_val]

theorem baseLevelCharacter_eq_prod_superdiagonalSum {E : Type} [Field E] [NumberField E] (Pg : Finset (Pl E)) (r : ℕ)
    (ψ : ∀ PP : Pl E, AddChar (kP PP) ℂ) (g) (hg : g ∈ (P0 Pg r ψ).H) :
    (((P0 Pg r ψ).chi ⟨g, hg⟩ : ℂˣ) : ℂ) = ∏ PP : Pg, ψ PP.1 (edgeSum supEdge (g PP)) := by
  unfold P0 LevelP.ofLocal
  dsimp only
  rw [MonoidHom.finset_prod_apply, Units.coe_prod]
  rfl

theorem mem_lastZeroOrthImageSubspace_iff {E : Type} [Field E] [NumberField E] {LL : Type} [CommRing LL] (Pg : Finset (Pl E)) (r : ℕ)
    (ψ : ∀ PP : Pl E, AddChar (kP PP) LL) (g : G0 Pg r) :
    g ∈ (P0 Pg r ψ).H ↔ ∀ PP, g PP ∈ unip (kP PP.1) r := by
  simp [P0, LevelP.ofLocal, Subgroup.mem_pi]

end GlobalTheory.TypeBase

namespace GlobalTheory.TypeBase

theorem base_level_unip_char : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.grp_levels F → R.grp_chiW → (∀ k, ∃ ζ : Ks, IsPrimitiveRoot ζ (D.host.g k)) → ∀ (e : Sq D.host ≃ R.Pg) (iso : ∀ v : Sq D.host, ZMod (D.host.g v.1) ≃+* kP (e v).1), ∃ (t : LevelGroup D.host ≃* G) (ψ : ∀ v : Sq D.host, AddChar (ZMod (D.host.g v.1)) Ks), (∀ u v, R.eG (t u) (e v) = Formalism.UG.bc (iso v : ZMod (D.host.g v.1) →+* kP (e v).1) (u v)) ∧ (∀ v, ψ v ≠ 1) ∧ (∀ u, t u ∈ (F.lvl false).P ↔ u ∈ levelU D.host) ∧ ∀ u (h : t u ∈ (F.lvl false).P), algebraMap Ks D.what₂.LL (psiU ψ u) = ((F.lvl false).ψ ⟨t u, h⟩ : D.what₂.LLˣ) ∧ ∀ i, (R.FW i).chi (t u) = 1 := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hlevels hchiW hζ e iso
  obtain ⟨ψ0, hgen, hlev, -⟩ := hlevels
  let φ : LevelGroup D.host ≃* G0 R.Pg D.R.r :=
    (MulEquiv.piCongrRight fun v : Sq D.host => (bcEquiv (n := Fin D.R.r) (iso v))).trans
      (piCongrLeftMul (fun PP : R.Pg => GL (Fin D.R.r) (kP PP.1)) e)
  have hφ : ∀ u v, φ u (e v) = Formalism.UG.bc (iso v : ZMod (D.host.g v.1) →+* kP (e v).1) (u v) := fun u v =>
    piCongrLeftMul_apply (fun PP : R.Pg => GL (Fin D.R.r) (kP PP.1)) e
      (fun v => Formalism.UG.bc (iso v : ZMod (D.host.g v.1) →+* kP (e v).1) (u v)) v
  have hex : ∀ v : Sq D.host, ∃ ψ : AddChar (ZMod (D.host.g v.1)) Ks,
      ∀ x, D.what₂.embLL (algebraMap Ks D.what₂.LL (ψ x)) = ψ0 (e v).1 (iso v x) := by
    intro v
    obtain ⟨ζ, hz⟩ := hζ v.1
    exact exists_char (D.what₂.embLL.comp (algebraMap Ks D.what₂.LL)) _ hz (iso v) (ψ0 (e v).1)
  choose ψ hψ using hex
  refine ⟨φ.trans R.eG.symm, ψ, fun u v => ?_, fun v h1 => ?_, fun u => ?_, fun u h => ?_⟩
  · show R.eG (R.eG.symm (φ u)) (e v) = _
    rw [MulEquiv.apply_symm_apply, hφ]
  · apply hgen (e v).1 (e v).2
    ext y
    obtain ⟨x, rfl⟩ := (iso v).surjective y
    rw [← hψ v x, h1, AddChar.one_apply, map_one, map_one, AddChar.one_apply]
  · show φ u ∈ (R.levR F false).H ↔ _
    rw [hlev, mem_lastZeroOrthImageSubspace_iff, GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.levelU, Subgroup.mem_pi]
    simp only [Set.mem_univ, true_implies]
    exact (e.forall_congr fun v => by rw [hφ, bc_mem_unip_iff]).symm
  · have hm : φ u ∈ (P0 R.Pg D.R.r ψ0).H := by rw [← hlev]; exact h
    have hun : ∀ PP, φ u PP ∈ unip (kP PP.1) D.R.r := (mem_lastZeroOrthImageSubspace_iff _ _ _ _).1 hm
    refine ⟨?_, fun i => ?_⟩
    · apply D.what₂.embLL.injective
      have e1 : (R.levR F false).chi ⟨φ u, h⟩ =
          Units.map (D.what₂.embLL : D.what₂.LL →* ℂ) ((F.lvl false).ψ ⟨(φ.trans R.eG.symm) u, h⟩) := rfl
      have key : ∀ X : LevelP R.Pg D.R.r ℂ, X = P0 R.Pg D.R.r ψ0 → ∀ g (hg : g ∈ X.H),
          ((X.chi ⟨g, hg⟩ : ℂˣ) : ℂ) = ∏ PP : R.Pg, ψ0 PP.1 (edgeSum supEdge (g PP)) := by
        rintro X rfl g hg
        exact baseLevelCharacter_eq_prod_superdiagonalSum _ _ _ g hg
      have h2 := key _ hlev (φ u) h
      rw [e1, Units.coe_map] at h2
      rw [show D.what₂.embLL (((F.lvl false).ψ ⟨(φ.trans R.eG.symm) u, h⟩ : D.what₂.LLˣ) : D.what₂.LL) =
        ∏ PP : R.Pg, ψ0 PP.1 (edgeSum supEdge (φ u PP)) from h2]
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.psiU, map_prod]
      refine Finset.prod_equiv e (by simp) fun v _ => ?_
      rw [hψ, hφ, edgeSum_bc, RingEquiv.coe_toRingHom]
    · apply Units.ext
      apply D.what₂.embLL.injective
      have hg : R.eG ((φ.trans R.eG.symm) u) = φ u := R.eG.apply_symm_apply _
      rw [hchiW i, hg, Finset.prod_eq_one (fun PP _ => by rw [det_unip (hun PP), map_one, Units.val_one]),
        Units.val_one, map_one]

end GlobalTheory.TypeBase
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BetaUnramifiedOutside
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FunObj

theorem beta_unrAt_off : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀)
    (i j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) ∉ G.pl.S0 →
      GlobalTheory.LFun.UnrAt (F := D.host.F) (E := D.host.E) (beta G i j) w := by
  intro D T L sc G μ₀ hL i j w hw
  have hi := i.2
  have h1 : 1 ≤ D.R.m - i := by omega
  have h2 : D.R.m - i ≤ D.R.m := by omega
  have hχ : GlobalTheory.LFun.UnrAt (F := D.host.F) (E := D.host.E) (G.ch.chi (D.R.m - i)) w :=
    (GlobalTheory.LFun.unrAt_iff_of_chrEq (G.ch.chi_eq _ h1 h2) w).2 (G.ch.unr _ h1 h2 w hw)
  have hη : GlobalTheory.LFun.UnrAt (F := D.host.F) (E := D.host.E) L.eta w :=
    (GlobalTheory.LFun.unrAt_iff_of_chrEq hL.eta w).2 (L.C.isEta.unr w)
  have hp : ∀ n : ℕ, GlobalTheory.LFun.UnrAt (F := D.host.F) (E := D.host.E) (L.eta ^ n) w := fun n x hx =>
    (map_pow Circle.toUnits _ n).trans
      (show GlobalTheory.LFun.locChar (F := D.host.F) (E := D.host.E) L.eta w x ^ n = 1 by rw [hη x hx, one_pow])
  exact hχ.mul (hp _)

end GlobalTheory.FunObj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUpperOfMulEqOne
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.BotPairSmall

theorem hatId_mul_of_mem_OhE (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) {x y : AE D} (hx : x ∈ OhE D)
    (hy : y ∈ hatId D 𝔪) : x * y ∈ hatId D 𝔪 := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨b, hb, x * s, (OhE D).mul_mem hx hs, by ring⟩
  | zero => simp
  | add y z _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
  | neg y _ h => rw [mul_neg]; exact neg_mem h

def blockUpperSub (R : Type) [CommRing R] (N a : ℕ) : Subalgebra R (Matrix (Fin N) (Fin N) R) where
  carrier := {A | ∀ i j : Fin N, j.1 < a → a ≤ i.1 → A i j = 0}
  mul_mem' {A B} hA hB i j hj hi := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : l.1 < a
    · rw [hA i l hl hi, zero_mul]
    · rw [hB l j hj (not_lt.1 hl), mul_zero]
  add_mem' {A B} hA hB i j hj hi := by simp [hA i j hj hi, hB i j hj hi]
  algebraMap_mem' r i j hj hi := by
    have : i ≠ j := fun e => by subst e; omega
    simp [Algebra.algebraMap_eq_smul_one, Matrix.one_apply_ne this]

theorem blockUpper_of_mul_eq_one {R : Type} [CommRing R] {N a : ℕ} {A B : Matrix (Fin N) (Fin N) R}
    (hAB : A * B = 1) (hA : ∀ i j : Fin N, j.1 < a → a ≤ i.1 → A i j = 0) :
    ∀ i j : Fin N, j.1 < a → a ≤ i.1 → B i j = 0 := by
  have hA' : A ∈ blockUpperSub R N a := hA
  have hBA : B * A = 1 := mul_eq_one_comm.1 hAB
  set p := A.charpoly
  have hq : Polynomial.aeval A p.divX ∈ blockUpperSub R N a :=
    Algebra.adjoin_le (Set.singleton_subset_iff.2 hA') (Polynomial.aeval_mem_adjoin_singleton R _)
  have hCH : Polynomial.aeval A p = 0 := Matrix.aeval_self_charpoly A
  rw [← Polynomial.X_mul_divX_add p, map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at hCH
  have h2 : p.coeff 0 • B = -Polynomial.aeval A p.divX := by
    have := congrArg (fun M => B * M) hCH
    simp only [mul_add, ← mul_assoc, hBA, one_mul, mul_zero, Algebra.algebraMap_eq_smul_one, Matrix.mul_smul,
      mul_one] at this
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact this
  have hdet : A.det * B.det = 1 := by rw [← Matrix.det_mul, hAB, Matrix.det_one]
  rw [Matrix.det_eq_sign_charpoly_coeff] at hdet
  have hB : B ∈ blockUpperSub R N a := by
    have hu : ((-1) ^ Fintype.card (Fin N) * B.det) * p.coeff 0 = 1 := by linear_combination hdet
    have : B = ((-1) ^ Fintype.card (Fin N) * B.det) • (p.coeff 0 • B) := by rw [smul_smul, hu, one_smul]
    rw [this, h2]
    exact Subalgebra.smul_mem _ (neg_mem hq) _
  exact hB

def blockLevelSub (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (a N : ℕ) : Subgroup (GA D N) where
  carrier := blockSet D 𝔪 a N
  one_mem' := by
    refine ⟨one_mem _, fun i j hj hi => ?_⟩
    have hij : i ≠ j := fun e => by subst e; omega
    simp [Matrix.one_apply_ne hij]
  mul_mem' {x y} hx hy := by
    have hX := (GlobalTheory.NormSum.mem_intG x).1 hx.1
    have hY := (GlobalTheory.NormSum.mem_intG y).1 hy.1
    refine ⟨mul_mem hx.1 hy.1, fun i j hj hi => ?_⟩
    rw [Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply]
    refine sum_mem fun l _ => ?_
    by_cases hl : l.1 < a
    · rw [mul_comm]; exact hatId_mul_of_mem_OhE D 𝔪 (hY l j).1 (hx.2 i l hl hi)
    · exact hatId_mul_of_mem_OhE D 𝔪 (hX i l).1 (hy.2 l j hj (not_lt.1 hl))
  inv_mem' {x} hx := by
    refine ⟨inv_mem hx.1, fun i j hj hi => ?_⟩
    have hI := (GlobalTheory.NormSum.mem_intG x).1 hx.1
    let J : Ideal (OhE D) :=
      { carrier := {z | (z : AE D) ∈ hatId D 𝔪}
        add_mem' := fun {u v} hu hv => by simpa using add_mem hu hv
        zero_mem' := by simp
        smul_mem' := fun c z hz => by simpa using hatId_mul_of_mem_OhE D 𝔪 c.2 hz }
    let M : Matrix (Fin N) (Fin N) (OhE D) := fun i j => ⟨_, (hI i j).1⟩
    let M' : Matrix (Fin N) (Fin N) (OhE D) := fun i j => ⟨_, (hI i j).2⟩
    have hMM : M * M' = 1 := by
      have hinj : Function.Injective fun A : Matrix (Fin N) (Fin N) (OhE D) => A.map (OhE D).subtype :=
        fun A B e => by
          ext i j
          exact congrFun (congrFun e i) j
      apply hinj
      change (M * M').map (OhE D).subtype = (1 : Matrix (Fin N) (Fin N) (OhE D)).map (OhE D).subtype
      rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
      have e1 : M.map (OhE D).subtype = ((x : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) := by
        ext; rfl
      have e2 : M'.map (OhE D).subtype =
          (((x : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) := by
        ext; rfl
      rw [e1, e2, Units.mul_inv]
    have hred := blockUpper_of_mul_eq_one (a := a) (A := M.map (Ideal.Quotient.mk J))
      (B := M'.map (Ideal.Quotient.mk J))
      (by rw [← Matrix.map_mul, hMM, Matrix.map_one _ (map_zero _) (map_one _)])
      (fun i j hj hi => by
        rw [Matrix.map_apply]
        exact Ideal.Quotient.eq_zero_iff_mem.2 (hx.2 i j hj hi)) i j hj hi
    rw [Matrix.map_apply] at hred
    have hm := Ideal.Quotient.eq_zero_iff_mem.1 hred
    exact hm

theorem blockJ_mem_iff_blockSet : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (a N : ℕ) (h : GA D N),
    h ∈ GlobalTheory.BotPairSmall.blockJ D 𝔪 a N ↔ h ∈ GlobalTheory.BotPairSmall.blockSet D 𝔪 a N := by
  intro D 𝔪 a N h
  constructor
  · intro hh
    exact (Subgroup.closure_le (blockLevelSub D 𝔪 a N)).2 (fun _ hx => hx) hh
  · intro hh
    exact Subgroup.subset_closure hh

end GlobalTheory.BotPairSmall
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomRanksSumLeTwoExponentAddCentreStatement
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bottomRanks_sum_le_two_exponent_add_centre : ∀ (D : D7) (C : ℝ) (i j : Fin D.R.m) (τ : D.what₂.Tau), ((GlobalTheory.FunObj.SqNum.botBig D i j + GlobalTheory.FunObj.SqNum.botSmall D i j : ℕ) : ℤ) ≤ 2 * ((GlobalTheory.ChiGrid.num D C τ).e (j + 1) + GlobalTheory.ChiGrid.cen D C τ (D.R.m - i)) := by
  first | exact @GlobalTheory.ChiGrid.botBig_add_botSmall_le_two_e_add_two_cen | exact GlobalTheory.ChiGrid.botBig_add_botSmall_le_two_e_add_two_cen | (intros; apply GlobalTheory.ChiGrid.botBig_add_botSmall_le_two_e_add_two_cen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardGroupElementsChartReturnLeStatement
section
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_group_elements_chart_return_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r) (x : Frame X.Ψ r) (ε ρ : ℝ), 0 < r → IsOrth X.toData x → 0 < ε → (r : ℝ) ^ 2 * ρ ≤ 1 / 100 → (∀ γ ∈ X.Γ, ∀ v ∈ X.L', (γ : Matrix (Fin r) (Fin r) E).mulVec v ∈ X.L') → (∀ v ∈ X.L', v ≠ 0 → ε ≤ ∑ τ, X.maj x τ (Data.emb τ.1 v)) → ({γ : GL (Fin r) E | γ ∈ X.Γ ∧ ∃ z z' : V (nd X.toData), ‖z‖ ≤ ρ ∧ ‖z'‖ ≤ ρ ∧ ∃ b ∈ Bor X.Ψ r, lact γ (cpt X.toData x z) = rmul (cpt X.toData x z') b}.encard : ℝ≥0∞) ≤ ENNReal.ofReal (multBd E r ε) := by
  first | exact @GlobalTheory.chart_mult_le | exact GlobalTheory.chart_mult_le | (intros; apply GlobalTheory.chart_mult_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechNonvanishingLineBundleInvMixOneZero
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
open scoped CategoryTheory.Obj

namespace GlobalTheory.AmpleGen

theorem isGen_oneGen {X Y : Scheme.{0}} (L : LB X) : (LB.oneGen (Y := Y) L).IsGen := by
  intro i j
  have hg : (LB.LinComb L (Y := Y) (K := PEmpty) PEmpty.elim PEmpty.elim).g i j = 1 :=
    by
    unfold LB.LinComb; simp
  simp only [LB.oneGen, hg, map_one, one_mul]

theorem exists_iso_mix_one_zero {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] (L : LB A.left)
    (hL : L.IsLB) : ∃ w : LB.Iso L (mix A L 1 0), w.IsGen := by
  have hs : LB.SameSum (K := PEmpty) PEmpty.elim PEmpty.elim
      (Sum.elim (fun _ : Fin 1 => 𝟙 A.left) ![𝟙 A.left, (GrpObj.inv : A ⟶ A).left])
      (Sum.elim (fun _ => (1 : ℤ)) fun k => -(![1, 0] : Fin 2 → ℤ) k) := by
    intro ψ
    by_cases h : 𝟙 A.left = ψ <;> by_cases h' : (GrpObj.inv : A ⟶ A).left = ψ <;>
      simp [Fintype.sum_sum_type, Fin.sum_univ_two, h, h']
  obtain ⟨t, ht, -⟩ := ReciprocityTheory.ChartRestriction.G.DVR.gen_transport hL hs (LB.oneGen L) (isGen_oneGen L)
  have key := (GlobalTheory.GermSectionCompare.isGen_divEquiv ![𝟙 A.left, (GrpObj.inv : A ⟶ A).left] ![1, 0]
    ((GlobalTheory.GermSectionCompare.divEquiv ![𝟙 A.left, (GrpObj.inv : A ⟶ A).left] ![1, 0]).symm t)).1
    (by rw [Equiv.apply_symm_apply]; exact ht)
  exact ⟨_, key⟩

theorem nv_mix_one_zero : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (L : LB A.left), L.IsLB →
    ∀ j : ℕ, NV A L j → NV A (mix A L 1 0) j := by
  intro K _ A _ L hL j ⟨κ, lo, ft, W, hW, hcov, hne⟩
  obtain ⟨w, hw⟩ := exists_iso_mix_one_zero A L hL
  have hM : (mix A L 1 0).IsLB := LB.isLB_linComb hL _ _
  exact ⟨κ, lo, ft, W, hW, hcov, fun h => hne (h.of_iso (GlobalTheory.AbLaw.cechLBCongr A.hom W hL hM w hw).symm)⟩

end GlobalTheory.AmpleGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartwiseC1DensityOfCompatible
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CurveStokes

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}

theorem contDiffAt_chart_of_smooth {A : ReciprocityTheory.AnForm.M.FinHolAtlas 1 (CxPts p σ)} (hA : IsAlgAtlas A)
    {χ : CxPts p σ → ℝ} (hχ : A.Smooth χ) (c : AlgChart p σ 1) {y : CxPts p σ} (hy : y ∈ c.e.source) :
    ContDiffAt ℝ 1 (fun v => χ (c.e.symm v)) (c.e y) := by
  have hC : ∀ x ∈ (Set.univ : Set (CxPts p σ)), CInfAt χ x := fun x _ => by
    obtain ⟨l, hl⟩ := A.cover x
    have h := hχ l
    rw [hA.chart_eq l] at h hl
    exact cInfAt_of_chart isOpen_univ _ ((AlgChart.contDiffOn_finChart_iff _ _ _ _).1 h) hl trivial
  have h := contDiffOn_chart hC c
  have hm : c.e y ∈ c.e.target ∩ c.e.symm ⁻¹' Set.univ := ⟨c.e.map_source hy, trivial⟩
  have hn : c.e.target ∩ c.e.symm ⁻¹' Set.univ ∈ 𝓝 (c.e y) := by
    rw [Set.preimage_univ, Set.inter_univ]; exact c.e.open_target.mem_nhds (c.e.map_source hy)
  exact ((h.contDiffAt hn).of_le (by norm_num))

end GlobalTheory.CurveStokes

namespace GlobalTheory

open GlobalTheory.CurveStokes in

theorem stokes_curve : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)] [SecondCountableTopology (CxPts p σ)], Nonempty (AnRead p σ 1) → ∀ (m : AlgChart p σ 1 → CxPts p σ → ℂ), (∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, ContDiffAt ℝ 1 (fun v => m c (c.e.symm v)) (c.e y)) → (∀ (c c' : AlgChart p σ 1) (y : CxPts p σ), y ∈ c.e.source → y ∈ c'.e.source → m c y = ChartGlue.transDet c.e c'.e y * m c' y) → total (fun (c : AlgChart p σ 1) (y : CxPts p σ) => (dbar (fun v => m c (c.e.symm v)) (c.e y) (EuclideanSpace.single 0 1)).re) = 0 := by
  intro k _ X p σ _ _ _ hR m hm hglue
  obtain ⟨R⟩ := hR
  set A := R.finAtlas
  have hA : IsAlgAtlas A := R.isAlgAtlas_finAtlas
  obtain ⟨P⟩ := ReciprocityTheory.AnForm.M.existsPartition A

  set mj : Fin A.n → AlgChart p σ 1 → CxPts p σ → ℂ := fun j c y => (P.χ j y : ℂ) * m c y with hmj
  have hχ : ∀ j (c : AlgChart p σ 1), ∀ y ∈ c.e.source,
      ContDiffAt ℝ 1 (fun v => ((P.χ j (c.e.symm v) : ℝ) : ℂ)) (c.e y) := fun j c y hy =>
    Complex.ofRealCLM.contDiff.contDiffAt.comp _ (contDiffAt_chart_of_smooth hA (P.smooth j) c hy)
  have hmj1 : ∀ j (c : AlgChart p σ 1), ∀ y ∈ c.e.source,
      ContDiffAt ℝ 1 (fun v => mj j c (c.e.symm v)) (c.e y) := fun j c y hy =>
    (hχ j c y hy).mul (hm c y hy)
  have hmj2 : ∀ j (c c' : AlgChart p σ 1) (y : CxPts p σ), y ∈ c.e.source → y ∈ c'.e.source →
      mj j c y = ChartGlue.transDet c.e c'.e y * mj j c' y := fun j c c' y hy hy' => by
    simp only [hmj, hglue c c' y hy hy']; ring
  set ρ : AlgChart p σ 1 → CxPts p σ → ℝ := fun c y =>
    (dbar (fun v => m c (c.e.symm v)) (c.e y) (EuclideanSpace.single 0 1)).re with hρ
  set ρj : Fin A.n → AlgChart p σ 1 → CxPts p σ → ℝ := fun j c y =>
    (dbar (fun v => mj j c (c.e.symm v)) (c.e y) (EuclideanSpace.single 0 1)).re with hρj

  have hzero : ∀ j, total (ρj j) = 0 := fun j => by
    obtain ⟨c₀, hc₀⟩ := hA j
    refine GlobalTheory.T.total_re_dbar_eq_zero_of_compact_support_in_chart k X p σ (mj j) (hmj1 j) (hmj2 j) c₀ (tsupport (P.χ j))
      (isClosed_tsupport _).isCompact ?_ ?_
    · have := P.tsupport_subset j
      rwa [hc₀, AlgChart.finChart_source] at this
    · intro c y _ hy
      simp [hmj, image_eq_zero_of_notMem_tsupport hy]

  have hsum : ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, ρ c y = ∑ j, ρj j c y := fun c y hy => by
    have e : (fun v => m c (c.e.symm v)) = fun v => ∑ j, mj j c (c.e.symm v) := funext fun v => by
      simp only [hmj, ← Finset.sum_mul, ← Complex.ofReal_sum, P.sum_eq_one, Complex.ofReal_one, one_mul]
    simp only [hρ, hρj, e]
    rw [dbar_sum fun j _ => ((hmj1 j c y hy).differentiableAt one_ne_zero)]
    simp [Complex.re_sum]

  obtain ⟨ν, w, hfin, -, hdens, htot⟩ := GlobalTheory.T.finite_measure_density_exists k X p σ ⟨R⟩
  have hd : ∀ j, IsDens (ρj j) := fun j => GlobalTheory.T.dbar_density_of_transition k X p σ (mj j) (hmj1 j) (hmj2 j)
  choose g hgc hgw using fun j => hdens _ (hd j)
  have hint : ∀ j, Integrable (g j) ν := fun j =>
    (hgc j).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h0 : ∀ j, ∫ y, g j y ∂ν = 0 := fun j => by
    rw [← (htot _ _ (hgc j) (hgw j)).2, hzero j]
  have hG : ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, ρ c y = (∑ j, g j y) * w c y := fun c y hy => by
    rw [hsum c y hy, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => hgw j c y hy
  rw [(htot ρ _ (continuous_finsetSum _ fun j _ => hgc j) hG).2, integral_finsetSum _ fun j _ => hint j]
  simp [h0]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexCoordsPrincipalLevelRangeEqTopStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexCoords_principalLevel_range_eq_top : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), A3.fam3.Ok3 1 → R.WeakCharacterisation F → GlobalTheory.LiftRows.UpInj R.toRealDat → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → (R.toCx3 F).zs.InBlock → ∀ t, LinearMap.range ((R.toCx3 F).iC (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false t) = ⊤ := by
  first | exact @GlobalTheory.PrimIn.iC_range_eq_top | exact GlobalTheory.PrimIn.iC_range_eq_top | (intros; apply GlobalTheory.PrimIn.iC_range_eq_top <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormGLIteratedDecayModerateGrowthStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_GL_iterated_decay_moderateGrowth : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (N : ℕ) (t : ℝ), 0 < t → ∀ i j : Fin a, (j : ℕ) = i + 1 → ∀ (m : ℕ) (ψ : Sm E a), IsCuspForm ψ → (∀ l : List (Lie E a), ∃ C : ℝ, ∀ y, ‖((l.map (lie E a)).prod ψ).1 (infGL E a y)‖ ≤ C * height y ^ N) → ∀ (Ω : Set (GL (Fin a) (Cinf E))), IsCompact Ω → ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) → ∀ c ∈ Ω, ‖ψ.1 (infGL E a (d * c))‖ ≤ C * (r j / r i) ^ m * height d ^ N := by
  first | exact @GlobalTheory.CuspRapid.iterated_decay | exact GlobalTheory.CuspRapid.iterated_decay | (intros; apply GlobalTheory.CuspRapid.iterated_decay <;> assumption)
end

