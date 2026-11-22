import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0370
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0286
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0353
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0271
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Formalism.LocalToGlobal.Columns.RecLevelLoc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0363
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0358
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0109
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0133
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0082
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0375
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0376
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0355
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0102
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0305
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0374
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerThetaEqSchwartzBruhat
section
noncomputable section

open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW

namespace GlobalTheory.SchSchwartzAll

theorem sch_sub {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : Continuous ψ) {A B : HSp D} {ν : Measure (WO A B)}
    {𝓨 : Set (WO A B)} (hν : IsCovolOne (ratL B A) ν 𝓨) {f f' : WO (dblSp A) B → ℂ}
    (hf : IsThetaFunO ψ (dblSp A) B f) (hf' : IsThetaFunO ψ (dblSp A) B f') :
    sch ψ A B ν 𝓨 (f - f') = sch ψ A B ν 𝓨 f - sch ψ A B ν 𝓨 f' := by
  funext x
  have h1 := (dblDec A).integrableOn_mixS hψ hν hf x 0
  have h2 := (dblDec A).integrableOn_mixS hψ hν hf' x 0
  refine Eq.trans ?_ (integral_sub h1 h2)
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  simp only [HypDec.integrandS_eq, Pi.sub_apply, mul_sub]

theorem schSchwartz : ∀ D : D7, SchSchwartz D := by
  intro D ψ hψ θ hθ A B ν 𝓨 hν
  refine ⟨fun f hf => (GlobalTheory.T.isSchwartzBruhat_iff_mem_adelicMatrixSchwartzSpace D θ hθ _ _ _).1 (GlobalTheory.T.isSchwartzBruhat_doubledPairSchrodingerFunction D ψ hψ A B ν 𝓨 hν f hf),
    fun φ hφ => GlobalTheory.T.exists_thetaFunction_schrodingerFunction_eq D ψ hψ A B ν 𝓨 hν φ ((GlobalTheory.T.isSchwartzBruhat_iff_mem_adelicMatrixSchwartzSpace D θ hθ _ _ _).2 hφ), fun f f' hf hf' h => ?_⟩
  refine sub_eq_zero.1 (GlobalTheory.T.doubledPairThetaFunction_eq_zero_of_schrodinger_eq_zero D ψ hψ A B ν 𝓨 hν (f - f') (GlobalTheory.OrientedHeis.theta_sub hf hf') ?_)
  rw [sch_sub hψ.1.1 hν hf hf', h, sub_self]

end GlobalTheory.SchSchwartzAll

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatHalfAdelicHomPairActionLevels
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

namespace GlobalTheory.SBMove

open Formalism.L2.Col in

theorem isFrame_one_std {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (n : ℕ) : Formalism.L2.DIV.IsFrame (F := F) 1 (Formalism.L2.Col.stdLat E n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · intro x
    simp only [inv_one, Units.val_one, Matrix.one_mulVec, IsEmpty.forall_iff, iff_true]
    rw [Subsingleton.elim x 0]; exact zero_mem _
  · haveI : NeZero n := ⟨hn.ne'⟩
    have e : Formalism.L2.Col.stdLat E n = baseLb E n ∅ := by
      ext x
      rw [rll_mem_baseLb]
      constructor
      · intro h
        have h' : ∀ j, ∃ r : 𝓞 E, algebraMap (𝓞 E) E r = x j := fun j =>
          (Submodule.mem_one).1 ((Submodule.mem_pi).1 h j (Set.mem_univ _))
        choose r hr using h'
        exact ⟨r, hr, fun P hP => absurd hP (Finset.notMem_empty _)⟩
      · rintro ⟨r, hr, -⟩
        exact (Submodule.mem_pi).2 fun j _ => (Submodule.mem_one).2 ⟨r j, hr j⟩
    intro x
    rw [e, rll_mem_hat_base, inv_one, Units.val_one, Matrix.one_mulVec]
    constructor
    · rintro ⟨y, hy, -⟩ i
      exact hy i ▸ (y i).2
    · exact fun h => ⟨fun i => ⟨x i, h i⟩, fun _ => rfl, fun P hP => absurd hP (Finset.notMem_empty _)⟩

theorem mulVec_mem_sub {A : Type} [CommRing A] {n : ℕ} (R : Subring A) (M : Matrix (Fin n) (Fin n) A)
    (hM : ∀ a b, M a b ∈ R) (v : Fin n → A) (hv : ∀ i, v i ∈ R) (i : Fin n) : (M *ᵥ v) i ∈ R := by
  simp only [Matrix.mulVec, dotProduct]
  exact R.sum_mem fun j _ => R.mul_mem (hM i j) (hv j)

theorem isFrame_of_int {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    {L : Submodule (𝓞 E) (Fin n → E)} (hL : Formalism.L2.DIV.IsFrame (F := F) 1 L)
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (h1 : ∀ a b, (β : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) a b ∈ Formalism.L2.Herm.intAf F E)
    (h2 : ∀ a b, ((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) a b ∈
      Formalism.L2.Herm.intAf F E) : Formalism.L2.DIV.IsFrame β L := by
  intro x
  rw [hL x, inv_one, Units.val_one, Matrix.one_mulVec]
  constructor
  · intro hx i; exact mulVec_mem_sub _ _ h2 x hx i
  · intro hx i
    have e : x = (β : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ
        (((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    rw [e]; exact mulVec_mem_sub _ _ h1 _ hx i

theorem int_of_moves {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) (g : GA D V)
    (h : Moves V hn g (Formalism.L2.Col.stdLat D.host.E n)) (a b : Fin V.rank) :
    toEAf D (Formalism.L2.Theta.mt V g⁻¹ a b) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  have hmem : (Pi.single (Fin.cast hn b) 1 : Fin n → D.host.E) ∈ Formalism.L2.Col.stdLat D.host.E n := by
    refine (Submodule.mem_pi).2 fun j _ => ?_
    by_cases hj : j = Fin.cast hn b
    · subst hj; simp only [Pi.single_eq_same]; exact Submodule.one_le.1 le_rfl
    · rw [Pi.single_eq_of_ne hj]; exact zero_mem _
  have h' := (h _).1 hmem (Fin.cast hn a)
  have e : (fun j => eToEAf D ((Pi.single (Fin.cast hn b) 1 : Fin n → D.host.E) j)) =
      Pi.single (Fin.cast hn b) 1 := by
    funext j
    by_cases hj : j = Fin.cast hn b
    · subst hj; simp
    · simp [Pi.single_eq_of_ne hj]
  rw [e, Matrix.mulVec_single_one] at h'
  simpa [finM, Matrix.reindex_apply] using h'

end GlobalTheory.SBMove

namespace GlobalTheory.SBMove

theorem mt_mul_inv_eq {D : D7} (V : HSp D) (g : GA D V) :
    Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V g⁻¹ = 1 := by
  simp only [Formalism.L2.Theta.mt]
  rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]

theorem actO_actO_inv {D : D7} {S T : HSp D} (g : GA D S) (h : GA D T) (x : WO S T) :
    actO S T g h (actO S T g⁻¹ h⁻¹ x) = x := by
  simp only [actO, inv_inv]
  simp only [← Matrix.mul_assoc]
  rw [mt_mul_inv_eq, Matrix.one_mul, Matrix.mul_assoc, mt_mul_inv_eq, Matrix.mul_one]

theorem actO_add' {D : D7} {S T : HSp D} (g : GA D S) (h : GA D T) (x y : WO S T) :
    actO S T g h (x + y) = actO S T g h x + actO S T g h y := by
  simp only [actO, Matrix.mul_add, Matrix.add_mul]

theorem actO_zero' {D : D7} {S T : HSp D} (g : GA D S) (h : GA D T) :
    actO S T g h 0 = 0 := by
  simp only [actO, Matrix.mul_zero, Matrix.zero_mul]

theorem actO_nsmul {D : D7} {S T : HSp D} (g : GA D S) (h : GA D T) (y : WO S T) (k : ℕ) :
    actO S T g h (k • y) = k • actO S T g h y := by
  induction k with
  | zero => rw [zero_nsmul, zero_nsmul, actO_zero']
  | succ k ih => rw [succ_nsmul, succ_nsmul, actO_add', ih]

theorem actO_add_nsmul {D : D7} {S T : HSp D} (g : GA D S) (h : GA D T) (x y : WO S T) (k : ℕ) :
    actO S T g h (x + k • y) = actO S T g h x + k • actO S T g h y := by
  rw [actO_add', actO_nsmul]

theorem actO_isHalf {D : D7} {S T : HSp D} (g : GA D S) (h : GA D T) (e : AE D) {x : WO S T} (hx : IsHalf e x) :
    IsHalf e (actO S T g h x) := by
  have hx' : x = e • x := by
    ext a b; exact (hx a b).symm
  have key : actO S T g h x = e • actO S T g h x := by
    conv_lhs => rw [hx']
    simp only [actO, Matrix.mul_smul, Matrix.smul_mul]
  intro i j
  have := congrFun (congrFun key i) j
  rw [Matrix.smul_apply, smul_eq_mul] at this
  exact this.symm

theorem coe_stdLat {D : D7} (n : ℕ) :
    ((Formalism.L2.Col.stdLat D.host.E n : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin n → D.host.E)) = intVec D n := by
  ext x
  simp only [SetLike.mem_coe, intVec, Set.mem_setOf_eq]
  rw [Formalism.L2.Col.stdLat, Submodule.mem_pi]
  refine forall_congr' fun k => ?_
  simp only [Set.mem_univ, true_implies, Submodule.mem_one]
  constructor
  · rintro ⟨y, hy⟩; rw [← hy]; exact y.isIntegral_coe
  · intro hk; exact ⟨⟨x k, hk⟩, rfl⟩

theorem actO_mem_stdHom {D : D7} (S T : HSp D) {n m : ℕ} (hn : S.rank = n) (hm : T.rank = m) (g : GA D S) (h : GA D T)
    (hg : Moves S hn g (Formalism.L2.Col.stdLat D.host.E n)) (hg' : Moves S hn g⁻¹ (Formalism.L2.Col.stdLat D.host.E n))
    (hh : Moves T hm h (Formalism.L2.Col.stdLat D.host.E m)) (hh' : Moves T hm h⁻¹ (Formalism.L2.Col.stdLat D.host.E m))
    {x : WO S T} (hx : x ∈ stdHom S T) : actO S T g h x ∈ stdHom S T := by
  have e : stdHom S T = latO S T ((Formalism.L2.Col.stdLat D.host.E S.rank : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) : Set (Fin S.rank → D.host.E))
      ((Formalism.L2.Col.stdLat D.host.E T.rank : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) : Set (Fin T.rank → D.host.E)) fun _ => True := by
    rw [coe_stdLat, coe_stdLat]
  rw [e] at hx ⊢
  have fr : ∀ (V : HSp D) {k : ℕ} (hk : V.rank = k) (b : GA D V), Moves V hk b (Formalism.L2.Col.stdLat D.host.E k) →
      Moves V hk b⁻¹ (Formalism.L2.Col.stdLat D.host.E k) →
      Formalism.L2.DIV.IsFrame (Matrix.GeneralLinearGroup.map (toEAf D) (matHom V b)) (Formalism.L2.Col.stdLat D.host.E V.rank) := by
    intro V k hk b hb hb'
    refine isFrame_of_int (isFrame_one_std _) _ (fun a c => ?_) (fun a c => ?_)
    · have := int_of_moves V hk b⁻¹ hb' a c
      rw [inv_inv] at this
      exact this
    · rw [← map_inv, ← map_inv]
      exact int_of_moves V hk b hb a c
  exact GlobalTheory.AdelicLatMove.actO_mem_latO S T g h _ _ _ _ 1 (Matrix.GeneralLinearGroup.map (toEAf D) (matHom S g)) 1
    (Matrix.GeneralLinearGroup.map (toEAf D) (matHom T h)) (isFrame_one_std _) (fr S hn g hg hg') (isFrame_one_std _)
    (fr T hm h hh hh') (by rw [Units.val_one, Matrix.mul_one]; rfl) (by rw [Units.val_one, Matrix.mul_one]; rfl) x hx

end GlobalTheory.SBMove

open GlobalTheory.SBMove in

theorem GlobalTheory.SBMove.isSBHalf_actO_lev : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ, ∀ Φ : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ, IsSBHalf A.e (stdHom _ _) Φ → ∀ (κ : A.U i α) (κ' : A.U (i + 1) γ), IsSBHalf A.e (stdHom _ _) (fun z => Φ (actO _ _ κ.1⁻¹ κ'.1⁻¹ z)) := by
  intro B X I hI hP l Z u a Ch A hA i hi α γ Φ hΦ κ κ'
  have hi0 : i ≤ B.R.m := Nat.le_of_succ_le hi
  have hU : ∀ j (hj : j ≤ B.R.m) (β : Ch j) g, g ∈ A.U j β →
      Moves _ (rankN (I.rec7 l Z) j hj) g (Formalism.L2.Col.stdLat B.fields.E _) :=
    fun j hj β g hg => GlobalTheory.AdForm.levels_keep_stdLat I hI hP l Z u a Ch A hA j hj β g hg
  have hG : ∀ x ∈ stdHom _ _, actO _ _ κ.1⁻¹ κ'.1⁻¹ x ∈ stdHom _ _ := fun x hx =>
    actO_mem_stdHom _ _ _ _ _ _ (hU i hi0 α _ (inv_mem κ.2)) (hU i hi0 α _ (by rw [inv_inv]; exact κ.2))
      (hU (i + 1) hi γ _ (inv_mem κ'.2)) (hU (i + 1) hi γ _ (by rw [inv_inv]; exact κ'.2)) hx
  have hH : ∀ x ∈ stdHom _ _, actO _ _ κ.1 κ'.1 x ∈ stdHom _ _ := fun x hx =>
    actO_mem_stdHom _ _ _ _ _ _ (hU i hi0 α _ κ.2) (hU i hi0 α _ (inv_mem κ.2))
      (hU (i + 1) hi γ _ κ'.2) (hU (i + 1) hi γ _ (inv_mem κ'.2)) hx
  obtain ⟨hsupp, k, hk, hinv, hden⟩ := hΦ
  refine ⟨fun t ht => ?_, k, hk, fun v hv hve t => ?_, fun t ht => ?_⟩
  · rw [← actO_actO_inv κ.1 κ'.1 t]
    exact actO_isHalf _ _ _ (hsupp _ ht)
  · show Φ (actO _ _ κ.1⁻¹ κ'.1⁻¹ (t + k • v)) = Φ (actO _ _ κ.1⁻¹ κ'.1⁻¹ t)
    rw [actO_add_nsmul]
    exact hinv _ (hG v hv) (actO_isHalf _ _ _ hve) _
  · have h1 := hden _ ht
    rw [← actO_nsmul] at h1
    rw [← actO_actO_inv κ.1 κ'.1 (k • t)]
    exact hH _ h1
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatHalfTensorSplitPlaceSelfDual
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil ValuativeRel

noncomputable section

namespace GlobalTheory.TensorLatO

theorem isSBHalf_tensorAt_of_bounds {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (p : Place D k) {S T : HSp D} {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y']
    [DecidableEq Y'] (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (L : AddSubgroup (WO S T))
    (e : AE D) (he : e * p.e = 0) (hMap : ∀ u ∈ L, u.map (fun a => p.e * a) ∈ L)
    (A B : ℕ) (hA : 0 < A) (hB : 0 < B)
    (hAL : ∀ X : Matrix Y Y' k, (∀ r q, X r q ∈ 𝒪[k]) → A • p.up FS FT X ∈ L)
    (hBL : ∀ u ∈ L, ∀ r q, (B : k) * p.down FS FT u r q ∈ 𝒪[k])
    (Φ : WO S T → ℂ) (hΦ : IsSBHalf e L Φ) (Ψ : Matrix Y Y' k → ℂ) (hΨ : Ψ ∈ SB (Matrix Y Y' k)) :
    IsSBHalf (e + p.e) L (p.tensorAt FS FT Φ Ψ) := by
  classical
  unfold IsSBHalf at hΦ ⊢
  obtain ⟨hΦs, kΦ, hkΦ, hΦi, hΦl⟩ := hΦ
  obtain ⟨N, hN, hΨi, hΨl⟩ := GlobalTheory.SBUnif.uniform k Y Y' Ψ hΨ
  have hud : ∀ u : WO S T, p.up FS FT (p.down FS FT u) = u.map (fun a => p.e * a) := by
    intro u
    unfold Place.down Place.up
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, FT.βγ, Matrix.one_mul, Matrix.mul_assoc, FS.βγ, Matrix.mul_one]
    ext i j
    exact p.ι_π _
  have hupn : ∀ (n : ℕ) (X : Matrix Y Y' k), p.up FS FT (n • X) = n • p.up FS FT X :=
    fun n X => map_nsmul (Witness.upH p FS FT) n X
  have hdownn : ∀ (n : ℕ) (u : WO S T), p.down FS FT (n • u) = n • p.down FS FT u :=
    fun n u => map_nsmul (Witness.downH p FS FT) n u
  have hsupp : ∀ t, p.tensorAt FS FT Φ Ψ t ≠ 0 →
      Φ (t - p.up FS FT (p.down FS FT t)) ≠ 0 ∧ Ψ (p.down FS FT t) ≠ 0 := fun t ht =>
    ⟨left_ne_zero_of_mul ht, right_ne_zero_of_mul ht⟩
  refine ⟨fun t ht => ?_, kΦ * (N * B * A), Nat.mul_pos hkΦ (Nat.mul_pos (Nat.mul_pos hN hB) hA),
    fun u hu hhu t => ?_, fun t ht => ?_⟩
  · obtain ⟨h1, -⟩ := hsupp t ht
    have hs := hΦs _ h1
    have hw := Witness.up_half p FS FT (p.down FS FT t)
    intro i j
    have a1 := hs i j
    have a2 := hw i j
    have e1 : t i j = (t - p.up FS FT (p.down FS FT t)) i j + p.up FS FT (p.down FS FT t) i j := by
      rw [Matrix.sub_apply, sub_add_cancel]
    rw [e1]
    linear_combination (1 - p.e) * a1 + (1 - e) * a2 +
      (p.up FS FT (p.down FS FT t) i j + (t - p.up FS FT (p.down FS FT t)) i j) * he
  · set X := p.down FS FT u with hX
    have hXL : p.up FS FT X ∈ L := by rw [hX, hud]; exact hMap u hu
    have hYi : ∀ r q, (((kΦ * A : ℕ) : k) • ((B : k) • X)) r q ∈ 𝒪[k] := fun r q => by
      rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
      exact mul_mem (natCast_mem _ _) (hBL u hu r q)
    have hd : p.down FS FT (t + (kΦ * (N * B * A)) • u) = p.down FS FT t + (kΦ * (N * B * A)) • X := by
      rw [Witness.down_add, hdownn]
    have e3 : p.down FS FT t + (kΦ * (N * B * A)) • X =
        p.down FS FT t + (N : k) • (((kΦ * A : ℕ) : k) • ((B : k) • X)) := by
      congr 1
      rw [← Nat.cast_smul_eq_nsmul k, smul_smul, smul_smul]
      congr 1
      push_cast; ring
    set w : WO S T := (N * B * A) • (u - p.up FS FT X) with hw
    have e2 : t + (kΦ * (N * B * A)) • u - p.up FS FT (p.down FS FT t + (kΦ * (N * B * A)) • X) =
        (t - p.up FS FT (p.down FS FT t)) + kΦ • w := by
      rw [Witness.up_add, hupn, hw, smul_smul, nsmul_sub]
      abel
    have hwL : w ∈ L := nsmul_mem (sub_mem hu hXL) _
    have hwH : IsHalf e w := by
      intro i j
      rw [hw, hX, hud, Matrix.smul_apply, Matrix.sub_apply, Matrix.map_apply, nsmul_eq_mul]
      linear_combination ((N * B * A : ℕ) : AE D) * hhu i j - ((N * B * A : ℕ) : AE D) * u i j * he
    show Φ (t + (kΦ * (N * B * A)) • u - p.up FS FT (p.down FS FT (t + (kΦ * (N * B * A)) • u))) *
        Ψ (p.down FS FT (t + (kΦ * (N * B * A)) • u)) =
      Φ (t - p.up FS FT (p.down FS FT t)) * Ψ (p.down FS FT t)
    rw [hd, e2, e3, hΦi w hwL hwH, hΨi _ _ hYi]
  · obtain ⟨h1, h2⟩ := hsupp t ht
    have a1 := hΦl _ h1
    have a2 : A • p.up FS FT (N • p.down FS FT t) ∈ L := hAL _ fun r q => by
      rw [Matrix.smul_apply, nsmul_eq_mul]; exact hΨl _ h2 r q
    rw [hupn] at a2
    have e1 : (kΦ * (N * B * A)) • t = (N * B * A) • (kΦ • (t - p.up FS FT (p.down FS FT t))) +
        kΦ • (B • (A • (N • p.up FS FT (p.down FS FT t)))) := by
      rw [smul_smul, smul_smul, smul_smul, smul_smul, mul_comm (N * B * A) kΦ,
        show kΦ * B * A * N = kΦ * (N * B * A) by ring, ← nsmul_add, sub_add_cancel]
    rw [e1]
    exact add_mem (nsmul_mem a1 _) (nsmul_mem (nsmul_mem a2 B) kΦ)

end GlobalTheory.TensorLatO
end

noncomputable section

namespace GlobalTheory.TensorLatO

theorem isSBHalf_tensorAt_latO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (M : Lat S) (M' : Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ (P : LocPl ψ S T M M') (e : AE D), e * P.q.e = 0 → ∀ Φ : WO S T → ℂ, IsSBHalf e (latO S T (M : Set _) (M' : Set _) fun _ => True) Φ → ∀ Ψ ∈ SB (Matrix P.Y P.Y' P.k), IsSBHalf (e + P.q.e) (latO S T (M : Set _) (M' : Set _) fun _ => True) ((ofSplit P.q).tensorAt P.FS P.FT Φ Ψ) := by
  classical
  intro D ψ S T M M' hS hT P e he Φ hΦ Ψ hΨ
  set L := latO S T (M : Set (Fin S.rank → D.host.E)) (M' : Set (Fin T.rank → D.host.E)) fun _ => True with hL
  set q := P.q with hq
  have hee : q.e * q.e = q.e := q.split.1

  have hMap : ∀ u ∈ L, u.map (fun a => (ofSplit q).e * a) ∈ L := fun u hu => by
    have h := GlobalTheory.SplitScalar.idem_smul_mem (LS := (M : Set (Fin S.rank → D.host.E)))
      (LT := (M' : Set (Fin T.rank → D.host.E))) hee u hu
    convert h using 1
    ext i j
    rfl

  obtain ⟨N₀, hN₀, h₀⟩ := GlobalTheory.FinPl.RdInt.exists_nat_mul_mem_fin
    (Sum.elim (fun x : Fin T.rank × P.Y => P.FT.β x.1 x.2) (fun x : P.Y' × Fin S.rank => P.FS.γ x.1 x.2))
  obtain ⟨K, hK, hmul⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO (S := S) (T := T) hS.1 hT.1
  have hAL : ∀ X : Matrix P.Y P.Y' P.k, (∀ r q, X r q ∈ 𝒪[P.k]) →
      (K * (N₀ * N₀)) • (ofSplit q).up P.FS P.FT X ∈ L := by
    intro X hX
    have hent := GlobalTheory.FinPl.RdInt.entry_mem P.FT.β P.FS.γ (fun i a => h₀ (Sum.inl (i, a)))
      (fun a j => h₀ (Sum.inr (a, j))) X hX
    have hh : IsHalf q.e ((N₀ * N₀) • (ofSplit q).up P.FS P.FT X) := fun i j => by
      rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm]
      exact congrArg _ (Witness.up_half (ofSplit q) P.FS P.FT X i j)
    have hui : ∀ i j, toEAf D (((N₀ * N₀) • (ofSplit q).up P.FS P.FT X) i j) ∈
        Formalism.L2.Herm.intAf D.host.F D.host.E := by
      intro i j
      have h1 : ((N₀ * N₀) • (ofSplit q).up P.FS P.FT X) i j =
          q.sec (((N₀ * N₀ : ℕ) : P.k) * (P.FT.β * X * P.FS.γ) i j) := by
        rw [← nsmul_eq_mul, map_nsmul]
        rfl
      rw [h1]
      exact GlobalTheory.PlaceCoord.toEAf_mem ((q.int_iff _).1 (hent i j))
    have h1 := hmul _ (GlobalTheory.PlaceDatum.infPart_of_half (GlobalTheory.PlaceCoord.infPart_split q.split) hh) hui
    rwa [mul_nsmul']

  obtain ⟨M₀, hM₀, hden⟩ := GlobalTheory.PlaceDatum.exists_den_latO (S := S) (T := T) hS.1.fg hT.1.fg
  obtain ⟨K₁, hK₁, h₁⟩ := GlobalTheory.FinPl.RdBound.exists_nat_mul_mem_family
    (fun x : P.Y × Fin T.rank => P.FT.γ x.1 x.2)
  obtain ⟨K₂, hK₂, h₂⟩ := GlobalTheory.FinPl.RdBound.exists_nat_mul_mem_family
    (fun x : Fin S.rank × P.Y' => P.FS.β x.1 x.2)
  have hBL : ∀ u ∈ L, ∀ i j, ((K₁ * M₀ * K₂ : ℕ) : P.k) * (ofSplit q).down P.FS P.FT u i j ∈ 𝒪[P.k] := by
    intro u hu i j
    have heu := GlobalTheory.SplitScalar.idem_smul_mem (LS := (M : Set (Fin S.rank → D.host.E)))
      (LT := (M' : Set (Fin T.rank → D.host.E))) hee u hu
    have hint : ∀ a b, (M₀ : P.k) * q.pr (u a b) ∈ 𝒪[P.k] := fun a b => by
      rw [q.int_iff]
      have h1 : q.sec ((M₀ : P.k) * q.pr (u a b)) = (M₀ : AE D) * (q.e • u) a b := by
        rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, q.sec_pr]
        rfl
      rw [h1]
      refine GlobalTheory.PlaceDatum.finPart_mem_of_toEAf ?_
      rw [RingHom.map_mul, map_natCast]
      exact hden _ heu a b
    change (_ : P.k) * (P.FT.γ * Matrix.map u q.pr * P.FS.β) i j ∈ 𝒪[P.k]
    rw [Matrix.mul_apply, Finset.mul_sum]
    refine sum_mem fun b _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    refine sum_mem fun a _ => ?_
    have e : ((K₁ * M₀ * K₂ : ℕ) : P.k) * (P.FT.γ i a * Matrix.map u q.pr a b * P.FS.β b j) =
        ((K₁ : P.k) * P.FT.γ i a) * ((M₀ : P.k) * q.pr (u a b)) * ((K₂ : P.k) * P.FS.β b j) := by
      rw [Matrix.map_apply]; push_cast; ring
    rw [e]
    exact mul_mem (mul_mem (h₁ (i, a)) (hint a b)) (h₂ (b, j))
  exact isSBHalf_tensorAt_of_bounds (ofSplit q) P.FS P.FT L e he hMap (K * (N₀ * N₀)) (K₁ * M₀ * K₂)
    (Nat.mul_pos hK (Nat.mul_pos hN₀ hN₀)) (Nat.mul_pos (Nat.mul_pos hK₁ hM₀) hK₂) hAL hBL Φ hΦ Ψ hΨ

end GlobalTheory.TensorLatO
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleStepLinearRelationsPeriodsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSaw_doubleStep_linearRelations_periods : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), DoubleStep D → RapidVal D → ValMove D → PerSum D → c.Is → (∀ s, (t s).Is) → (∀ s, (t s).LocFin) → ValX t → TwoX t → RdX t → StepX t := by
  first | exact @GlobalTheory.SeeSawStep.stepX_of_laws | exact GlobalTheory.SeeSawStep.stepX_of_laws | (intros; apply GlobalTheory.SeeSawStep.stepX_of_laws <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeEqOfSplitPlaceFrameSpanStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDual_lattice_eq_of_splitPlace_frame_span : ∀ {D : D7} (V : HSp D) (t : GA D V) (Λ L N : GlobalTheory.FinPl.Lat V) (β : GL (Fin V.rank) (Lev.EAf D)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (Y : Type) [Fintype Y] [DecidableEq Y] (F : Frame k V.rank Y) (σ : Fin V.rank ≃ Y), t ∈ GfC V → IsSelfDualC V Λ → Formalism.L2.DIV.IsFrame β Λ → IsSelfDualC V L → IsSelfDualC V N → GlobalTheory.FinPl.Moves V t Λ L (· = q.v) → MovedTo (ofSplit q) V t β (F.β.submatrix id σ) → IntIn q V F N → GlobalTheory.FinPl.latV V L (· = q.v) = GlobalTheory.FinPl.latV V N (· = q.v) := by
  first | exact @GlobalTheory.SplitFrameLat.latV_eq | exact GlobalTheory.SplitFrameLat.latV_eq | (intros; apply GlobalTheory.SplitFrameLat.latV_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeFrameChainStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.self_dual_lattice_frame_chain : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ j, j < D.R.m → IsSelfDualC (Yc D j) ((pk W).ΛY j) ∧ Formalism.L2.DIV.IsFrame ((pk W).βY j) ((pk W).ΛY j) := by
  first | exact @GlobalTheory.Fam.sdY_frames | exact GlobalTheory.Fam.sdY_frames | (intros; apply GlobalTheory.Fam.sdY_frames <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceIdempotentMulEqZeroOfNePlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceIdempotent_mul_eq_zero_of_ne_place : ∀ (D : D7) (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (q : SplitPt D k) (q' : SplitPt D k'), q.v ≠ q'.v → q.e * q'.e = 0 := by
  first | exact @GlobalTheory.SplitOrth.split_mul_split | exact GlobalTheory.SplitOrth.split_mul_split | (intros; apply GlobalTheory.SplitOrth.split_mul_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceIdempotentMulIdemSumEqZeroOfNotMemStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceIdempotent_mul_idemSum_eq_zero_of_not_mem : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (PP : Formalism.L2.DIV.Pl D.host.E) (e : AE D), PP ∉ P → Formalism.L2.NTheta.IsIdemAt p.e PP → IsIdemSum e P → e * p.e = 0 := by
  first | exact @GlobalTheory.LocMod.OutsideOrth.mul_eq_zero | exact GlobalTheory.LocMod.OutsideOrth.mul_eq_zero | (intros; apply GlobalTheory.LocMod.OutsideOrth.mul_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceIntegralMatrixIndicatorMemSchwartzBruhStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceIntegralMatrixIndicator_mem_schwartzBruhat : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'], Place.intInd (k := k) Y Y' ∈ SB (Matrix Y Y' k) := by
  first | exact @GlobalTheory.LocMod.Place.intInd_mem_SB | exact GlobalTheory.LocMod.Place.intInd_mem_SB | (intros; apply GlobalTheory.LocMod.Place.intInd_mem_SB <;> assumption)
end

