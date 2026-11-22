import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0006
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0062
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0119
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0057
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0071
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0124
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0715
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0128
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0722
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0598
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0061
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0064
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0048
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0131
import Development.AutomorphicArithmetic.UnitTensorPairings.Bundle0004
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0017
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0019
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0184
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0723
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0123
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0024
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0132
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0078
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0067
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0037

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsSplitDeformationLift
section
set_option synthInstance.maxHeartbeats 200000

section
section
noncomputable section
namespace GlobalTheory.DefSplit
section Alg
open scoped TensorProduct
variable {K L B W : Type} [Field K] [Field L] [Algebra K L] [CommRing B] [Algebra K B] [AddCommGroup W] [Module K W]
end Alg
section Geo
open CategoryTheory Limits AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient (fnAt basePt)
open GlobalTheory.LevelCoverCompare (fnRule fnRule_mem fnRule_injective fnAt_comp)
variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
variable {G : Type} [Group G] {lev : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La)}
end Geo
section Main
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open Formalism.IndefR.FWT
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem exists_free_action_permuting_summands_thirdPlace : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i _ _ => (i : ℕ) + 1 = (Fm.D x ι).R.m → ∀ (hp : _root_.GlobalTheory.CovTop.RowsTAlt p) (Hg : Type) [Group Hg] [Finite Hg] (φ : Hg →* p.P.Gp),
    GlobalTheory.DefPt.FreePt (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (fun h => (p.O i).lev2 (φ h)) →
    ∃ (X : Type) (_ : Fintype X) (_ : DecidableEq X) (_ : MulAction Hg X) (A : X → Submodule ℂ (GlobalTheory.DefRead.VC (GlobalTheory.DefHalf.sigC p) (GlobalTheory.DefHalf.CF p i))),
      (∀ (h : Hg) (y : X), h • y = y → h = 1) ∧ DirectSum.IsInternal A ∧
      ∀ (h : Hg) (y : X), ∀ v ∈ A y, GlobalTheory.DefRead.bcLin (GlobalTheory.DefHalf.sigC p) (_root_.GlobalTheory.DefHalf.groupActionOnCoefficients p i hp.1 (φ h)) v ∈ A (h • y) := by
  intro _ _
  have hw : _root_.GlobalTheory.CovTop.LiftWeightNumerator := _root_.GlobalTheory.CovTop.WtShape.wtN_z
  unfold _root_.GlobalTheory.CovTop.LiftWeightNumerator _root_.GlobalTheory.CovTop.LiftsCondition at *
  refine Closed.imp hw ?_
  rintro eps Fm CH - ⟨C, hC, x0, ha⟩
  refine ⟨C, hC, x0, fun x hx hle ι p hp i hi hp' Hg _ _ φ hF => ?_⟩
  have hW := ha x hx hle ι p hp i
  have hj : InR (Fm.D x ι) ((i : ℕ) + 1) := ⟨Nat.succ_pos _, hi.le⟩
  have hq : (p.T.Q.Dw ((i : ℕ) + 1)).q = 0 := by
    have : (dat p i).q = (Fm.D x ι).R.m - ((i : ℕ) + 1) := by rw [hW.sig.2.1]; rfl
    simpa [dat, hi] using this
  have hU := p.fw.laws.unf _ hj
  have h : ActLev (Xo := p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (p.O i).lev2 := (p.pins i).2.act.1
  have hL : ActLev (Xo := p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (fun g : Hg => (p.O i).lev2 (φ g)) :=
    ⟨fun g => h.total (φ g), fun g => h.func (φ g), fun S _ _ y => by
        have := h.one S y
        rw [← map_one φ] at this
        exact this,
      fun g g' S _ _ y y' y'' a b => by
        have := h.mul (φ g) (φ g') S y y' y'' a b
        rw [← map_mul φ] at this
        exact this,
      fun g => h.nat (φ g), fun g => h.bor (φ g)⟩
  refine split_rules hq hL hF (GlobalTheory.DefHalf.CF p i) (fun b f hf => ?_) (fun g => _root_.GlobalTheory.DefHalf.groupActionOnCoefficients p i hp'.1 (φ g))
    (fun g f => rfl) _
  refine GlobalTheory.DefPt.ReadsPt.mem_cusp_of_sec hq hU hW.dom ?_
  have := sec_mul _ _ _ _ _ _ (GlobalTheory.LevelCoverCompare.fnRule_mem b) (cusp_le_sec _ _ _ _ _ hf)
  rwa [zero_add, zero_add] at this
end Main
end GlobalTheory.DefSplit
end
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open Formalism.IndefR.FWT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isInternal_free_permuted_thirdPlace : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i _ _ => (i : ℕ) + 1 = (Fm.D x ι).R.m → ∀ (hp : _root_.GlobalTheory.CovTop.RowsTAlt p) (Hg : Type) [Group Hg] [Finite Hg] (φ : Hg →* p.P.Gp),
    GlobalTheory.DefPt.FreePt (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (fun h => (p.O i).lev2 (φ h)) →
    ∃ (X : Type) (_ : Fintype X) (_ : DecidableEq X) (_ : MulAction Hg X) (A : X → Submodule ℂ (GlobalTheory.DefRead.VC (GlobalTheory.DefHalf.sigC p) (GlobalTheory.DefHalf.CF p i))),
      (∀ (h : Hg) (y : X), h • y = y → h = 1) ∧ DirectSum.IsInternal A ∧
      ∀ (h : Hg) (y : X), ∀ v ∈ A y, GlobalTheory.DefRead.bcLin (GlobalTheory.DefHalf.sigC p) (_root_.GlobalTheory.DefHalf.groupActionOnCoefficients p i hp.1 (φ h)) v ∈ A (h • y) := by
  first | exact @_root_.GlobalTheory.DefSplit.exists_free_action_permuting_summands_thirdPlace | exact _root_.GlobalTheory.DefSplit.exists_free_action_permuting_summands_thirdPlace | (intros; apply _root_.GlobalTheory.DefSplit.exists_free_action_permuting_summands_thirdPlace <;> assumption)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsTheta
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
namespace GlobalTheory.HeightCounting.ThetaSt
section Gen
variable {D : D7}
theorem res_xiBar_alt (kv : Σ k : Fin 2, D.nd.PlG k) {PP : Pl D.host.E} (e : PP = D.naut.plGw kv.1 kv.2)
    (res : kP PP ≃+* ZMod (D.host.g kv.1)) : res (xiBar D PP) = NX.xiRed D kv := by
  subst e
  obtain ⟨a, c, hc, hac, hmem⟩ := Formalism.IndefR.NX.xiRed_isXiRes D kv
  have h1 := Formalism.L2.Col.reduction_spec (D.naut.plGw kv.1 kv.2) (a := D.host.xi0) (r := a) (s := c) hc (by
    change (c : D.host.E) * D.host.xi0 = (a : D.host.E)
    rw [hac, mul_comm])
  have h2 : Ideal.Quotient.mk (D.naut.plGw kv.1 kv.2).asIdeal (((NX.xiRed D kv).val : ℕ) : 𝓞 D.host.E) *
      Ideal.Quotient.mk (D.naut.plGw kv.1 kv.2).asIdeal c = Ideal.Quotient.mk (D.naut.plGw kv.1 kv.2).asIdeal a := by
    rw [← map_mul, Ideal.Quotient.eq]
    exact hmem
  have hc0 : Ideal.Quotient.mk (D.naut.plGw kv.1 kv.2).asIdeal c ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have h3 : Formalism.L2.Col.redP (D.naut.plGw kv.1 kv.2) D.host.xi0 =
      Ideal.Quotient.mk (D.naut.plGw kv.1 kv.2).asIdeal (((NX.xiRed D kv).val : ℕ) : 𝓞 D.host.E) := by
    apply mul_left_cancel₀ hc0
    rw [h1, ← h2, mul_comm]
  show res (Formalism.L2.Col.redP _ D.host.xi0) = _
  rw [h3, map_natCast, map_natCast, ZMod.natCast_zmod_val]
theorem exists_theta_ne_one_psiU_eq_psi0_inv {G : Type} [Group G] {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ} {Ps : Subgroup G} {ψs : Ps →* D.what₂.LLˣ}
    {eG : G ≃* G0g D.nd} (h : PsiPPTie D P0 ψ0 Ps ψs eG) (ζ : Fin 2 → ↥D.LL0)
    (hζ : ∀ k, D.what₂.embLL (ζ k : D.what₂.LL) = Complex.exp (2 * Real.pi * Complex.I / (D.host.g k : ℂ))) :
    ∃ θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ, (∀ kk, θ kk ≠ 1) ∧
      (∀ g : G, g ∈ P0 ↔ eG g ∈ Formalism.IndefR.NX.U D.nd) ∧
      ∀ (u : P0) (hu : eG u ∈ Formalism.IndefR.NX.U D.nd),
        (((psiUOf D.nd (NX.xiRed D) θ ⟨_, hu⟩ : (↥D.LL0)ˣ) : ↥D.LL0) : D.what₂.LL) =
          (((ψ0 u)⁻¹ : D.what₂.LLˣ) : D.what₂.LL) := by
  have hp := pow_of_emb ζ hζ
  obtain ⟨Pg, pl, res, ψ, eC, hT, hW⟩ := h
  refine ⟨thOf ζ hp, fun k hk => ?_, fun g => ?_, fun u hu => ?_⟩
  ·
    have hg1 : 1 < D.host.g k := (D.host.g_prime k).one_lt
    have : Fact (1 < D.host.g k) := ⟨hg1⟩
    have e := congrArg (fun f : Multiplicative (ZMod (D.host.g k)) →* (↥D.LL0)ˣ =>
      (((f (Multiplicative.ofAdd 1) : (↥D.LL0)ˣ) : ↥D.LL0) : D.what₂.LL)) hk
    simp only [thOf_val, ZMod.val_one, pow_one, MonoidHom.one_apply, Units.val_one] at e
    have e' : (ζ k : D.what₂.LL) = 1 := by
      have := congrArg (·⁻¹) e
      simpa using this
    have e2 := congrArg D.what₂.embLL e'
    rw [hζ, map_one] at e2
    exact ((Complex.isPrimitiveRoot_exp (D.host.g k) (D.host.g_prime k).ne_zero).ne_one hg1) e2
  ·
    rw [hT.p0, mem_U]
    change (∀ PP ∈ Set.univ, eC g PP ∈ unip _ _) ↔ _
    simp only [Set.mem_univ, forall_true_left]
    rw [pl.surjective.forall]
    refine forall_congr' fun kv => ?_
    rw [hT.comp g kv]
    have e : ∀ a b : Fin D.R.r, (Matrix.GeneralLinearGroup.map (res kv).toRingHom (eC g (pl kv))).val a b =
        res kv ((eC g (pl kv)).val a b) := fun _ _ => rfl
    simp only [e, EmbeddingLike.map_eq_zero_iff, EmbeddingLike.map_eq_one_iff]
    exact ⟨fun h => ⟨fun a b hab => h.1 hab, h.2⟩, fun h => ⟨fun a b hab => h.1 a b hab, h.2⟩⟩
  ·
    have hu0 : eC u ∈ (Formalism.L2.DIV.P0 Pg D.R.r ψ).H := (hT.p0 u).1 u.2
    rw [hT.chi0 u hu0, Units.val_inv_eq_inv_val, baseLevelCharacter_eq_prod_superdiagonalSum]
    have hfac : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ψ (pl kv).1 (edgeSum supEdge (eC u (pl kv))) =
        (ζ kv.1 : D.what₂.LL) ^ (NX.xiRed D kv * Formalism.L2.NX.supSum D.R.r
          (((eG u : G0g D.nd) kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))).val := by
      intro kv
      have hres : res kv (xiBar D (pl kv).1 * edgeSum supEdge (eC u (pl kv))) = NX.xiRed D kv * Formalism.L2.NX.supSum D.R.r
          (((eG u : G0g D.nd) kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) := by
        rw [map_mul, _root_.GlobalTheory.HeightCounting.ThetaSt.res_xiBar_alt kv (hT.place kv), hT.comp u kv, supSum_map]
        rfl
      rw [← hres]
      have hb : xiBar D (pl kv).1 * edgeSum supEdge (eC u (pl kv)) =
          (((res kv (xiBar D (pl kv).1 * edgeSum supEdge (eC u (pl kv)))).val : ℤ) : kP (pl kv).1) := by
        apply (res kv).injective
        rw [map_intCast, Int.cast_natCast, ZMod.natCast_zmod_val]
      apply D.what₂.embLL.injective
      rw [hW kv _ _ hb, map_pow, hζ, ← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    have lhs : (((psiUOf D.nd (NX.xiRed D) (thOf ζ hp) ⟨_, hu⟩ : (↥D.LL0)ˣ) : ↥D.LL0) : D.what₂.LL) =
        ∏ kv : (Σ k : Fin 2, D.nd.PlG k), ((ζ kv.1 : D.what₂.LL) ^ (NX.xiRed D kv * Formalism.L2.NX.supSum D.R.r
          (((eG u : G0g D.nd) kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))).val)⁻¹ := by
      rw [psiUOf_apply, Units.coe_prod, IntermediateField.coe_prod]
      exact Finset.prod_congr rfl fun kv _ => thOf_val ζ hp kv.1 _
    rw [lhs, ← Fintype.prod_equiv pl (fun kv => ψ (pl kv).1 (edgeSum supEdge (eC u (pl kv)))) _ (fun _ => rfl),
      Finset.prod_inv_distrib]
    exact congrArg _ (Finset.prod_congr rfl fun kv _ => (hfac kv).symm)
end Gen
section State
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
end State
theorem main_alt_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x → ∃ θ : ∀ kk : Fin 2, Multiplicative (ZMod ((Dof x).host.g kk)) →* (↥(Dof x).LL0)ˣ, (∀ kk, θ kk ≠ 1) ∧ LvlPsi x.m.z.R x.m.z.F x.m.z.cG θ := by
  intro hL
  refine StepW.of_all fun K B f T w _ _ _ P x _ => ?_
  have hζ := fun k => roots_g x k
  choose ζ hζ using hζ
  obtain ⟨θ, hne, hlvl, hpsi⟩ := _root_.GlobalTheory.HeightCounting.ThetaSt.exists_theta_ne_one_psiU_eq_psi0_inv x.m.z.pins.keep.psi ζ hζ
  exact ⟨θ, hne, hlvl, hpsi⟩
section Gen
end Gen
end GlobalTheory.HeightCounting.ThetaSt
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FormsCAtState
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.HeightCounting.RatSide
end GlobalTheory.HeightCounting.RatSide
namespace GlobalTheory.HeightCounting.RatSide
theorem formsC_at_state_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, StepW Start fun K B f T w =>
    ∀ (P : Pre2 K w) (x : St P), _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x → FormsC (SOf x) := by
  intro hL
  refine StepW.of_all fun K _ _ _ w _ _ _ P x _ => formsC_of_full _ fun j _ _ =>
    ⟨x.m.z.geo.fw.ks (idxOf _ j), GlobalTheory.GoodLat.Obj.mkFull_of_tie x.m.z.geo.fw (idxOf _ j)⟩
end GlobalTheory.HeightCounting.RatSide
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FrsFMemGlintRedVEqStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SymBridge GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_finite_family_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (n : Fin a.n) (t : W.P.T) (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (j : ℕ), j + 1 ≤ B.R.m → ∀ (β : J.Ch₀ j) (P : GlobalTheory.QTw.BadPr I (W.P.I.tup t)), P.1 = (a.pl n).1 →
    Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 j β).1.1 P ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N j) P.1 ∧
    ∀ x ∈ Formalism.L2.Col.stdAt B.fields.E (B.R.N j) P.1, Formalism.L2.Col.redV P.1 (Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 j β).1.1 P x) = Formalism.L2.Col.redV P.1 x := by
  first | exact @_root_.GlobalTheory.Fam.LevelFrames.frsF_mem_glint_redV_eq_alt | exact _root_.GlobalTheory.Fam.LevelFrames.frsF_mem_glint_redV_eq_alt | (intros; apply _root_.GlobalTheory.Fam.LevelFrames.frsF_mem_glint_redV_eq_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisRepTransportOfCopyAll
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.HeightCounting GlobalTheory.TwInputs.Move GlobalTheory.HeightCounting.SideCopy
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
private theorem multiset_eq_of_esymm_pz (M M' : Multiset ℂ) (r : ℕ) (h1 : M.card = r) (h2 : M'.card = r)
    (h : ∀ k, 1 ≤ k → k ≤ r → M.esymm k = M'.esymm k) : M = M' := by
  have hp : (M.map fun a => Polynomial.X - Polynomial.C a).prod = (M'.map fun a => Polynomial.X - Polynomial.C a).prod := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm, Multiset.prod_X_sub_X_eq_sum_esymm, h1, h2]
    refine Finset.sum_congr rfl fun k hk => ?_
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp [Multiset.esymm]
    · rw [h k hk0 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]
  rw [← Polynomial.roots_multiset_prod_X_sub_C M, hp, Polynomial.roots_multiset_prod_X_sub_C]
private theorem multiset_eq_of_norm_pz (M M' : Multiset ℂ) (r : ℕ) (h1 : M.card = r) (h2 : M'.card = r) (q u : ℂ) (n : ℕ)
    (hq : q ≠ 0) (hu : u ≠ 0)
    (h : ∀ k, 1 ≤ k → k ≤ r → q ^ (k * (r - k) / 2) * (M.map fun a => a⁻¹ * u⁻¹ * (q ^ n)⁻¹).esymm k =
      q ^ (k * (r - k) / 2) * (M'.map fun a => a⁻¹ * u⁻¹ * (q ^ n)⁻¹).esymm k) : M = M' := by
  have hinj : Function.Injective fun a : ℂ => a⁻¹ * u⁻¹ * (q ^ n)⁻¹ := fun a b hab =>
    inv_injective (mul_right_cancel₀ (inv_ne_zero hu) (mul_right_cancel₀ (inv_ne_zero (pow_ne_zero _ hq)) hab))
  refine Multiset.map_injective hinj (multiset_eq_of_esymm_pz _ _ r (by rw [Multiset.card_map, h1])
    (by rw [Multiset.card_map, h2]) fun k a b => mul_left_cancel₀ (pow_ne_zero _ hq) (h k a b))
private theorem isRepOf_of_split_pz (D : D7) {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {n : ℕ} (π : D.naut.CG n) (s : ℝ)
    (hC : GlobalTheory.RowTie.ChebSplit D.nd) (ρ₁ ρ₂ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin n) (Qbar l))
    (h₂ : IsRepOf D l ι π s ρ₂)
    (c₁ : Continuous (fun g => ((ρ₁ g : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)))) (s₁ : IsSSRep ρ₁)
    (f₁ : ∀ᶠ w in Filter.cofinite, IsSplitPl D.host w → ∀ (B : ValuationSubring D.nd.Om) (σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om),
      IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) σ →
      ((ρ₁ σ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.map ι.toRingHom =
        galPol D.naut (D.naut.lpTw (D.naut.locG π w) s)) : IsRepOf D l ι π s ρ₁ := by
  obtain ⟨c₂, s₂, f₂⟩ := h₂
  have hfin := (Filter.eventually_cofinite.mp f₁).union (Filter.eventually_cofinite.mp f₂)
  have hcp := GlobalTheory.TwistLG.charpoly_eq_of_dense ρ₁ ρ₂ c₁ c₂ _ (hC hfin.toFinset).closure_eq (by
    rintro g ⟨w, hw, hs, B, hB, hg⟩
    rw [Set.Finite.mem_toFinset] at hw
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hw
    apply Polynomial.map_injective ι.toRingHom ι.injective
    rw [hw.1 hs B g hB hg, hw.2 B g hB hg])
  refine ⟨c₁, s₁, f₂.mono fun w hw B σ hB hσ => ?_⟩
  rw [hcp σ]
  exact hw B σ hB hσ
private theorem side_data_pz (D : D7) (cf : CharFrame D) (hCS : CharSide D cf) (Rw : RowSide D) (Sb : Finset (PlE D.host))
    (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (hE : GlobalTheory.TwInputs.EigTrue D cf Rw Sb eig) (S : RatDat D.ntw)
    (c : ∀ (i : D.ntw.Tw) (_b : Bool) (_P : PlE D.host), (D.ntw.O i)ˣ) (rowS : ∀ i, D.ntw.Sig i → D.what₂.FT)
    (hR : RowEig D S eig c rowS) (i : D.ntw.Tw) (s : D.ntw.Sig i)
    (hi : D.what₂.isot (D.ntw.jS i s) (rowS i s) ≠ ⊥) (hg : D.nd.goodRow (rowS i s)) (π : D.naut.CG D.R.r)
    (hπ : ∀ w, IsSplitPl D.host w → D.naut.locG π w = Rw.locR (rowS i s) w) (j : Fin D.R.m) (hj : j.1 + 1 = D.ntw.jS i s)
    (t : ℝ) (P : PlE D.host) (hP : IsSplitPl D.host P) (h1 : P ∉ Sb) (h2 : P ∉ D.ntw.S0 i) :
    ∃ M : Multiset ℂ, M.card = D.R.r ∧
      galPol D.naut (D.naut.lpTw (D.naut.locG (D.naut.tw π D.naut.etaTinv) P) t) =
        (((M.map (· * ((cf.eta.val P : ℂˣ) : ℂ))).map (· * ((normV P : ℕ) : ℂ) ^ ((t : ℝ) : ℂ))).map
          fun α => Polynomial.X - Polynomial.C α).prod ∧
      ∀ k, 1 ≤ k → k ≤ D.R.r → ∃ x : ↥D.LL0, embLL0 D x = ((normV P : ℕ) : ℂ) ^ (k * (D.R.r - k) / 2) * (M.map fun a =>
        a⁻¹ * (((cf.mu0 j).val P : ℂˣ) : ℂ)⁻¹ * (((normV P : ℕ) : ℂ) ^ (D.R.nV / 2))⁻¹).esymm k ∧
        algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (D.ntw.hEig i s k P) =
          algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (c i (D.ntw.side i s) P) ^ k *
            IsFractionRing.map (A := D.ntw.O0 i) (B := D.ntw.O i) (K := FractionRing (D.ntw.O0 i))
              (L := FractionRing (D.ntw.O i)) (D.ntw.O_inj i)
              ((if D.ntw.side i s then D.ntw.emb0 i else D.ntw.emb0b i) x) := by
  obtain ⟨hu, he⟩ := hE j (rowS i s) (by rw [hj]; exact hi) hg P hP h1
  rw [← hπ P hP] at hu he
  refine ⟨D.naut.frobEig (D.naut.locG π P), by rw [D.naut.frobEig_card _ hu, D.naut.locG_dim], ?_, fun k a b => ?_⟩
  · have hue : D.naut.unr (D.naut.locG D.naut.etaTinv P) := (D.naut.etaTinv_def P).1
    have hfe : D.naut.frobEig (D.naut.locG D.naut.etaTinv P) = {((cf.eta.val P : ℂˣ) : ℂ)} := by
      rw [hCS.frob _ P ((hCS.unr_iff _ P).1 hue), hCS.etaTinv, HChar.val_inv, inv_inv]
    have hd : D.naut.lpDim (D.naut.locG D.naut.etaTinv P) = 1 := D.naut.locG_dim _ P
    rw [galPol, D.naut.locG_tw, D.naut.frobEig_tw _ _ (D.naut.unr_char _ _ hd hu hue),
      D.naut.frobEig_char _ _ _ hu hue hd hfe]
  · refine ⟨eig (D.ntw.jS i s) (rowS i s) k P, ?_, hR i s k P a b hP h2⟩
    have := he k a b
    rw [hj] at this
    exact this
private theorem read_cancel_pz (D : D7) (i : D.ntw.Tw) (b : Bool) (u : (D.ntw.O i)ˣ) (k : ℕ) (x y : ↥D.LL0)
    (h : algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) u ^ k *
        IsFractionRing.map (A := D.ntw.O0 i) (B := D.ntw.O i) (K := FractionRing (D.ntw.O0 i))
          (L := FractionRing (D.ntw.O i)) (D.ntw.O_inj i) ((if b then D.ntw.emb0 i else D.ntw.emb0b i) x) =
      algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) u ^ k *
        IsFractionRing.map (A := D.ntw.O0 i) (B := D.ntw.O i) (K := FractionRing (D.ntw.O0 i))
          (L := FractionRing (D.ntw.O i)) (D.ntw.O_inj i) ((if b then D.ntw.emb0 i else D.ntw.emb0b i) y)) : x = y :=
  RingHom.injective _ (RingHom.injective _ (mul_left_cancel₀ (pow_ne_zero _ (u.isUnit.map _).ne_zero) h))
theorem UpperTheory.galoisRep_transport_of_copyAll_alt :
    GlobalTheory.Published.GlobalArtinReciprocity → ∀ {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}, CopyAll D D' ι e → ∀ {cf : CharFrame D} {cf' : CharFrame D'}, SameFrame cf cf' → CharSide D cf → ∀ (Rw : RowSide D) (jE' : D'.host.E →+* Qb) (A' : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D' cf' jE'), RowCusp D Rw → GalEx D' → GlobalTheory.RowTie.ChebSplit D'.nd → ∀ (Sb : Finset (PlE D.host)) (Sb' : Finset (PlE D'.host)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (eig' : ℕ → D'.what₂.FT → ℕ → PlE D'.host → ↥D'.LL0), GlobalTheory.TwInputs.EigTrue D cf Rw Sb eig → GlobalTheory.TwInputs.EigTrue D' cf' A'.row Sb' eig' → ∀ (S : RatDat D.ntw) (S' : RatDat D'.ntw) (c : ∀ (i : D.ntw.Tw) (_b : Bool) (_P : PlE D.host), (D.ntw.O i)ˣ) (c' : ∀ (i : D'.ntw.Tw) (_b : Bool) (_P : PlE D'.host), (D'.ntw.O i)ˣ), SameUnits c c' → ∀ (rowS : ∀ i, D.ntw.Sig i → D.what₂.FT) (rowS' : ∀ i, D'.ntw.Sig i → D'.what₂.FT), RowEig D S eig c rowS → RowEig D' S' eig' c' rowS' → RhoSpec D Rw rowS → (∀ i s, D'.what₂.isot (D'.ntw.jS i s) (rowS' i s) ≠ ⊥ ∧ D'.nd.goodRow (rowS' i s)) → RhoSpec D' A'.row rowS' := by
  intro hGA D D' ι e h cf cf' hF hCS Rw jE' A' hRC hGal hCh Sb Sb' eig eig' hE hE' S S' c c' hU rowS rowS' hR hR' hρ hgood
  obtain ⟨r, rfl⟩ := h.cp.exists_rest
  intro i s
  refine ⟨(hgood i s).1, (hgood i s).2, fun π' hc hr hloc φ ιq hφ hι => ?_⟩
  obtain ⟨hi, hg, hspec⟩ := hρ i s
  have hjr := D.ntw.jS_range i s
  obtain ⟨π, pc, pr, ploc, -⟩ := hRC _ hjr.1 hjr.2 _ hi hg
  have hemb : ∀ x, (if D.ntw.side i s then D.ntw.emb0 i else D.ntw.emb0b i) (e x) =
      (if (overD D r).ntw.side i s then (overD D r).ntw.emb0 i else (overD D r).ntw.emb0b i) x := by
    intro x
    have e1 := eq_of_heq (h.cp.emb0 i i HEq.rfl x)
    have e2 := eq_of_heq (h.cp.emb0b i i HEq.rfl x)
    have e3 : (overD D r).ntw.side i s = D.ntw.side i s := rfl
    rw [e3]
    cases D.ntw.side i s
    · exact e2
    · exact e1
  have hι0 : ∀ x : ↥D.LL0, ιq (φ ((if D.ntw.side i s then D.ntw.emb0 i else D.ntw.emb0b i) x)) = embLL0 D x := by
    intro x
    obtain ⟨y, rfl⟩ := e.surjective x
    rw [hemb y, h.cp.embLL0_eq]
    exact hι y
  obtain ⟨c1, s1, f1⟩ := hspec π pc pr ploc φ ιq hφ hι0
  obtain ⟨ρ', hρ'⟩ := _root_.GlobalTheory.HeightCounting.TwistAny.exists_isRepOf_tw_alt hGA _ cf' jE' A' hGal _ ιq π' hc hr
  refine isRepOf_of_split_pz _ ιq _ _ hCh _ ρ' hρ' c1 s1 ?_
  have hmu : cf.mu0 = cf'.mu0 := eq_of_heq hF.mu0
  have heta : cf.eta = cf'.eta := eq_of_heq hF.eta
  have hcc : ∀ b P, c' i b P = c i b P := fun b P => eq_of_heq (hU i i b P P HEq.rfl HEq.rfl)
  have hj : (⟨D.ntw.jS i s - 1, by omega⟩ : Fin D.R.m).1 + 1 = D.ntw.jS i s := Nat.sub_add_cancel hjr.1
  filter_upwards [f1, Sb.eventually_cofinite_notMem, Sb'.eventually_cofinite_notMem,
    (D.ntw.S0 i).eventually_cofinite_notMem] with P hP n1 n2 n3 hs B σ hB hσ
  obtain ⟨M, m1, m2, m3⟩ := side_data_pz D cf hCS Rw Sb eig hE S c rowS hR i s hi hg π ploc _ hj
    ((1 - (D.R.nV : ℝ)) / 2) P hs n1 n3
  obtain ⟨M', m1', m2', m3'⟩ := side_data_pz _ cf' A'.chr A'.row Sb' eig' hE' S' c' rowS' hR' i s (hgood i s).1 (hgood i s).2
    π' hloc _ hj ((1 - (D.R.nV : ℝ)) / 2) P hs n2 n3
  have hq : ((normV P : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.mp h0)
  have hM : M = M' := by
    refine multiset_eq_of_norm_pz M M' D.R.r m1 m1' _ _ (D.R.nV / 2) hq
      ((cf.mu0 ⟨D.ntw.jS i s - 1, by omega⟩).val P).ne_zero fun k a b => ?_
    obtain ⟨x, x1, x2⟩ := m3 k a b
    obtain ⟨y, y1, y2⟩ := m3' k a b
    rw [← hmu] at y1
    rw [← hemb y, hcc] at y2
    have hxy : x = e y := read_cancel_pz D i _ _ k _ _ (x2.symm.trans y2)
    refine x1.symm.trans (Eq.trans ?_ y1)
    rw [hxy, h.cp.embLL0_eq]
  subst hM
  rw [← heta] at m2'
  exact (hP B σ hB hσ).trans (m2.trans m2'.symm)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GenPin
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.HeightCounting
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
namespace GlobalTheory.Fc.LabLinked
def GenPinAlt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch}
    (a : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL D cf nch tp) : Prop :=
  ∀ k, a.nt.A.grp.ζ k = @GlobalTheory.GLq.LabelDatum.gen _ ⟨a.nt.D.host.g_prime k⟩
    (@GlobalTheory.Mem.TypePl.labDat (a.nt.D.host.g k) ⟨a.nt.D.host.g_prime k⟩)
section Rows
end Rows
end GlobalTheory.Fc.LabLinked
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GoodGenericRows
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem.R3
noncomputable section
namespace GlobalTheory.Mem.R3.GenRows
set_option maxHeartbeats 4000000 in
theorem goodGeneric_rows_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (Γ : GeoP) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), p = _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none Γ → (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → ∀ (K : Ctx) (q : WPt p.s K), (∀ X : GlobalTheory.Mem.Stages, K.Over X.B.toPre → HostHyp X.toD7 ∧ X.toD7.host.F = maximalRealSubfield X.toD7.host.E ∧ (∀ i, IsFDiag (Wc X.toD7 i) ∧ IsFDiag (Vc X.toD7 i)) ∧ (∀ i, (Vc X.toD7 i).IsPosDef) ∧ (∀ j, Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.Y j) ∧ Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.V j) ∧ (1 ≤ j → j ≤ X.toD7.R.m → Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.W j))) ∧ Formalism.IndefR.Seed.FrmC.StdLat X.toD7.sp.X' ∧ (∀ i, (∀ a b, (Vc X.toD7 i).hT ((Vc X.toD7 i).frame a) ((Vc X.toD7 i).frame b) = if a = b then 1 else 0) ∧ (Vc X.toD7 i).L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range (Vc X.toD7 i).frame)) ∧ ((∀ a b, X.toD7.sp.X'.hT (X.toD7.sp.X'.frame a) (X.toD7.sp.X'.frame b) = if a = b then 1 else 0) ∧ X.toD7.sp.X'.L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range X.toD7.sp.X'.frame))) → GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat → ∀ (a : TwArgs q.O.ex q.x.what₂), letI := a.x.grp; letI := a.x.fin; ∀ χ ∈ a.x.A3.A.X, chiIdem χ * lvlIdem a.x.F.P0 a.x.F.ψ0 ≠ 0 := by
  intro _ _ _ _ _ _ _ _ _ hL N Γ p hp _ K q _ _ a
  have hSer : ∀ k : Fin 2, haveI : Fact ((q.w.st q.Z).toD7.host.g k).Prime := ⟨(q.w.st q.Z).toD7.host.g_prime k⟩
      ∃ (C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv (ZMod ((q.w.st q.Z).toD7.host.g k)))
        (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod ((q.w.st q.Z).toD7.host.g k)) C),
        ∀ f, (q.w.st q.Z).toD7.ntypes.eSer k f = Formalism.L2.NT.eSerO O (q.w.st q.Z).toD7.R.r f :=
    fun k => ⟨_, q.core_data_of_point.a.all.types.O k, q.core_data_of_point.a.all.types.eSer_def k⟩
  letI := a.x.grp
  letI := a.x.fin
  letI := a.x.alg
  exact (GlobalTheory.T.goodGenericCharacter_of_weakCharacterisation a.x.R a.x.F a.x.pins.char 1 a.intersectionNumber_baseChange.ok hSer).1
end GlobalTheory.Mem.R3.GenRows
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HermWCellLastMulMulVecEqOfInWb
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
namespace GlobalTheory.Fc.RL.PrimAt
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL}
theorem of_wit_alt {K : Ctx} {q : WPt p.s K} {c : ℝ} {b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c} (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) : _root_.GlobalTheory.Fc.R1.PrimitivityBundleCondition _ _ c b := by
  have h : (fun r : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S => Formalism.IndefR.Links.PrimRows3 r.B.Q.Rl r.B.Q.F ∧ r.P.A3.fam3.TypesSep3) (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput w.y.y) :=
    ⟨w.y.intersectionNumber_baseChange.prim, w.y.intersectionNumber_baseChange.sep⟩
  rw [← w.y.eq] at h
  exact h
theorem herm_wCell_last_mul_mulVec_eq_of_inWb (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (Q : V4.Slot) : _root_.GlobalTheory.Fc.R1.SlotPrimitivityCondition Q (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) := by
  refine RowE.row (R := _root_.GlobalTheory.Fc.R1.PrimitivityBundleCondition) (RowE.of_all fun κ K β c b _ _ hl => ?_)
  obtain ⟨q, b', ⟨w⟩, he⟩ := hl
  have := congrArg (fun s : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.BundleCondition D O c => _root_.GlobalTheory.Fc.R1.PrimitivityBundleCondition s.1 s.2.1 c s.2.2) he
  exact cast this.symm (_root_.GlobalTheory.Fc.RL.PrimAt.of_wit_alt w)
theorem linkedAt_hPA : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP),
    _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.R1.SlotPrimitivityCondition :=
  fun _ N S Γ => _root_.GlobalTheory.Fc.RL.LinkedAt.of_row (_root_.GlobalTheory.Fc.RL.PrimAt.herm_wCell_last_mul_mulVec_eq_of_inWb (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _)
end GlobalTheory.Fc.RL.PrimAt
end
end
end

