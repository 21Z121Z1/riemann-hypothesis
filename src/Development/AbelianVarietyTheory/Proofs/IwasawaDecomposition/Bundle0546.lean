import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0543
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0515
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0471
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0496
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0542
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0518
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanRangeMulVec
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0021
import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodFormsReferenceTupleIsometryColumnPairingStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodForms_referenceTuple_isometry_column_pairing : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), K.Over B.toPre → Forced K B T →
    pinAnd HasPk K B f T w → ∀ (P : Pre2 K w) (x : St P) (hη : ∀ j v, 1 ≤ j → j ≤ B.R.m → x.o.η j v = P.q.eta j v), ∀ u F G, inner ℂ ((w.D x.o.Z).eMt u F) ((w.D x.o.Z).eMt u G) = TC.ipMt w.I w.l u w.I.mu0 F G := by
  first | exact @GlobalTheory.Mem.R3.Rw.St.eMt0_isometry | exact GlobalTheory.Mem.R3.Rw.St.eMt0_isometry | (intros; apply GlobalTheory.Mem.R3.Rw.St.eMt0_isometry <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepNearLiftsComponentMemLocalChartGroup
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT.LevGe

theorem exists_put : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F)) (κ : GL (Fin n) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))), κ ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) → ∃ x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F), (∀ v', v' ≠ v → bc (prV (E := E) v') x = 1) ∧ bc (prV (E := E) v) x = bc (prV (E := E) v) κ := by
  intro F E _ _ _ _ _ σ n J v κ hκ
  classical
  refine ⟨Formalism.UG.P.afsplitU v (bc (prV (E := E) v) κ) 1,
    Formalism.UG.P.afsplitU_mem v σ J _ 1 (Formalism.UG.P.afsplit_bc_mem σ J v κ hκ) (one_mem _), fun w hw => ?_, ?_⟩
  · apply Units.ext
    rw [Formalism.UG.P.afsplit_coe_bc_prV, Formalism.UG.P.afsplitU_coe, Formalism.UG.P.afsplitC_prV_ne v w hw, Units.val_one, Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  · exact Formalism.UG.P.afsplit_right1 v _ 1

set_option maxHeartbeats 800000 in

theorem mem_uloc : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : Charts I l Z u a i hi bad chOf) (k : Ch → GA B (B.R.N i)), ReadsAt I l Z K k → ∀ (c : (I.stp u a i).Cl) (fb : SBof I a → GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E), FrNear I l Z a (k (chOf c)) fb → ∀ (P : SBof I a) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) → ∀ κ ∈ UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), ∀ g ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1, GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb (I.cst a).D P κ g → (∀ g' ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1, CongE P.1 ((I.cst a).D P) g g' → ∃ κ' : (I.stp u a i).G c.1, Keeps I κ' ((I.stp u a i).rep c) ∧ LiftsInv I κ' P g' ∧ ∀ P', P' ≠ P → LiftsInv I κ' P' 1) → bc (prV (E := (I.rec7 l Z).host.E) v) κ ∈ (K (chOf c)).lev.Uloc v := by
  intro B X I hOk hPins l Z u a i hi bad Ch chOf K k hR c fb hfb P v hv κ hκ g hg hF hL
  obtain ⟨N, hN⟩ := GlobalTheory.T.stepLevel_contains_deep_congruence_at_bad_prime I hOk hPins l Z a (B.T u) i hi bad (K (chOf c)).lev P v hv
  obtain ⟨x, hx, hxoff, hxv⟩ := exists_put _ _ v κ hκ
  obtain ⟨kk, hkk⟩ : ∃ kk : GL (Fin ((I.rec7 l Z).R.N i)) (TensorProduct (I.rec7 l Z).host.F (I.rec7 l Z).host.E (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)), kk = k (chOf c) := ⟨_, rfl⟩
  obtain ⟨z, hz, hzoff, hzN, g', hg', hgg', hpt⟩ := GlobalTheory.T.deepElement_conj_rational_at_badPrime I hOk hPins l Z a i hi kk fb (hkk ▸ hfb) P v hv κ hκ g hg hF x hx hxv N
  obtain ⟨κ', hK, hLP, hLo⟩ := hL g' hg' hgg'
  have hxz : x * z ∈ UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) := mul_mem hx hz
  have hxzoff : ∀ v', v' ≠ v → bc (prV (E := (I.rec7 l Z).host.E) v') (x * z) = 1 := fun v' hv' => by
    rw [map_mul, hxoff v' hv', hzoff v' hv', mul_one]
  have hpt' : ∀ r s, adAt (I.rec7 l Z).host.F (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((kk⁻¹ * (x * z) * kk).1 r s) = algebraMap (I.rec7 l Z).host.E ((GlobalTheory.TwU.seamP (sm I l Z) P.1).adicCompletion (I.rec7 l Z).host.E) ((GlobalTheory.TwU.seamGL (sm I l Z) g').1 r s) := hpt
  have hq := GlobalTheory.T.representative_image_point_of_lift I hOk hPins l Z u a i hi bad Ch chOf K k hR c kk hkk P v hv (x * z) hxz hxzoff g' hg' hpt' κ' hK hLP hLo
  subst hkk
  have hxzU : x * z ∈ (K (chOf c)).lev.U := (hR.lev c (x * z) _ hq).2 ⟨κ', hK.1, rfl, hK.2⟩
  have hzU : z ∈ (K (chOf c)).lev.U := hN z hz hzoff hzN
  have hxU : x ∈ (K (chOf c)).lev.U := by
    have := mul_mem hxzU (inv_mem hzU)
    rwa [mul_inv_cancel_right] at this
  have := (((K (chOf c)).lev.U_eq x).1 hxU).2 v
  rwa [hxv] at this

end GlobalTheory.Mem.Col2.AdT.LevGe

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ZeroSubspaceSpannedByDataZeroSubspaceLifts
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.R3.DivisionRationalLift

section Core

variable {K : Type} [Field K] [NumberField K] [StarRing K] {σ : K →+* ℂ} {M W : Type} [NormedAddCommGroup M]
  [InnerProductSpace ℂ M] [AddCommGroup W] [Module ℂ W]

omit [NumberField K] [StarRing K] in

theorem mulVec_map_injective {a b : ℕ} (Θ : Matrix (Fin a) (Fin b) K) (hΘ : Function.Injective Θ.mulVec) :
    Function.Injective (Θ.map σ).mulVec := by
  obtain ⟨g, hg⟩ := Θ.mulVecLin.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hΘ)
  have hL : LinearMap.toMatrix' g * Θ = 1 := by
    have := congrArg LinearMap.toMatrix' hg
    rwa [LinearMap.toMatrix'_comp, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this
  have hL' : (LinearMap.toMatrix' g).map σ * Θ.map σ = 1 := by
    rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero σ) (map_one σ)]
  intro x y hxy
  have := congrArg (fun v => (LinearMap.toMatrix' g).map σ *ᵥ v) hxy
  simp only [Matrix.mulVec_mulVec, hL', Matrix.one_mulVec] at this
  exact this

theorem orth_ker_inf_range {n d e : ℕ} (J : (Fin n → K) →ₛₗ[σ] M)
    (hsp : Submodule.span ℂ (Set.range fun k => J (Pi.single k 1)) = ⊤)
    (H : Matrix (Fin n) (Fin n) K) (hin : ∀ x y, inner ℂ (J x) (J y) = σ (Formalism.DivisionValues.hform H x y))
    (eM : M →ₗ[ℂ] M) (E : Matrix (Fin n) (Fin n) K) (hop : ∀ x, eM (J x) = J (E *ᵥ x))
    (Zm : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K) (hP : Formalism.DivisionValues.IsOrthProj H Zm Pr)
    (hEZ : ∀ z, E *ᵥ (Zm *ᵥ z) = Zm *ᵥ z)
    (jW : (Fin e → K) →ₛₗ[σ] W) (hW : LinearIndependent ℂ fun k => jW (Pi.single k 1))
    (Θ : Matrix (Fin e) (Fin d) K) (hΘ : Function.Injective Θ.mulVec)
    (θ' : M →ₗ[ℂ] W) (hθ : ∀ x, θ' (J x) = jW (Θ *ᵥ (Pr *ᵥ x))) :
    (LinearMap.ker θ')ᗮ ⊓ LinearMap.range eM = Submodule.span ℂ (Set.range fun k => J (Zm *ᵥ Pi.single k 1)) := by

  classical
  set S := Submodule.span ℂ (J '' Set.range fun z => Zm *ᵥ z) with hS
  set N := Submodule.span ℂ (J '' {y | Pr *ᵥ y = 0}) with hN
  have hSN : ∀ a ∈ S, ∀ b ∈ N, inner ℂ a b = 0 := by
    have hle : N ≤ Sᗮ := by
      rw [hN, Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_orthogonal]
      intro u hu
      have hle2 : S ≤ (Submodule.span ℂ {J y})ᗮ := by
        rw [hS, Submodule.span_le]
        rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_left, hin]
        have h0 := GlobalTheory.Mem.LiftForms.hform_orth hP z y
        rw [show Pr *ᵥ y = 0 from hy, Matrix.mulVec_zero, map_zero] at h0
        rw [← h0, map_zero]
      exact Submodule.mem_orthogonal_singleton_iff_inner_left.1 (hle2 hu)
    intro a ha b hb
    exact (Submodule.mem_orthogonal _ _).1 (hle hb) a ha
  have hker : ∀ x, Pr *ᵥ (x - Zm *ᵥ (Pr *ᵥ x)) = 0 := by
    intro x
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hP.1, Matrix.one_mulVec, sub_self]
  have htop : ∀ v : M, ∃ a ∈ S, ∃ b ∈ N, a + b = v := by
    intro v
    have hv : v ∈ S ⊔ N := by
      have : (⊤ : Submodule ℂ M) ≤ S ⊔ N := by
        rw [← hsp, Submodule.span_le]
        rintro _ ⟨k, rfl⟩
        have hd : J (Pi.single k 1) = J (Zm *ᵥ (Pr *ᵥ Pi.single k 1)) + J (Pi.single k 1 - Zm *ᵥ (Pr *ᵥ Pi.single k 1)) := by
          rw [← map_add, add_sub_cancel]
        show J (Pi.single k 1) ∈ S ⊔ N
        rw [hd]
        exact Submodule.add_mem_sup (Submodule.subset_span ⟨_, ⟨_, rfl⟩, rfl⟩) (Submodule.subset_span ⟨_, hker _, rfl⟩)
      exact this Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hv
    exact ⟨a, ha, b, hb, hab⟩
  have hNk : N ≤ LinearMap.ker θ' := by
    rw [hN, Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, hθ, show Pr *ᵥ y = 0 from hy, Matrix.mulVec_zero, map_zero]
  have hexp : ∀ y : Fin e → K, jW y = ∑ l, σ (y l) • jW (Pi.single l 1) := by
    intro y
    have hz : y = ∑ l, y l • (Pi.single l 1 : Fin e → K) := by
      ext i; simp [Pi.single_apply]
    conv_lhs => rw [hz]
    simp only [map_sum, map_smulₛₗ]
  have hSk : ∀ a ∈ S, θ' a = 0 → a = 0 := by
    intro a ha h0
    rw [hS, GlobalTheory.Mem.LiftForms.span_range_mulVec, ← Fintype.range_linearCombination] at ha
    obtain ⟨c, rfl⟩ := ha
    have hcomp : θ' (Fintype.linearCombination ℂ (fun k => J (Zm *ᵥ Pi.single k 1)) c) =
        ∑ l, ((Θ.map σ) *ᵥ c) l • jW (Pi.single l 1) := by
      simp only [Fintype.linearCombination_apply, map_sum, map_smul, hθ, Matrix.mulVec_mulVec, hP.1, Matrix.one_mulVec]
      simp only [hexp (Θ *ᵥ _), Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← Finset.sum_smul]
      congr 1
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm]
    rw [hcomp] at h0
    have hc0 : (Θ.map σ) *ᵥ c = 0 := funext fun l => Fintype.linearIndependent_iff.1 hW _ h0 l
    have hc : c = 0 := mulVec_map_injective Θ hΘ (hc0.trans (Matrix.mulVec_zero _).symm)
    rw [hc, map_zero]
  have hSZ : S ≤ LinearMap.range eM := by
    rw [hS, Submodule.span_le]
    rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
    exact ⟨J (Zm *ᵥ z), by rw [hop, hEZ]⟩
  have hmain : (LinearMap.ker θ')ᗮ = S := by
    apply le_antisymm
    · intro v hv
      obtain ⟨a, ha, b, hb, rfl⟩ := htop v
      have h1 : inner ℂ b (a + b) = 0 := (Submodule.mem_orthogonal _ _).1 hv b (hNk hb)
      have h2 : inner ℂ b a = 0 := by rw [← inner_conj_symm, hSN a ha b hb, map_zero]
      rw [inner_add_right, h2, zero_add, inner_self_eq_zero] at h1
      rw [h1, add_zero]
      exact ha
    · intro s hs
      rw [Submodule.mem_orthogonal]
      intro w hw
      obtain ⟨a, ha, b, hb, rfl⟩ := htop w
      have hθa : θ' a = 0 := by
        have h3 := LinearMap.mem_ker.1 hw
        rwa [map_add, LinearMap.mem_ker.1 (hNk hb), add_zero] at h3
      rw [hSk a ha hθa, zero_add, ← inner_conj_symm, hSN s hs b hb, map_zero]
  rw [hmain, inf_eq_left.2 hSZ, hS, GlobalTheory.Mem.LiftForms.span_range_mulVec]

end Core

section Main

theorem divisionRows_rationalLift : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → ∀ (i : Fin D.R.m) (t : T), Formalism.BasicNotions.Idx.Z0 D (Y.tup t) ((i : ℕ) + 1) = Submodule.span ℂ (Set.range fun k => (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1)) (Y.eMt i t ((lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t).mulVec (Pi.single k 1)))) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH i t
  have hR := complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim
  have hb : Function.Bijective ((A3.indefDown (s0Of R F)).θ i t).mulVec :=
    CxData.liftMat_bij (R.toCx3 F) F.cr false hR.kForm hR.ewNorm (hR.h4pos.2.2 false) hR.lifts0.1 hR.ratTh i t
  have hB : BlockHyp (A3.A.fam.L i t) (A3.A.fam.lvlA F.P0 F.ψ0) A3.A.v0 1 :=
    ⟨hH.ok.ok2.conj, hH.ok.ok2.irr, hH.ok.ok2.lifts i t⟩
  have hp : Formalism.DivisionValues.IsOrthProj (lH D A3.A F.P0 F.ψ0 i t) (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t)
      (lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t) := BlockDat.lf_l_proj hB
  have he : ∀ z, lE D A3.A F.P0 F.ψ0 i t *ᵥ (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ z) =
      lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ z := fun z => GlobalTheory.Mem.LiftForms.lvlOp_lE hB z
  obtain ⟨hTh, hθ⟩ := GlobalTheory.T.liftCuspFormSpace_thetaMap_eq_data D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH
  have hf := Y.formsL i t
  exact orth_ker_inf_range ((D.what₂.jMt (Y.tup t) ((i : ℕ) + 1)).comp (Y.eMt i t).toLinearMap) hf.span
    (lH D A3.A F.P0 F.ψ0 i t) hf.inner (D.what₂.eMt (Y.tup t) ((i : ℕ) + 1)) (lE D A3.A F.P0 F.ψ0 i t) hf.op_eq
    _ _ hp he (Z.jW i) (hTh.li i) _ hb.1 (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1)) (hθ i t)

end Main

end GlobalTheory.Mem.R3.DivisionRationalLift

end
end

