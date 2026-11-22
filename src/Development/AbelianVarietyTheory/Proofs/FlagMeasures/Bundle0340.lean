import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
import Formalism.LocalToGlobal.HermitianForms.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0332
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0209
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0141
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0324
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0147
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0338
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0328
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0335
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0323
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0114
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EmbeddedDatumOfTermDefiniteSpace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0334
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0309
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLimitOfChart
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0150
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0170
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0336
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.TopfBasis
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0014
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthComplementUnitVectorSameFields
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFinEmb
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeFrameLocalBasisUnitriangular
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

theorem GlobalTheory.St.G.frame_local_basis_unitriangular : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (k t : ℕ) (gp : Fin 2 → ℕ) (G : GLoc F E cm.sig gp) (L : Submodule (𝓞 E) (Fin n → E)) (Fr : AdFrame cm.sig J (hat F L) (gp 0 * gp 1) k), k = n → (∀ i, (gp i).Prime) → gp 0 ≠ gp 1 → (∀ i, SplitsIn E (gp i)) → IsLat L → ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (hv : (gp i : 𝓞 F) ∈ v.asIdeal), SelfDualAt cm.sig J v L → ∃ (fr : GL (Fin n) (v.adicCompletion F)) (ψ : AddChar (kv F v) ℂ), ψ ≠ 1 ∧ (∀ x : Fin n → v.adicCompletion F, (∃ y ∈ loc v L, ∀ b, G.phi i v hv (y b) = x b) ↔ ∀ b, ((fr⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec x b ∈ v.adicCompletionIntegers F) ∧ ∀ y ∈ levelVL cm.sig J v L, (Fr.LocK L v y ↔ InJ n t n false (redM F v (G.mat i v hv fr y))) ∧ (Fr.LocK L v y → Fr.locChi v y = lamJ ψ (fun _ => 1) n t 0 n (redM F v (G.mat i v hv fr y))) := by
  intro F E _ _ _ _ _ _ cm n J hJ hdet k t gp G L Fr hk hpr hne hspl hlat i v hv _hsd
  subst k
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    refine ⟨1, G.psi0 i v hv, G.psi_zero_nontrivial_character i v hv, ?_, ?_⟩
    · intro x
      exact ⟨fun _ b => b.elim0, fun _ => ⟨0, zero_mem _, fun b => b.elim0⟩⟩
    · intro y _
      refine ⟨⟨fun _ => ⟨fun x => x.elim0, fun x => x.elim0, fun x => x.elim0, fun _ x => x.elim0⟩, fun _ i => i.elim0⟩, fun _ => ?_⟩
      simp only [AdFrame.locChi, supSum, lamJ, Finset.univ_eq_empty, Finset.sum_empty, mul_zero, map_zero,
        Finset.range_zero, Finset.prod_empty, mul_one, AddChar.map_zero_eq_one]
      exact Fr.psi_int 0 (zero_mem _)
  · obtain ⟨-, hsplitv⟩ := GlobalTheory.T.cmField_splitCompletely_place_structure F E cm (gp i) (hpr i) (hspl i)
    obtain ⟨-, hmax, -⟩ := hsplitv v hv
    obtain ⟨hmaxg, hgv, q, hq, hgq⟩ := GlobalTheory.T.uniformiser_product_type_primes F gp hpr hne i v hv hmax
    have hint := GlobalTheory.T.local_integers_iff_split_at_type_prime F E cm gp G hpr hspl i v hv
    obtain ⟨he1, he2, he3, he4, hb, hbd, hbe, hbde, hdual, hspan⟩ :=
      GlobalTheory.T.adelicLatticeFrame_component_localFrame F E cm.sig n J L (gp 0 * gp 1) n Fr v
    have hcase := GlobalTheory.T.local_frame_idempotent_factor_cases F E cm.sig n v (G.sp i v hv) (G.sp_sig i v hv) (G.sp_alg i v hv)
      (gp 0 * gp 1) hgv L hlat hpos _ he1 he2 he4
    have hne0 : prV (E := E) v Fr.eps ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hcase
      rcases hcase with h | h <;> simp [Prod.ext_iff] at h
    obtain ⟨a, ha, hpa⟩ := GlobalTheory.T.standardAdditiveCharacter_local_ne_one_splitPrime F E cm Fr.psi Fr.psi_add Fr.psi_int Fr.psi_rat (gp i) (hpr i) (hspl i)
      v hv _ he3 he1 hne0
    have hnt : ∃ a ∈ intV E v, Fr.psi (Formalism.UG.P.afsplitIE v (algebraMap F (E ⊗[F] v.adicCompletion F)
        (((gp 0 * gp 1 : ℕ) : F)⁻¹) * (prV (E := E) v Fr.eps * a))) ≠ 1 := by
      refine ⟨(q : E ⊗[F] v.adicCompletion F) * a, mul_mem (natCast_mem _ q) ha, ?_⟩
      have hq0 : (q : F) ≠ 0 := by exact_mod_cast hq.ne'
      have hp0 : ((gp i : ℕ) : F) ≠ 0 := by exact_mod_cast (hpr i).ne_zero
      have key : algebraMap F (E ⊗[F] v.adicCompletion F) (((gp 0 * gp 1 : ℕ) : F)⁻¹) *
          (prV (E := E) v Fr.eps * ((q : E ⊗[F] v.adicCompletion F) * a)) =
          algebraMap F (E ⊗[F] v.adicCompletion F) (((gp i : ℕ) : F)⁻¹) * (prV (E := E) v Fr.eps * a) := by
        rw [← map_natCast (algebraMap F (E ⊗[F] v.adicCompletion F)) q, mul_left_comm (prV (E := E) v Fr.eps),
          ← mul_assoc, ← map_mul]
        have hcast : ((gp 0 * gp 1 : ℕ) : F) = ((gp i : ℕ) : F) * (q : F) := by rw [hgq]; push_cast; ring
        congr 2
        rw [hcast]
        field_simp
      rw [key]
      exact hpa
    rcases hcase with hc | hc
    · exact GlobalTheory.T.splitPlace_firstFactor_localFrame F E cm n J hJ hdet t v (G.sp i v hv) (G.sp_sig i v hv) (G.sp_alg i v hv) hint (gp 0 * gp 1) hmaxg L hlat _ hc _ _ hb hbd hbe hbde hdual hspan Fr.psi Fr.psi_add Fr.psi_int hnt
    · exact GlobalTheory.T.localFrame_secondFactor_reversedDualBasis F E cm n J hJ hdet t v (G.sp i v hv) (G.sp_sig i v hv) (G.sp_alg i v hv) hint (gp 0 * gp 1) hmaxg L hlat _ hc _ _ hb hbd hbe hbde hdual hspan Fr.psi Fr.psi_add Fr.psi_int hnt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BaseLatticeConstructionHolds
section
noncomputable section
open scoped Classical Pointwise
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm

namespace GlobalTheory.TypeAsm.LatticeOrthogonalComplement

section Gen
variable {K V W : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
  [IsScalarTower (𝓞 K) K W] {H : HermSpace K V} {HW : HermSpace K W} {r : ℕ}

theorem B_swap {x y : V} (h : H.B x y = 0) : H.B y x = 0 := by
  rw [← H.herm, h, star_zero]

theorem X_B_e (F : FlagD H r) (a : Fin (r + 1)) (x : V) (hx : x ∈ F.X) : H.B x (F.e a) = 0 := by
  have key : ∀ b : Fin r, H.B (F.e b.castSucc) (F.e a) = 0 := by
    intro b
    induction a using Fin.lastCases with
    | last => exact F.zperp b
    | cast c => exact F.iso b c
  have : F.X ≤ LinearMap.ker (H.B.flip (F.e a)) := by
    unfold FlagD.X FlagD.Xa
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, -, rfl⟩
    simpa using key b
  simpa using this hx

theorem X_B_perp (F : FlagD H r) {v : V} (hv : ∀ a : Fin (r + 1), H.B (F.e a) v = 0) (x : V) (hx : x ∈ F.X) :
    H.B x v = 0 := by
  have : F.X ≤ LinearMap.ker (H.B.flip v) := by
    unfold FlagD.X FlagD.Xa
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, -, rfl⟩
    simpa using hv b.castSucc
  simpa using this hx

theorem flag_vector_mem_base_lattice (F : FlagD H r) (a : Fin (r + 1)) : F.e a ∈ V0 F F := by
  unfold V0
  induction a using Fin.lastCases with
  | last => exact Submodule.mem_sup_right (Submodule.subset_span (Set.mem_insert _ _))
  | cast c => exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.subset_span ⟨c, c.2, rfl⟩))

theorem mem_wSp (F : FlagD H r) (v : V) : v ∈ wSp F F ↔ ∀ a, H.B (F.e a) v = 0 := by
  rw [wSp, mem_perp_iff]
  constructor
  · intro h a
    exact B_swap (h _ (flag_vector_mem_base_lattice F a))
  · intro h x hx
    apply B_swap
    have : V0 F F ≤ LinearMap.ker (H.B.flip v) := by
      unfold V0
      refine sup_le (sup_le ?_ ?_) (Submodule.span_le.2 ?_)
      · intro y hy; simpa using X_B_perp F h y hy
      · intro y hy; simpa using X_B_perp F h y hy
      · rintro _ (rfl | rfl) <;> simpa [FlagD.z] using h (Fin.last r)
    simpa using this hx

theorem mem_perp_lattice_flag_iff (F : FlagD H r) (Λ : Submodule (𝓞 K) V) (v : V) :
    v ∈ flagPairDefinitePartLattice F F Λ ↔ v ∈ Λ ⊔ rs (𝓞 K) F.X ∧ v ∈ wSp F F := by
  simp only [flagPairDefinitePartLattice, latL, Submodule.mem_inf, Submodule.restrictScalars_mem]
  constructor
  · rintro ⟨⟨-, h1⟩, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨?_, h1⟩, h2⟩
    rw [uPerp, mem_perp_iff]
    rw [wSp, mem_perp_iff] at h2
    exact fun x hx => h2 x ((le_sup_left : F.X ⊔ F.X ≤ V0 F F) hx)

variable {F : FlagD H r} {e : W →ₗ[K] V}

theorem e_perp (hE : IsEmb F HW e) (w : W) (a : Fin (r + 1)) : H.B (F.e a) (e w) = 0 :=
  (hE.2 _).2 (Submodule.mem_sup_left ⟨w, rfl⟩) a

theorem e_wSp (hE : IsEmb F HW e) (w : W) : e w ∈ wSp F F := (mem_wSp F _).2 (e_perp hE w)

theorem X_wSp (x : V) (hx : x ∈ F.X) : x ∈ wSp F F :=
  (mem_wSp F _).2 fun a => B_swap (X_B_e F a x hx)

theorem decomp (hE : IsEmb F HW e) {v : V} (hv : v ∈ wSp F F) : ∃ w, v - e w ∈ F.X := by
  obtain ⟨_, ⟨w, rfl⟩, z, hz, h⟩ := Submodule.mem_sup.1 ((hE.2 v).1 ((mem_wSp F v).1 hv))
  exact ⟨w, by rw [← h]; simpa using hz⟩

theorem XB_e (hE : IsEmb F HW e) (x : V) (hx : x ∈ F.X) (w : W) : H.B x (e w) = 0 :=
  X_B_perp F (e_perp hE w) x hx

theorem memL_e (hE : IsEmb F HW e) (Λ : Submodule (𝓞 K) V) (w : W) :
    e w ∈ flagPairDefinitePartLattice F F Λ ↔ w ∈ lat0 F e Λ :=
  (mem_perp_lattice_flag_iff F Λ _).trans ⟨fun h => h.1, fun h => ⟨h, e_wSp hE w⟩⟩

theorem X_L (Λ : Submodule (𝓞 K) V) (x : V) (hx : x ∈ F.X) : x ∈ flagPairDefinitePartLattice F F Λ :=
  (mem_perp_lattice_flag_iff F Λ x).2 ⟨Submodule.mem_sup_right hx, X_wSp x hx⟩

theorem quotEquiv (hE : IsEmb F HW e) (Λ : Submodule (𝓞 K) V)
    (hspan : Submodule.span K (flagPairDefinitePartLattice F F Λ : Set V) = wSp F F) :
    Nonempty ((↥(Formalism.HermitianLatticesTheory.dual HW.B.flip (lat0 F e Λ)) ⧸
        (lat0 F e Λ).comap (Formalism.HermitianLatticesTheory.dual HW.B.flip (lat0 F e Λ)).subtype) ≃ₗ[𝓞 K]
      (↥(dual H (flagPairDefinitePartLattice F F Λ)) ⧸ (flagPairDefinitePartLattice F F Λ).comap (dual H (flagPairDefinitePartLattice F F Λ)).subtype)) := by
  set L := flagPairDefinitePartLattice F F Λ with hL
  set M := lat0 F e Λ with hM
  set DW := Formalism.HermitianLatticesTheory.dual HW.B.flip M with hDW
  set DV := dual H L with hDV
  have hmemW : ∀ w, w ∈ DW ↔ ∀ y ∈ M, HW.B w y ∈ (1 : Submodule (𝓞 K) K) := fun w => by
    rw [hDW, Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
    simp only [LinearMap.flip_apply]
  have hin : ∀ w : DW, e w ∈ DV := by
    rintro ⟨w, hw⟩
    rw [hDV, mem_dual_iff, hspan]
    refine ⟨e_wSp hE w, fun x hx => ?_⟩
    obtain ⟨w', hw'⟩ := decomp hE ((mem_perp_lattice_flag_iff F Λ x).1 hx).2
    have hw'M : w' ∈ M := (memL_e hE Λ w').1 (by simpa using L.sub_mem hx (X_L Λ _ hw'))
    have h1 : H.B (e w) x = HW.B w w' := by
      have e1 : x = e w' + (x - e w') := by abel
      rw [e1, map_add, B_swap (XB_e hE _ hw' w), add_zero, hE.1]
    rw [h1]
    exact (hmemW w).1 hw w' hw'M
  let f : DW →ₗ[𝓞 K] DV :=
    LinearMap.codRestrict DV ((e.restrictScalars (𝓞 K)).comp DW.subtype) (fun w => hin w)
  let Φ := (L.comap DV.subtype).mkQ ∘ₗ f
  have hker : LinearMap.ker Φ = M.comap DW.subtype := by
    ext w
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_comap, Submodule.mem_comap]
    exact memL_e hE Λ w
  have hsurj : Function.Surjective Φ := by
    intro q
    obtain ⟨⟨v, hv⟩, rfl⟩ := Submodule.mkQ_surjective _ q
    have hv' := (mem_dual_iff H L v).1 hv
    rw [hspan] at hv'
    obtain ⟨w, hw⟩ := decomp hE hv'.1
    have hwD : w ∈ DW := (hmemW w).2 fun y hy => by
      have h1 : HW.B w y = H.B v (e y) := by
        rw [← hE.1]
        have e1 : v = e w + (v - e w) := by abel
        conv_rhs => rw [e1]
        rw [map_add, LinearMap.add_apply, XB_e hE (v - e w) hw y, add_zero]
      rw [h1]
      exact hv'.2 _ ((memL_e hE Λ y).2 hy)
    refine ⟨⟨w, hwD⟩, ?_⟩
    show Submodule.Quotient.mk (f ⟨w, hwD⟩) = Submodule.Quotient.mk ⟨v, hv⟩
    rw [Submodule.Quotient.eq]
    show e w - v ∈ L
    have := L.neg_mem (X_L Λ _ hw)
    simpa using this
  exact ⟨(Submodule.quotEquivOfEq _ _ hker.symm).trans (Φ.quotKerEquivOfSurjective hsurj)⟩

end Gen

end GlobalTheory.TypeAsm.LatticeOrthogonalComplement

open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
namespace GlobalTheory.TypeAsm
open LatticeOrthogonalComplement
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem lat0C : LatticeNormalizationCondition := by
  intro D large₂ X Y u hS W HW hE Λ hΛ
  obtain ⟨hCM, -, -, -, -, -, -, -, -, -, -, hg, -⟩ := GlobalTheory.T.unitaryHostFieldArithmeticConditions D large₂ hS
  obtain ⟨N, hF, hF', -, hT, -, hTerm, -, -⟩ := GlobalTheory.T.fixedFrameSelfNormalFormExists_proof D large₂ X Y u hS Λ (Or.inl hΛ)
  have hg1 : 1 ≤ gS D := by omega
  obtain ⟨-, -, -, hLat, -, hNe⟩ := GlobalTheory.DegCnt.PrimPerp.main _ _ (HV D) hCM D.R.rS N (gS D) Λ hg1 hTerm
  rw [hF, hF'] at hLat hNe
  rw [hT] at hNe
  have hAd : Adapt (F0 X u) (F0 X u) N.𝔡 N := by
    have := adapt_self N
    rwa [hF, hF'] at this
  obtain ⟨⟨hInt, -⟩, -⟩ := GlobalTheory.DegAsm.isDat_datOf _ _ _ (HV D) HW W.subtype hCM D.R.rS (F0 X u) (F0 X u) N.𝔡 N
    (gS D) Λ hg1 hE hAd hTerm
  have hd : (datOf (F0 X u) (F0 X u) W.subtype (gS D) Λ).1 = lat0 (F0 X u) W.subtype Λ := by
    ext w
    change W.subtype w ∈ flagPairDefinitePartLattice (F0 X u) (F0 X u) Λ ⊔ rs _ (F0 X u).X ↔ w ∈ lat0 (F0 X u) W.subtype Λ
    rw [sup_eq_left.2 (fun x hx => X_L Λ x hx), memL_e hE Λ]
  refine ⟨hd ▸ hInt, ?_⟩
  obtain ⟨q⟩ := quotEquiv hE Λ hLat.2
  obtain ⟨i⟩ := hNe
  exact ⟨q.trans i⟩

end GlobalTheory.TypeAsm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousDensitySelfDualLatticeIndicatorAtUnitStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuousDensity_selfDualLatticeIndicator_at_unit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ), 1 ≤ M → ∀ (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.UnramifiedPlace F E v → ∀ ψ : AddChar (Fv F v) ℂ, GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.IsLocalChar v ψ → ∀ n : ℤ, GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.DualExponent v ψ n → ∀ L : Submodule (GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.maxOrder F E v) (Fin M → Fv F v ⊗[F] E), GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.IsSelfDualLattice σ J v L → ∀ (μ : Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)) (ν : Measure (Fv F v)), SdW F E σ M J (Fv F v) ψ 1 μ → SdR (Fv F v) ψ ν → ∀ g : Fv F v → ℂ, IsContDensityOn μ (fun X => qR (Fv F v) σ J (X 0)) id ν {c | c ≠ 0} ({X | X 0 ∈ L}.indicator 1) g → ∀ β : Fv F v, Valued.v β = 1 → g β = (((GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.resCard F v ^ n) ^ ((1 / 2 : ℝ) - (M : ℝ)) * (1 - GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.eta F E v ^ M * (GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.resCard F v ^ M)⁻¹) : ℝ) : ℂ) := by
  first | exact @GlobalTheory.LatticeContDensity.contDensity_unit | exact GlobalTheory.LatticeContDensity.contDensity_unit | (intros; apply GlobalTheory.LatticeContDensity.contDensity_unit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousRepresentativePropertiesStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_representative_properties : ∀ (B : RowsAut), (∀ F f f', IsContRep B F f → IsContRep B F f' → f = f') ∧ (∀ F F' f f' (c : ℂ), IsContRep B F f → IsContRep B F' f' → IsContRep B (F + c • F') (fun x => f x + c * f' x)) ∧ (∀ F f g, IsContRep B F f → IsContRep B (B.R g F) (fun x => f (x * g))) ∧ ∀ F f, IsContRep B F f → f =ᵐ[B.I.muA B.μf] B.I.ext F ∧ ∫⁻ x in B.fund, ‖f x‖ₑ ^ 2 ∂(B.I.muA B.μf) = ENNReal.ofReal (‖F‖ ^ 2) := by
  first | exact @GlobalTheory.ContRepUniq.contRep_unique_linear | exact GlobalTheory.ContRepUniq.contRep_unique_linear | (intros; apply GlobalTheory.ContRepUniq.contRep_unique_linear <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DeepRegionKernelDiagonalBound
section
open MeasureTheory NumberField Formalism.MainNotions.S GlobalTheory.Count

namespace GlobalTheory.DeepRegion

theorem one_le_f (I : AutInst) : 1 ≤ I.f := by
  show 0 < Module.finrank ℚ I.F
  exact Module.finrank_pos

theorem one_le_rd (I : AutInst) : 1 ≤ I.rd := by
  have hd : (1 : ℝ) ≤ |(discr I.E : ℝ)| := by
    have h0 : discr I.E ≠ 0 := discr_ne_zero I.E
    have : (1 : ℤ) ≤ |discr I.E| := Int.one_le_abs h0
    exact_mod_cast this
  exact Real.one_le_rpow hd (by positivity)

theorem deepBound (hV : GlobalTheory.FlagMeas.AbsoluteVolume) (hK : GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.DeepKernelBound) :
    GlobalTheory.IndefiniteRowSideFullHecke.DeepSet.DeepBound := by
  intro Cg hCg
  refine ⟨8, ?_⟩
  intro B d p q b hq hH
  obtain ⟨hDS, hSig, hn0, hqn, hrd, hf, hb, hbb, hlam, hg1, hgb, hg0p, hg0, hsplit, hgap⟩ := id hH
  have hgc : ∀ v, ∃ c : ℝ, 0 < c ∧ IsGauge (B.I.ε v) c := fun v => by
    obtain ⟨c, hc, hc', -⟩ := GlobalTheory.GaugeConst.exists_unique_isGauge B.I.n (B.I.ε v)
    exact ⟨c, hc, hc'⟩
  choose c hc0 hc using hgc
  have hn8 : 8 ≤ B.I.n := hn0
  have hf1 : 1 ≤ B.I.f := one_le_f B.I
  have hrd1 : 1 ≤ B.I.rd := one_le_rd B.I
  have hnR : (8 : ℝ) ≤ B.I.n := by exact_mod_cast hn8
  have hfR : (1 : ℝ) ≤ B.I.f := by exact_mod_cast hf1
  have hgR : (1 : ℝ) ≤ B.g := by exact_mod_cast hg1
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = (B.I.n : ℝ) * B.I.f * B.I.rd * B.g * b := ⟨_, rfl⟩
  have a1 : (8 : ℝ) ≤ B.I.n * B.I.f := by nlinarith
  have a2 : (8 : ℝ) ≤ B.I.n * B.I.f * B.g := by nlinarith
  have a3 : (16 : ℝ) ≤ B.I.n * B.I.f * B.g * b := by nlinarith
  have hXe : X = B.I.rd * (B.I.n * B.I.f * B.g * b) := by rw [hX]; ring
  have hX16 : 16 ≤ X := by rw [hXe]; nlinarith
  have hXrd : B.I.rd ≤ X := by rw [hXe]; nlinarith
  have hXf : 2 * B.I.f * B.I.rd ≤ X := by
    have : 2 * (B.I.f : ℝ) ≤ B.I.n * B.I.f * B.g * b := by nlinarith
    rw [hXe]; nlinarith
  have hXsq : 2 * B.I.f * B.I.rd ≤ X ^ 2 := by nlinarith
  have hVol := hV B.I p q (by first | exact hSig | exact fun v => hSig v) hqn hn8 X (by linarith) hXrd hXsq
    c B.μf (by first | exact hc | exact fun v => ⟨hc0 v, hc v⟩ | exact fun v => ⟨hc v, hc0 v⟩)
  obtain ⟨hKs, hKg0, hKsT⟩ := GlobalTheory.CongIndex.measure_Kset_le B.I B.μf B.g hg1
  obtain ⟨hcov, -⟩ := GlobalTheory.T.leftQuotientCovolume_eq_fundamentalDomain_inter B.I B.μf B.fund Set.univ B.fund_spec MeasurableSet.univ
    (fun _ _ _ _ => trivial)
  rw [Set.univ_inter] at hcov
  change ENNReal.ofReal (∏ v, c v) * _ / B.μf B.I.Kset ≤ _ at hVol
  rw [hcov] at hVol
  set N : ℕ := B.I.n ^ 2 * B.I.f with hN
  set P : ℝ := ∏ v, c v with hP
  have hP0 : 0 < P := Finset.prod_pos fun v _ => hc0 v
  have hKgT : B.μf (B.I.Kg B.g) ≠ ⊤ :=
    ne_top_of_le_ne_top hKsT.ne (measure_mono fun x hx => hx.1)
  set kR : ℝ := (B.μf (B.I.Kg B.g)).toReal with hkR
  have hkR0 : 0 < kR := ENNReal.toReal_pos hKg0.ne' hKgT
  have hX0 : 0 < X := by linarith
  have hg0' : (0 : ℝ) < B.g := by linarith
  have hm0 : B.μf B.I.Kset ≠ 0 := (lt_of_lt_of_le hKg0 (measure_mono fun x hx => hx.1)).ne'

  have hF : B.I.muA B.μf B.fund ≤ ENNReal.ofReal (X ^ N * (B.g : ℝ) ^ (2 * N) * kR / P) := by
    have h1 : ENNReal.ofReal P * B.I.muA B.μf B.fund ≤ ENNReal.ofReal (X ^ N) * B.μf B.I.Kset :=
      (ENNReal.div_le_iff hm0 hKsT.ne).1 hVol
    have h2 : B.μf B.I.Kset ≤ ENNReal.ofReal ((B.g : ℝ) ^ (2 * N) * kR) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hKgT, ENNReal.ofReal_pow hg0'.le,
        ENNReal.ofReal_natCast]
      exact hKs
    have h3 : ENNReal.ofReal P * B.I.muA B.μf B.fund ≤
        ENNReal.ofReal (X ^ N * ((B.g : ℝ) ^ (2 * N) * kR)) := by
      rw [ENNReal.ofReal_mul (by positivity)]
      exact h1.trans (by gcongr)
    rw [ENNReal.ofReal_div_of_pos hP0, ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hP0))
      (Or.inl ENNReal.ofReal_ne_top), mul_comm, ← mul_assoc]
    simpa [mul_assoc] using h3

  set Kc : ℝ := Real.exp (-(N : ℝ)) / ((B.g : ℝ) ^ (2 * N) * X ^ N) * B.D * P / kR with hKc
  have hpt : ∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.DeepSet.deepSet B q b,
      ENNReal.ofReal (kern B.I (phe B d) x x).re ≤ ENNReal.ofReal Kc := by
    intro x hx
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.DeepSet.deepSet, Set.mem_setOf_eq] at hx
    apply ENNReal.ofReal_le_ofReal
    have hτ0 : 0 < least B.I x :=
      ((GlobalTheory.T.canonicalLatticeFiltration_size_properties B.I x 1 one_pos).2.2.2.2.2.2.2.2 (by omega)).1
    have hτle : least B.I x ≤ ((B.I.n : ℝ) * B.I.f * B.I.rd * B.g * b)⁻¹ ^ (11 * q) := hx.2.le
    have hk := hK Cg 8 B d p q b c x hCg le_rfl hq hH hc hx.2
    have he := (GlobalTheory.deep_region_exponents B.I.n B.I.f q B.I.rd B.g b (least B.I x) hn8 hf1 hq hqn
      hrd1 hb hgR hτ0 hτle).2
    have hN' : GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B = N := rfl
    have hst : GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * N + N) =
        √(B.I.n : ℝ) * b ^ 2 + 1.5 * (B.I.n : ℝ) ^ ((3 : ℝ) / 2) + 3 * ((8 * q * N + N : ℕ) : ℝ) := by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe
      have : (B.I.n : ℝ) ^ ((3 : ℝ) / 2) = B.I.n * √(B.I.n : ℝ) := by
        rw [Real.sqrt_eq_rpow, show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num,
          Real.rpow_add (by positivity), Real.rpow_one]
      rw [this]; push_cast; ring
    rw [hN', hst] at hk
    rw [hX] at hKc
    have hA : ((2 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.radRh B q (least B.I x) * √(B.I.f : ℝ) *
          (√(B.I.n : ℝ) * b ^ 2 + 1.5 * (B.I.n : ℝ) ^ ((3 : ℝ) / 2) + 3 * ((8 * q * N + N : ℕ) : ℝ))) ^
            (16 * q * N) *
          (6 * (√(B.I.n : ℝ) * b ^ 2 + 1.5 * (B.I.n : ℝ) ^ ((3 : ℝ) / 2) +
            3 * ((8 * q * N + N : ℕ) : ℝ))) ^ N *
          Real.exp B.I.f * (17 * √(B.I.n : ℝ) / least B.I x ^ 2) ^ (2 * N)) *
          ((B.g : ℝ) ^ (2 * N) * ((B.I.n : ℝ) * B.I.f * B.I.rd * B.g * b) ^ N) ≤
          Real.exp (-(N : ℝ)) := by
      rw [show 16 * q * N = 2 * (8 * q * N) by ring]
      refine le_of_eq_of_le ?_ he
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.radRh]
      ring
    have hD : (0 : ℝ) ≤ B.D := Nat.cast_nonneg _
    refine hk.trans ?_
    rw [hKc]
    have hpos : 0 < (B.g : ℝ) ^ (2 * N) * ((B.I.n : ℝ) * B.I.f * B.I.rd * B.g * b) ^ N := by
      rw [← hX]; positivity
    gcongr
    rw [le_div_iff₀ hpos]
    exact hA
  calc ∫⁻ x in GlobalTheory.IndefiniteRowSideFullHecke.DeepSet.deepSet B q b, ENNReal.ofReal (kern B.I (phe B d) x x).re ∂(B.I.muA B.μf)
      ≤ ∫⁻ _ in GlobalTheory.IndefiniteRowSideFullHecke.DeepSet.deepSet B q b, ENNReal.ofReal Kc ∂(B.I.muA B.μf) := by
        first
          | exact setLIntegral_mono measurable_const hpt
          | exact lintegral_mono_ae ((ae_restrict_iff' (by
              simp only [GlobalTheory.IndefiniteRowSideFullHecke.DeepSet.deepSet]; exact (measurableSet_eq_fun_of_countable
                measurable_const measurable_const))).2 (Filter.Eventually.of_forall hpt))
    _ = ENNReal.ofReal Kc * B.I.muA B.μf (GlobalTheory.IndefiniteRowSideFullHecke.DeepSet.deepSet B q b) := setLIntegral_const _ _
    _ ≤ ENNReal.ofReal Kc * B.I.muA B.μf B.fund := by
        gcongr
        intro x hx
        simp only [GlobalTheory.IndefiniteRowSideFullHecke.DeepSet.deepSet, Set.mem_setOf_eq] at hx
        exact hx.1
    _ ≤ ENNReal.ofReal Kc * ENNReal.ofReal (X ^ N * (B.g : ℝ) ^ (2 * N) * kR / P) := by gcongr
    _ = ENNReal.ofReal ((B.D : ℝ) * Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ)))) := by
        rw [← ENNReal.ofReal_mul (by rw [hKc]; positivity)]
        congr 1
        rw [hKc, hN]
        push_cast
        field_simp

end GlobalTheory.DeepRegion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesKernelSummableWithBoundStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discreteSeriesKernel_summable_with_bound : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → 1 ≤ B.I.n → LocDec B h → HBig B 32 h → ∀ x y : B.I.GA, Summable (fun γ : B.I.GFset => ‖phe B d (x⁻¹ * γ.1 * y)‖) ∧ ∑' γ : B.I.GFset, ‖phe B d (x⁻¹ * γ.1 * y)‖ ≤ kerC B d * (tau1 B.I x * tau1 B.I y)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) := by
  first | exact @GlobalTheory.Dec.kernel_abs_bound | exact GlobalTheory.Dec.kernel_abs_bound | (intros; apply GlobalTheory.Dec.kernel_abs_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EventuallyLocalLatticeCompletionEqCoordinateLattStatement
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_localLatticeCompletion_eq_coordinateLattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ) (b : Module.Basis (Fin d) F E) (L : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E L → ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, {X : Fin 1 → Fin n → Fv F v ⊗[F] E | X 0 ∈ GlobalTheory.AdelicU.latLoc F L v} = latV b v := by
  first | exact @GlobalTheory.AdelicU.Cofinite.eventually_latLoc_eq_latV | exact GlobalTheory.AdelicU.Cofinite.eventually_latLoc_eq_latV | (intros; apply GlobalTheory.AdelicU.Cofinite.eventually_latLoc_eq_latV <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContinuousMulEquivCongruenceTopologyAdelicStatement
section
open MeasureTheory Formalism.MainNotions.S Formalism.BasicNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuousMulEquiv_congruenceTopology_adelicUnitary : ∀ (I : AutInst), ∃ e : I.Gf ≃ₜ* Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Af I.F) I.cm.sig I.J, (∀ x, ((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Af I.F) I.cm.sig I.J (e x) : GL (Fin I.n) _) : Matrix (Fin I.n) (Fin I.n) _) = (I.fmat x).map (Algebra.TensorProduct.comm I.F I.E (Af I.F))) ∧ ∀ x, x ∈ I.Kset ↔ GlobalTheory.Mem.Vol.StabHat I.F (I.L : Set (Fin I.n → I.E)) ((I.fmat x).map (Algebra.TensorProduct.comm I.F I.E (Af I.F))) := by
  first | exact @GlobalTheory.CongTop.Swap.exists_continuousMulEquiv_adelic | exact GlobalTheory.CongTop.Swap.exists_continuousMulEquiv_adelic | (intros; apply GlobalTheory.CongTop.Swap.exists_continuousMulEquiv_adelic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsHaarMeasureUnipotentRadicalCovolumeOneStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_haarMeasure_unipotentRadical_covolume_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → ∃ μ : Measure (Nsub (AF F) σ J P), μ.IsHaarMeasure ∧ covol μ = 1 := by
  first | exact @GlobalTheory.NsubHaarCovol.exists_haar_covol_one | exact GlobalTheory.NsubHaarCovol.exists_haar_covol_one | (intros; apply GlobalTheory.NsubHaarCovol.exists_haar_covol_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthComplementUnitVectorSameFieldsStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthComplement_unitVector_same_fields : ∀ (I I' : AutInst) (e : I'.E ≃+* I.E) (s : Bool) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin I'.n) I.E) (xf : I.Gf), IsPerpInst I I' e s x A xf → ∃ (D : Sib I) (B : Matrix (Fin I.n) (Fin D.n) I.E), IsPerp D s x B xf ∧ ∀ (c : InfinitePlace I.F → ℝ) (μ : Measure D.inst.Gf) [SigmaFinite μ] [μ.IsHaarMeasure] (c' : InfinitePlace I'.F → ℝ) (μ' : Measure I'.Gf) [SigmaFinite μ'] [μ'.IsHaarMeasure], IsGaugeAll D.inst c → IsGaugeAll I' c' → gaugeVol D.inst c μ = gaugeVol I' c' μ' := by
  first | exact @GlobalTheory.PerpReduce.exists_sib | exact GlobalTheory.PerpReduce.exists_sib | (intros; apply GlobalTheory.PerpReduce.exists_sib <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSelfDualLatticeCompletionMaxOrderStatement
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_selfDualLattice_completion_maxOrder : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)), IsHermND σ J → Submodule.IsLattice E L → (∀ y : Fin n → E, y ∈ L ↔ ∀ x ∈ L, hE σ J x y ∈ (algebraMap (𝓞 E) E).range) → ∀ v : HeightOneSpectrum (𝓞 F), ∃ Lv : Submodule (GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.maxOrder F E v) (Fin n → Fv F v ⊗[F] E), GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.IsSelfDualLattice σ J v Lv ∧ ∀ y, y ∈ Lv ↔ y ∈ GlobalTheory.AdelicU.latLoc F L v := by
  first | exact @GlobalTheory.CompletedSelfDual.exists_isSelfDualLattice | exact GlobalTheory.CompletedSelfDual.exists_isSelfDualLattice | (intros; apply GlobalTheory.CompletedSelfDual.exists_isSelfDualLattice <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HarishChandraParameterDescentStatement
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harish_chandra_parameter_descent : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (π' : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (lam : Fin n → ℝ), IsParU lam → ∃ m : ℤ, ∑ a, lam a = (m : ℝ) ∧ IsParS (fun a => lam a - (m : ℝ) / n) ∧ (IsHCS ε (fun a => lam a - (m : ℝ) / n) π' → ∃ π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H), Ext ε m π' π ∧ IsHCU ε lam π) := by
  first | exact @GlobalTheory.SUtoU.extension_main | exact GlobalTheory.SUtoU.extension_main | (intros; apply GlobalTheory.SUtoU.extension_main <;> assumption)
end

