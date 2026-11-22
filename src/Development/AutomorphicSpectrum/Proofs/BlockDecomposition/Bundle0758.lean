import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0736
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0741
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0752
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0750
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierZeroHolds
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0370
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PtMMapOfZero
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle0006
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0467
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0495
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousPairProjection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1204
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0723
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0732
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0751
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0592
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0742
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingLatticeRefinementCard
section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair GlobalTheory.CompanionTheory.BZCore
open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.BZCore

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {d : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

theorem ind_eq_sum_reps {L' L : COSub k d} {S : Finset (Fin d → k)} (h : L'.sub ≤ L.sub) (hS : IsReps L' L S)
    (c : Fin d → k) (a : V) : ind L c a = ∑ s ∈ S, ind L' (c + s) a := by
  classical
  refine Subtype.ext (funext fun y => ?_)
  rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
  show (ind L c a).1 y = ∑ s ∈ S, (ind L' (c + s) a).1 y
  simp only [ind_apply]
  have e : ∀ s, y - (c + s) = y - c - s := fun s => by abel
  simp only [e]
  by_cases hy : y - c ∈ L.sub
  · obtain ⟨s, ⟨hs, hys⟩, hu⟩ := hS.2 _ hy
    rw [if_pos hy, Finset.sum_eq_single s, if_pos hys]
    · intro t ht hts
      exact if_neg fun hm => hts (hu t ⟨ht, hm⟩)
    · exact fun hn => (hn hs).elim
  · rw [if_neg hy]
    refine (Finset.sum_eq_zero fun s hs => if_neg fun hm => hy ?_).symm
    simpa using L.sub.add_mem (h hm) (hS.1 s hs)

theorem mL_refine (B : SchF k d V →ₗ[ℂ] SchF k d V' →ₗ[ℂ] ℂ)
    (hT : ∀ x f f', B (shiftF x f) (shiftF x f') = B f f') (L' L : COSub k d) (S : Finset (Fin d → k))
    (h : L'.sub ≤ L.sub) (hS : IsReps L' L S) (x : Fin d → k) (a : V) (a' : V') :
    mL B L x a a' = (S.card : ℂ) * ∑ s ∈ S, mL B L' (x + s) a a' := by
  classical
  have h1 : ∀ y, y ∈ L.sub → ∃ s, s ∈ S ∧ y - s ∈ L'.sub := fun y hy => (hS.2 y hy).exists
  choose! rep hrepS hrep using h1
  have uniq : ∀ y ∈ L.sub, ∀ s ∈ S, y - s ∈ L'.sub → rep y = s := fun y hy s hs hys =>
    (hS.2 y hy).unique ⟨hrepS y hy, hrep y hy⟩ ⟨hs, hys⟩
  have hshift : ∀ t ∈ S, ∑ s ∈ S, mL B L' (x + s - t) a a' = ∑ s ∈ S, mL B L' (x + s) a a' := by
    intro t ht
    have htL := hS.1 t ht
    have hm : ∀ s ∈ S, s - t ∈ L.sub := fun s hs => L.sub.sub_mem (hS.1 s hs) htL
    have hp : ∀ s ∈ S, s + t ∈ L.sub := fun s hs => L.sub.add_mem (hS.1 s hs) htL
    refine Finset.sum_nbij' (fun s => rep (s - t)) (fun s => rep (s + t)) (fun s hs => hrepS _ (hm s hs))
      (fun s hs => hrepS _ (hp s hs)) (fun s hs => ?_) (fun s hs => ?_) (fun s hs => ?_)
    · refine uniq _ (L.sub.add_mem (hS.1 _ (hrepS _ (hm s hs))) htL) s hs ?_
      have := L'.sub.neg_mem (hrep _ (hm s hs))
      have e : rep (s - t) + t - s = -(s - t - rep (s - t)) := by abel
      rwa [e]
    · refine uniq _ (L.sub.sub_mem (hS.1 _ (hrepS _ (hp s hs))) htL) s hs ?_
      have := L'.sub.neg_mem (hrep _ (hp s hs))
      have e : rep (s + t) - t - s = -(s + t - rep (s + t)) := by abel
      rwa [e]
    · have e : x + s - t = x + rep (s - t) + (s - t - rep (s - t)) := by abel
      rw [e, mL_add_mem B L' _ (hrep _ (hm s hs))]
  calc mL B L x a a'
      = B (∑ s ∈ S, ind L' (x + s) a) (∑ t ∈ S, ind L' (0 + t) a') := by
        rw [mL, ← ind_eq_sum_reps h hS, ← ind_eq_sum_reps h hS]
    _ = ∑ t ∈ S, ∑ s ∈ S, mL B L' (x + s - t) a a' := by
        simp only [map_sum, LinearMap.sum_apply, B_ind_ind B hT, zero_add]
    _ = (S.card : ℂ) * ∑ s ∈ S, mL B L' (x + s) a a' := by
        rw [Finset.sum_congr rfl hshift, Finset.sum_const, nsmul_eq_mul]

end GlobalTheory.CompanionTheory.BZCore

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicUnipotentLeviFactorStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolic_unipotent_levi_factor : ∀ (D : D7) (p : ℕ) (q : G D p), q ∈ P D p → ∀ a : GL (Fin p) (AE D), blkA (mat q) = a.1 →
  ∃ (g₁ g₂ : G D p) (b : Mx D p p), q = g₁ * g₂ ∧ mat g₁ = blk4 1 b 0 1 ∧ mat g₂ = blk4 a.1 0 0 (adj (a⁻¹).1) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelNM.unip_mul_levi | exact GlobalTheory.CompanionTheory.SiegelNM.unip_mul_levi | (intros; apply GlobalTheory.CompanionTheory.SiegelNM.unip_mul_levi <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialCoefficientSub
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.PcAdd

theorem iterated_sub {Z X : Type*} [TopologicalSpace Z] [MeasurableSpace Z] [OpensMeasurableSpace Z]
    [TopologicalSpace X] [FirstCountableTopology X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (l : Measure Z) (u : Measure X) [IsFiniteMeasure l] [IsFiniteMeasure u] (a b : X → Z → ℂ) (A B : ℝ)
    (ha : ∀ x, Continuous (a x)) (hb : ∀ x, Continuous (b x))
    (ha' : ∀ z, Continuous fun x => a x z) (hb' : ∀ z, Continuous fun x => b x z)
    (hA : ∀ x z, ‖a x z‖ ≤ A) (hB : ∀ x z, ‖b x z‖ ≤ B) :
    ∫ x, ∫ z, (a x z - b x z) ∂l ∂u = (∫ x, ∫ z, a x z ∂l ∂u) - ∫ x, ∫ z, b x z ∂l ∂u := by
  have key : ∀ c : X → Z → ℂ, ∀ C : ℝ, (∀ x, Continuous (c x)) → (∀ z, Continuous fun x => c x z) →
      (∀ x z, ‖c x z‖ ≤ C) → (∀ x, Integrable (c x) l) ∧ Integrable (fun x => ∫ z, c x z ∂l) u := by
    intro c C hc hc' hC
    have hi : ∀ x, Integrable (c x) l := fun x =>
      Integrable.of_bound (hc x).aestronglyMeasurable C (Eventually.of_forall (hC x))
    refine ⟨hi, ?_⟩
    have hcont : Continuous fun x => ∫ z, c x z ∂l :=
      continuous_of_dominated (bound := fun _ => C) (fun x => (hc x).aestronglyMeasurable)
        (fun x => Eventually.of_forall (hC x)) (integrable_const C) (Eventually.of_forall hc')
    refine Integrable.of_bound hcont.aestronglyMeasurable (C * l.real Set.univ)
      (Eventually.of_forall fun x => ?_)
    exact norm_integral_le_of_norm_le_const (Eventually.of_forall (hC x))
  obtain ⟨i1, j1⟩ := key a A ha ha' hA
  obtain ⟨i2, j2⟩ := key b B hb hb' hB
  rw [← integral_sub j1 j2]
  exact integral_congr_ae (Eventually.of_forall fun x => integral_sub (i1 x) (i2 x))

theorem firstCountable_of_second (X : Type*) [TopologicalSpace X] [SecondCountableTopology X] :
    FirstCountableTopology X := inferInstance

theorem pc_sub : PcBound → ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (m : Meas D ρ p)
    (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) (F F' : G D n → ℂ), Continuous F →
    LeftInv (GF D n) F → Continuous F' → LeftInv (GF D n) F' → ∀ (y : Mx D ρ p) (g : G D n),
    pc M m ψ b₀ (F - F') (M.sh y * g) = pc M m ψ b₀ F (M.sh y * g) - pc M m ψ b₀ F' (M.sh y * g) := by
  intro hP D n ρ p hn M m ψ hψ b₀ F F' hF hFi hF' hFi' y g
  obtain ⟨C, hC, hCm, -⟩ := (hP D n ρ p hn M m ψ hψ b₀).2 (g)
  haveI : BorelSpace (Mx D ρ p) := ⟨rfl⟩
  haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  haveI : BorelSpace (hermA D ρ) := Subtype.borelSpace _
  haveI : SecondCountableTopology (Mx D ρ p) := (GlobalTheory.MixModel.lattice_Mx D ρ p).2.2.1
  haveI : FirstCountableTopology (Mx D ρ p) := firstCountable_of_second _
  haveI h1 : IsFiniteMeasure (m.lz.restrict m.𝓖) :=
    ⟨by rw [Measure.restrict_apply_univ, m.hz.2.2]; exact ENNReal.one_lt_top⟩
  haveI h2 : IsFiniteMeasure (m.μ.restrict m.𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, m.hμ.2.2]; exact ENNReal.one_lt_top⟩
  have hchz : Continuous fun z : hermA D ρ => conj (chz ψ b₀ z) :=
    Complex.continuous_conj.comp
      (hψ.1.comp ((GlobalTheory.CompanionTheory.FourierN.continuous_pr b₀.1).comp continuous_subtype_val))
  have hnorm : ∀ z, ‖conj (chz ψ b₀ z)‖ = 1 := fun z => by
    rw [RCLike.norm_conj]
    exact hψ.2.1 _
  have hz : ∀ x, Continuous fun z : hermA D ρ => M.nzx z 0 * (M.nzx 0 x * (M.sh y * g)) := fun x =>
    (M.nzx_cont.comp (continuous_id.prodMk continuous_const)).mul continuous_const
  have hx : ∀ z, Continuous fun x : Mx D ρ p => M.nzx z 0 * (M.nzx 0 x * (M.sh y * g)) := fun z =>
    continuous_const.mul ((M.nzx_cont.comp (continuous_const.prodMk continuous_id)).mul continuous_const)
  have bd : ∀ Φ : G D n → ℂ, Continuous Φ → LeftInv (GF D n) Φ →
      ∃ B : ℝ, ∀ x z, ‖Φ (M.nzx z 0 * (M.nzx 0 x * (M.sh y * g))) * conj (chz ψ b₀ z)‖ ≤ B := by
    intro Φ hΦ hi
    obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hΦ.continuousOn
    refine ⟨B, fun x z => ?_⟩
    obtain ⟨γ, hγ, hc⟩ := hCm z x y
    rw [norm_mul, hnorm, mul_one, ← hi γ hγ]
    exact hB _ hc
  obtain ⟨A, hA⟩ := bd F hF hFi
  obtain ⟨B, hB⟩ := bd F' hF' hFi'
  have key := iterated_sub (m.lz.restrict m.𝓖) (m.μ.restrict m.𝓕)
    (fun x z => F (M.nzx z 0 * (M.nzx 0 x * (M.sh y * g))) * conj (chz ψ b₀ z))
    (fun x z => F' (M.nzx z 0 * (M.nzx 0 x * (M.sh y * g))) * conj (chz ψ b₀ z)) A B
    (fun x => (hF.comp (hz x)).mul hchz) (fun x => (hF'.comp (hz x)).mul hchz)
    (fun z => (hF.comp (hx z)).mul continuous_const) (fun z => (hF'.comp (hx z)).mul continuous_const) hA hB
  simp only [PositivityTheory.Rg.Rsw.pc, PositivityTheory.Rg.Rsw.zc, Pi.sub_apply, sub_mul]
  exact key

end GlobalTheory.CompanionTheory.PcAdd

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PtMulComplSelf
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Cell

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.CellDecomp

section Weyl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem matHom_proj_weyl (σ : E →ₐ[F] E) (J : Matrix (Fin (n + n)) (Fin (n + n)) E)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (g : GAd σ J)
    (hg : (matHom _ σ J g).1 = blk4 0 1 (-1) 0) :
    (matHom _ σ J (proj σ J v g)).1 = blk4 (0 : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) 1 (-1) 0 := by
  rw [matHom_proj, bc_val, hg]
  exact weyl_map _

theorem stab_of_weyl (σ : E →ₐ[F] E) (J : Matrix (Fin (n + n)) (Fin (n + n)) E)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (k : GLoc σ J v)
    (hk : (matHom _ σ J k).1 = blk4 (0 : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) 1 (-1) 0) :
    k ∈ stabLoc σ J (stdLattice E (n + n)) v := by
  rw [stabLoc, Subgroup.mem_comap]
  change ∀ x, x ∈ latLoc F (stdLattice E (n + n)) v ↔ (↑(matHom _ σ J k) : Matrix _ _ _).mulVec x ∈ latLoc F (stdLattice E (n + n)) v
  rw [hk]
  have hmap : ∀ y ∈ latLoc F (stdLattice E (n + n)) v,
      (blk4 (0 : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) 1 (-1) 0).mulVec y ∈ latLoc F (stdLattice E (n + n)) v := by
    intro y hy
    change y ∈ AddSubgroup.closure _ at hy
    change _ ∈ AddSubgroup.closure _
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      apply AddSubgroup.subset_closure
      refine ⟨a, ha, (blk4 (0 : Matrix (Fin n) (Fin n) E) 1 (-1) 0).mulVec x, ?_, ?_⟩
      · change _ ∈ Submodule.pi _ _ at hx ⊢
        rw [Submodule.mem_pi] at hx ⊢
        intro j _
        obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective j
        rcases s with i | i
        · rw [(weyl_mulVec x i).1]
          exact hx _ (Set.mem_univ _)
        · rw [(weyl_mulVec x i).2]
          exact neg_mem (hx _ (Set.mem_univ _))
      · funext j
        obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective j
        rcases s with i | i
        · rw [(weyl_mulVec _ i).1, (weyl_mulVec x i).1]
        · rw [(weyl_mulVec _ i).2, (weyl_mulVec x i).2, TensorProduct.tmul_neg]
    | zero =>
      rw [Matrix.mulVec_zero]
      exact zero_mem _
    | add y z _ _ hy hz =>
      rw [Matrix.mulVec_add]
      exact add_mem hy hz
    | neg y _ hy =>
      rw [Matrix.mulVec_neg]
      exact neg_mem hy
  have hWW : ∀ y : Fin (n + n) → Fv F v ⊗[F] E,
      (blk4 (0 : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) 1 (-1) 0).mulVec
        ((blk4 (0 : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) 1 (-1) 0).mulVec y) = -y := by
    intro y
    funext j
    obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective j
    rcases s with i | i
    · rw [(weyl_mulVec _ i).1, (weyl_mulVec y i).2, Pi.neg_apply]
    · rw [(weyl_mulVec _ i).2, (weyl_mulVec y i).1, Pi.neg_apply]
  intro x
  constructor
  · exact hmap x
  · intro hx
    have h2 := neg_mem (hmap _ hx)
    rwa [hWW, neg_neg] at h2

end Weyl

section Main

variable {D : D7} {n : ℕ}

theorem pt_comm {e : AE D} (he : e * e = e) (hc : cA D e = e) (he' : (1 - e) * (1 - e) = 1 - e)
    (hc' : cA D (1 - e) = 1 - e) (x y : G D n) :
    pt e he hc x * pt (1 - e) he' hc' y = pt (1 - e) he' hc' y * pt e he hc x := by
  apply mat_inj
  rw [mat_mul', mat_mul', mat_pt, mat_pt, (ptM_mul_compl he he' _ _).1, (ptM_mul_compl he he' _ _).2]

theorem pt_mul_compl_self {e : AE D} (he : e * e = e) (hc : cA D e = e) (he' : (1 - e) * (1 - e) = 1 - e)
    (hc' : cA D (1 - e) = 1 - e) (x : G D n) : pt e he hc x * pt (1 - e) he' hc' x = x := by
  apply mat_inj
  rw [mat_mul', mat_pt, mat_pt, (ptM_mul_compl he he' _ _).1, ← add_smul, add_sub_cancel, one_smul]

theorem pt_nb {e : AE D} (he : e * e = e) (hc : cA D e = e) {nb : hermA D n → G D n} (hnb : IsNMap nb)
    (x : hermS D n e) : pt e he hc (nb x.1) = nb x.1 := by
  apply mat_inj
  rw [mat_pt, hnb, ptM_unip he x.2]

theorem proj_weyl {w : G D n} (hw : IsW w) (v : Pl D) :
    proj D.sp.cm.sig (Jst D n) v w ∈ stabLoc D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) v := by
  exact stab_of_weyl _ _ v _ (matHom_proj_weyl _ _ v w hw)

theorem proj_pt_zero {f : AE D} (hf : f * f = f) (hc : cA D f = f) (x : G D n) {v : Pl D} (h : cv D v f = 0) :
    proj D.sp.cm.sig (Jst D n) v (pt f hf hc x) = 1 := by
  refine matHom_injective _ _ _ (Units.ext ?_)
  rw [matHom_proj, map_one, bc_val]
  exact ptM_map_of_zero (cv D v) hf h (mat x)

theorem proj_pt_one {f : AE D} (hf : f * f = f) (hc : cA D f = f) (x : G D n) {v : Pl D} (h : cv D v f = 1) :
    proj D.sp.cm.sig (Jst D n) v (pt f hf hc x) = proj D.sp.cm.sig (Jst D n) v x := by
  refine matHom_injective _ _ _ (Units.ext ?_)
  rw [matHom_proj, matHom_proj, bc_val, bc_val]
  exact ptM_map_of_one (cv D v) hf h (mat x)

theorem projArch_pt_zero {f : AE D} (hf : f * f = f) (hc : cA D f = f) (x : G D n) {w : NumberField.InfinitePlace D.host.F}
    (h : compInf D.host.F D.host.E w f = 0) : projArch D.sp.cm.sig (Jst D n) w (pt f hf hc x) = 1 := by
  refine matHom_injective _ _ _ (Units.ext ?_)
  rw [matHom_projArch, map_one, bc_val]
  exact ptM_map_of_zero (compInf D.host.F D.host.E w) hf h (mat x)

theorem cv_of_mem {S : Finset (Pl D)} {e : AE D} (hS : IsIdem S e) {v : Pl D} (hv : v ∈ S) : cv D v e = 1 := by
  rw [hS.2 v, if_pos hv]

theorem cv_of_not_mem {S : Finset (Pl D)} {e : AE D} (hS : IsIdem S e) {v : Pl D} (hv : v ∉ S) : cv D v e = 0 := by
  rw [hS.2 v, if_neg hv]

theorem pt_mem_KOff {S : Finset (Pl D)} {e : AE D} (hS : IsIdem S e) (he' : (1 - e) * (1 - e) = 1 - e)
    (hc' : cA D (1 - e) = 1 - e) {x : G D n}
    (hx : ∀ v, proj D.sp.cm.sig (Jst D n) v x ∈ stabLoc D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) v) :
    pt (1 - e) he' hc' x ∈ KOff D n S := by
  refine mem_levelOff.2 ⟨mem_finPts_iff_forall.2 fun w => ?_, fun v hv => ?_, fun v hv => ?_⟩
  · exact projArch_pt_zero he' hc' x (map_compl_zero _ (hS.1 w))
  · exact proj_pt_zero he' hc' x (map_compl_zero _ (cv_of_mem hS hv))
  · rw [proj_pt_one he' hc' x (map_compl_one _ (cv_of_not_mem hS hv))]
    exact hx v

theorem mat_inv_wn {w : G D n} (hw : IsW w) {nb : hermA D n → G D n} (hnb : IsNMap nb) (y : hermA D n) :
    mat (w * nb y)⁻¹ = blk4 (-y.1) (-1) 1 0 := by
  have hw' : mat w = blk4 0 1 (-1) 0 := hw
  have h1 : mat (w * nb y) * blk4 (-y.1) (-1) 1 0 = 1 := by
    rw [mat_mul', hw', hnb, weyl_inv]
  have h2 : mat (w * nb y)⁻¹ * mat (w * nb y) = 1 := by
    rw [← mat_mul', inv_mul_cancel, mat_one']
  calc mat (w * nb y)⁻¹ = mat (w * nb y)⁻¹ * (mat (w * nb y) * blk4 (-y.1) (-1) 1 0) := by
        rw [h1, mul_one]
    _ = blk4 (-y.1) (-1) 1 0 := by rw [← mul_assoc, h2, one_mul]

theorem cB_quot {e : AE D} (he : e * e = e) (hc : cA D e = e) {w : G D n} (hw : IsW w) {nb : hermA D n → G D n}
    (hnb : IsNMap nb) (g : G D n) (y : hermA D n) (hy : mm (e • cB g) y.1 = e • dB g) :
    cB (pt e he hc (g * (w * nb y)⁻¹)) = 0 := by
  rw [cB_pt, cB_mul, blkA_of (mat_inv_wn hw hnb y), cB_of (mat_inv_wn hw hnb y)]
  exact cell_alg hy

theorem cB_off {f : AE D} (hf : f * f = f) (hc : cA D f = f) {q : G D n} (hq : q ∈ P D n) :
    cB (pt f hf hc q) = 0 := by
  rw [cB_pt, cB_of_mem_P hq, smul_zero]

theorem decomp (hI : IdemEx) : Decomp := by
  intro D p nb hnb w hw S e hS g _ y hy
  obtain ⟨he, hc⟩ := (hI D S).2 e hS
  have he' := idem_compl he
  have hc' : cA D (1 - e) = 1 - e := by rw [map_sub, map_one, hc]
  obtain ⟨q₀, hq₀, k₀, hk₀, hgk⟩ := GlobalTheory.StdUnn.Iwasawa.exists_mul D p g
  have hA : pt e he hc (nb y.1) = nb y.1 := pt_nb he hc hnb y
  have key := assemble (pt e he hc) (pt (1 - e) he' hc') (pt_comm he hc he' hc')
    (pt_mul_compl_self he hc he' hc') (w := w) hA hgk
  refine ⟨pt e he hc (g * (w * nb y.1)⁻¹) * pt (1 - e) he' hc' q₀, ?_, pt (1 - e) he' hc' (w⁻¹ * k₀), ?_, key, ?_⟩
  · exact mul_mem (mem_siegelParabolic_of_lowerLeft_eq_zero (cB_quot he hc hw hnb g y.1 hy)) (mem_siegelParabolic_of_lowerLeft_eq_zero (cB_off he' hc' hq₀))
  · apply pt_mem_KOff hS he' hc'
    intro v
    have hk : proj D.sp.cm.sig (Jst D p) v k₀ ∈
        stabLoc D.sp.cm.sig (Jst D p) (stdLattice D.host.E (p + p)) v :=
      Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hk₀).1 v
    rw [map_mul, map_inv]
    exact mul_mem (inv_mem (proj_weyl hw v)) hk
  · intro x
    rw [← pt_nb he hc hnb x]
    exact pt_comm he hc he' hc' _ _

end Main

end GlobalTheory.CompanionTheory.CellDecomp

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictedProductIntegralStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.FA
open scoped Classical
open GlobalTheory.CompanionTheory.FinActS

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restricted_product_integral : ∀ {ι Γ : Type} [Group Γ] {Hl : ι → Type} [∀ i, Group (Hl i)] (p : ∀ i, Γ →* Hl i) (e : ∀ i, Hl i →* Γ) (K : Subgroup Γ) (KH V : ∀ i, Subgroup (Hl i))
    (f : ∀ i, Hl i → ℂ)
    (hpe : ∀ i m, p i (e i m) = m) (hpe' : ∀ i j m, i ≠ j → p j (e i m) = 1)
    (hsep : ∀ x y : Γ, (∀ i, p i x = p i y) → x = y)
    (hev : ∀ x, ∀ᶠ i in cofinite, p i x ∈ KH i)
    (hK : ∀ x, x ∈ K ↔ ∀ i, p i x ∈ KH i)
    (hVK : ∀ i, V i ≤ KH i) (hVi : ∀ i, (V i).relIndex (KH i) ≠ 0)
    (hVe : ∀ᶠ i in cofinite, V i = KH i ∧ f i = (KH i : Set (Hl i)).indicator 1)
    (hfV : ∀ i, ∀ u ∈ V i, ∀ x, f i (x * u) = f i x)
    (hfs : ∀ i, {q : Hl i ⧸ V i | f i q.out ≠ 0}.Finite)
    (g : Γ → ℂ) (hg : ∀ u, (∀ i, p i u ∈ V i) → ∀ x, g (x * u) = g x)
    (l : List ι) (hl : l.Nodup)
    (hfix : ∀ i, i ∉ l → (fun x => hint (KH i) fun m => f i m * g (x * e i m)) = g),
    hint K (fun x => (∏ᶠ i, f i (p i x)) * g x) =
      l.foldr (fun i g' x => hint (KH i) fun m => f i m * g' (x * e i m)) g 1 := by
  first | exact @GlobalTheory.CompanionTheory.FinActCore.hint_prod_eq_foldr | exact GlobalTheory.CompanionTheory.FinActCore.hint_prod_eq_foldr | (intros; apply GlobalTheory.CompanionTheory.FinActCore.hint_prod_eq_foldr <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReverseOrderedProductHasSocleStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reverse_ordered_product_has_socle : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → LSegJacquet k → LUnlinkedIrr k → LUnlinkedComm k → ∀ {h N : ℕ} (Γ : Fin h → Segment k) (y : Fin h → IrrGL k) (hd : ∑ a, (y a).1 = N), IsRevOrdered Γ → (∀ i, IsLSeg (Γ i) (y i).rep) → ∃ τ : IrrRep (GL (Fin N) k), IsSocle τ.ρ (prodIrr y hd) := by
  first | exact @GlobalTheory.CompanionTheory.SocleRev.exists_isSocle_prodIrr_of_isRevOrdered | exact GlobalTheory.CompanionTheory.SocleRev.exists_isSocle_prodIrr_of_isRevOrdered | (intros; apply GlobalTheory.CompanionTheory.SocleRev.exists_isSocle_prodIrr_of_isRevOrdered <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightDerivativeLowerBlockAtOneStatement
section
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.right_derivative_lower_block_at_one : ∀ (n : ℕ) (lev : Fin n → ℕ) (f h : GlobalTheory.CompanionTheory.ModelS.SmF n), f ∈ GlobalTheory.CompanionTheory.ModelS.Eqv lev f.1 → f.1 1 = 1 → h ∈ GlobalTheory.CompanionTheory.ModelS.Eqv lev f.1 → ∀ X : Mat n, (∀ a b, lev a < lev b → X a b = 0) → (GlobalTheory.CompanionTheory.ModelS.DR X h).1 1 = (GlobalTheory.CompanionTheory.ModelS.DR X f).1 1 * h.1 1 := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.DR_one_of_eqv | exact GlobalTheory.CompanionTheory.ModelS.DR_one_of_eqv | (intros; apply GlobalTheory.CompanionTheory.ModelS.DR_one_of_eqv <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightDerivativePreservesEquivariantStatement
section
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.right_derivative_preserves_equivariant : ∀ (n : ℕ) (lev : Fin n → ℕ) (φ : Mat n → ℂ) (X : Mat n) (h : GlobalTheory.CompanionTheory.ModelS.SmF n), h ∈ GlobalTheory.CompanionTheory.ModelS.Eqv lev φ → GlobalTheory.CompanionTheory.ModelS.DR X h ∈ GlobalTheory.CompanionTheory.ModelS.Eqv lev φ := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.DR_mem_Eqv | exact GlobalTheory.CompanionTheory.ModelS.DR_mem_Eqv | (intros; apply GlobalTheory.CompanionTheory.ModelS.DR_mem_Eqv <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightDerivativeRealLieHomStatement
section
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.right_derivative_real_lie_hom : ∀ (n : ℕ), (∀ X Y : Mat n, GlobalTheory.CompanionTheory.ModelS.DR (X + Y) = GlobalTheory.CompanionTheory.ModelS.DR X + GlobalTheory.CompanionTheory.ModelS.DR Y) ∧ (∀ (r : ℝ) (X : Mat n), GlobalTheory.CompanionTheory.ModelS.DR ((r : ℂ) • X) = (r : ℂ) • GlobalTheory.CompanionTheory.ModelS.DR X) ∧ (∀ X Y : Mat n, GlobalTheory.CompanionTheory.ModelS.DR (X * Y - Y * X) = GlobalTheory.CompanionTheory.ModelS.DR X * GlobalTheory.CompanionTheory.ModelS.DR Y - GlobalTheory.CompanionTheory.ModelS.DR Y * GlobalTheory.CompanionTheory.ModelS.DR X) := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.LieAct.DR_lie | exact GlobalTheory.CompanionTheory.ModelS.LieAct.DR_lie | (intros; apply GlobalTheory.CompanionTheory.ModelS.LieAct.DR_lie <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentLengthTwoIrreducibleSubStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.segment_length_two_irreducible_sub : (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ), 0 < d →
    ∀ σ : IrrRep (GL (Fin d) k), IsCuspidal σ.ρ →
      ¬ (multiProd (GlobalTheory.Published.consecBlocks 2 d) (segTerm σ.ρ 2)).IsIrreducible) →
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ), 0 < d →
    ∀ σ : IrrRep (GL (Fin d) k), IsCuspidal σ.ρ →
      ∃ S : Subrepresentation (multiProd (GlobalTheory.Published.consecBlocks 2 d) (segTerm σ.ρ 2)),
        S.toRepresentation.IsIrreducible ∧
        (∀ S' : Subrepresentation (multiProd (GlobalTheory.Published.consecBlocks 2 d) (segTerm σ.ρ 2)),
          S'.toRepresentation.IsIrreducible → S' = S) ∧
        Nonempty ((jac (GlobalTheory.Published.consecBlocks 2 d) S.toRepresentation).Equiv (piTensor (segTerm σ.ρ 2))) := by
  first | exact @GlobalTheory.CompanionTheory.SegTwo.segment_two | exact GlobalTheory.CompanionTheory.SegTwo.segment_two | (intros; apply GlobalTheory.CompanionTheory.SegTwo.segment_two <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilConvergentRangeStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_weil_convergent_range : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
  ∀ n : ℕ, 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ dx : Measure (Fin n → Fin M → AF F ⊗[F] E), SdW F E σ M J (AF F) ψ n dx →
  ∀ db : Measure (HermR (AF F) σ n), SdHerm F E σ (AF F) ψ n db →
  ∀ Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ, GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat Φ →
    Integrable (starN σ J ψ dx Φ) db := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.integrable_starN | exact GlobalTheory.CompanionTheory.SiegelND.Integ.integrable_starN | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.integrable_starN <;> assumption)
end

