import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0642
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0646
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0658
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0616
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0676
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0681
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0480
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0551
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0645
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsEqSmulOfInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationInvariantFunctionalRestrict
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0250
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0133
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0224
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsClopenCompactNbhdZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntOffOfSmul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0672
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.PullHEq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HdgAffIso
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import GroundTheory.AutomorphicForms.CuspidalDiscreteness
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0015
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0523
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0522
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0026
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0058
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0580
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0042
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0061
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0062
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0024
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0593
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0675
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HodgeC

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousIpFst
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Em
open IsDedekindDomain NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.OrbExist

variable {D : D7} {a n r t : ℕ}

theorem continuous_qv (V : HSp D) (b₀ : HermE D r) :
    Continuous (fun z : Mx D V.rank r × Mx D V.rank t => qv V b₀ z) := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have hip : ∀ {X : Type} [TopologicalSpace X] {a c : ℕ} {f : X → Mx D V.rank a} {g : X → Mx D V.rank c},
      Continuous f → Continuous g → Continuous (fun x => ip V (f x) (g x)) := by
    intro X _ a c f g hf hg
    unfold ip
    exact (continuous_adj.comp hf).matrix_mul (continuous_const.matrix_mul hg)
  have hyv : Continuous (fun z : Mx D V.rank r × Mx D V.rank t => yv V b₀ z) := by
    unfold yv
    exact continuous_const.matrix_mul (hip continuous_fst continuous_snd)
  have hpr : Continuous (fun x : Mx D V.rank r × Mx D V.rank t => pr b₀ (yv V b₀ x) (yv V b₀ x)) := by
    unfold pr
    exact (continuous_adj.comp hyv).matrix_mul (continuous_const.matrix_mul hyv)
  unfold qv
  have h1 : Continuous (fun z : Mx D V.rank r × Mx D V.rank t => ip V z.2 z.2) := hip continuous_snd continuous_snd
  have hn : ContinuousNeg (AE D) := IsTopologicalRing.toContinuousNeg
  have ha : ContinuousAdd (AE D) := IsTopologicalSemiring.toContinuousAdd
  exact continuous_matrix fun i j => (h1.matrix_elem i j).add (hpr.matrix_elem i j).neg |>.congr fun z => (sub_eq_add_neg _ _).symm

theorem continuous_ip_fst (V : HSp D) :
    Continuous (fun z : Mx D V.rank r × Mx D V.rank t => ip V z.1 z.1) := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  unfold ip
  exact (continuous_adj.comp continuous_fst).matrix_mul (continuous_const.matrix_mul continuous_fst)

theorem continuous_pch₂ {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {X : Type} [TopologicalSpace X]
    {f g : X → Mx D t t} (hf : Continuous f) (hg : Continuous g) : Continuous (fun x => pch ψ (f x) (g x)) := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have htr : Continuous (trA : AE D → AF D.host.F) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D))
  have hhalf : Continuous (halfTr : AE D → AF D.host.F) := by
    unfold halfTr
    exact continuous_const.mul htr
  unfold pch
  exact hψ.1.comp (hhalf.comp (hf.matrix_mul hg).matrix_trace)

theorem isClosed_fixed (e : AE D) :
    IsClosed {z : Mx D a r × Mx D a t | e • z.1 = z.1 ∧ e • z.2 = z.2} := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  obtain ⟨-, -, -, h1, -⟩ := GlobalTheory.CompanionTheory.ColumnSplitting.top_mx (D := D) a r
  obtain ⟨-, -, -, h2, -⟩ := GlobalTheory.CompanionTheory.ColumnSplitting.top_mx (D := D) a t
  have c1 : Continuous fun x : Mx D a r => e • x := continuous_const_smul e
  have c2 : Continuous fun x : Mx D a t => e • x := continuous_const_smul e
  exact (isClosed_eq (c1.comp continuous_fst) continuous_fst).inter (isClosed_eq (c2.comp continuous_snd) continuous_snd)

theorem conj_cancel (g : GL (Fin t) (AE D)) (q : Mx D t t) :
    mm (mm (adj (g⁻¹).1) (mm (mm (adj g.1) q) g.1)) (g⁻¹).1 = q := by
  have h1 : g.1 * (g⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2 : (adj (g⁻¹).1 * adj g.1 : Mx D t t) = 1 := by
    have := adj_mul (D := D) g.1 (g⁻¹).1
    rw [← this, h1, adj_one_r]
  simp only [mm]
  calc _ = (adj (g⁻¹).1 * adj g.1 : Mx D t t) * q * (g.1 * (g⁻¹).1) := by simp only [Matrix.mul_assoc]
    _ = q := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

theorem comp_mem {θ : InfFam D} (hθ : IsInfFam θ) {hn : r + t = n} {S : Finset (Pl D)} {e : AE D} (hS : IsIdem S e)
    (hR : ∀ f ∈ algA (a := a) θ hn S e,
      ∃ Φ ∈ schwartzA θ a n, Good S e Φ ∧ HasCompactSupport Φ ∧ f = fun z => Φ (jn hn z.1.1 z.1.2))
    (hSt : AlgStab) (h : GL (Fin a) (AE D)) (g : GL (Fin n) (AE D)) (hh : e • (h.1 - 1) = h.1 - 1) (hg : e • (g.1 - 1) = g.1 - 1)
    (Θ : XS D a r t e → XS D a r t e)
    (hΘ : ∀ z, jn hn (Θ z).1.1 (Θ z).1.2 = mm (mm h.1 (jn hn z.1.1 z.1.2)) g.1) (f : XS D a r t e → ℂ)
    (hf : f ∈ algA (a := a) θ hn S e) : f ∘ Θ ∈ algA (a := a) θ hn S e := by
  obtain ⟨Φ, h1, h2, h3, rfl⟩ := hR f hf
  obtain ⟨m1, m2, m3⟩ := hSt D θ hθ a n S e hS h g hh hg Φ h1 h2 h3
  refine Submodule.subset_span ⟨_, m1, m2, m3, ?_⟩
  funext z
  simp only [Function.comp, hΘ]

theorem trans_int₁ {X N : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [TopologicalSpace N] [MeasurableSpace N]
    [BorelSpace N] (σ : Measure X) (lam : Measure N) (k : N → X → ℂ) (f : X → ℂ) (Θ : X ≃ₜ X)
    (h₁ : σ.map Θ = σ) (hk : ∀ x, ∀ᵐ z ∂σ, k x z = k x (Θ z)) :
    ∫ x, ∫ z, f (Θ z) * k x z ∂σ ∂lam = ((1 : ℝ≥0) : ℂ) * ∫ x, ∫ z, f z * k x z ∂σ ∂lam := by
  have := trans_int σ lam k f Θ (Homeomorph.refl N) 1 1 (by rw [one_smul]; exact h₁) (by simp) hk
  simpa using this

theorem kap (A : ℝ≥0) (hA : A ≠ 0) (N r t : ℕ) (hN : N = r + 2 * t) : (A⁻¹) ^ N * ((A⁻¹)⁻¹) ^ t = (A⁻¹) ^ (r + t) := by
  subst hN
  rw [inv_inv, two_mul, ← add_assoc, pow_add, mul_assoc, ← mul_pow, inv_mul_cancel₀ hA, one_pow, mul_one]

theorem absA_inv (D : D7) (u : (AE D)ˣ) : absA D u⁻¹ = (absA D u)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← map_mul, inv_mul_cancel, map_one]

theorem absA_ne (D : D7) (u : (AE D)ˣ) : absA D u ≠ 0 := by
  have h1 : absA D u * absA D u⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  intro h
  rw [h, zero_mul] at h1
  exact zero_ne_one h1

end GlobalTheory.CompanionTheory.OrbExist

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMulLeftFin
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology SchwartzMap
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Em

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.AlgRich

variable {D : D7}

variable {a r t n : ℕ} {S : Finset (Pl D)} {e : AE D}

theorem theta_idem {θ : InfFam D} (hθ : IsInfFam θ) (hid : IsIdem S e) (τ : D.what₂.Tau) : θ τ (infPart D e) = 1 := by
  have h := ((GlobalTheory.StdUnn.RealComp.real_components D θ hθ).1 (e - 1)).1 (fun w => by
    rw [RingHom.map_sub, hid.1 w, map_one, sub_self])
  have h' := h τ
  rw [RingHom.map_sub, RingHom.map_sub, map_one, map_one, sub_eq_zero] at h'
  exact h'

theorem clopen_sep (D : D7) {x y : Af D.host.F ⊗[D.host.F] D.host.E} (h : x ≠ y) :
    ∃ U : Set (Af D.host.F ⊗[D.host.F] D.host.E), IsClopen U ∧ x ∈ U ∧ y ∉ U := by
  have hne : GlobalTheory.AfTensNbhd.coordEquiv D.host.F D.host.E x ≠ GlobalTheory.AfTensNbhd.coordEquiv D.host.F D.host.E y :=
    fun h' => h ((GlobalTheory.AfTensNbhd.coordEquiv D.host.F D.host.E).injective h')
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hne
  haveI : T2Space (Af D.host.F) := GlobalTheory.IntegralFinAdele.t2Space_finiteAdeleRing' D.host.F
  have hd : GlobalTheory.AfTensNbhd.coordEquiv D.host.F D.host.E y k - GlobalTheory.AfTensNbhd.coordEquiv D.host.F D.host.E x k ≠ 0 :=
    sub_ne_zero.2 hk.symm
  obtain ⟨G, hGo, hGs⟩ := GlobalTheory.SmallLevel.exists_open_subgroup D.host.F
    {GlobalTheory.AfTensNbhd.coordEquiv D.host.F D.host.E y k - GlobalTheory.AfTensNbhd.coordEquiv D.host.F D.host.E x k}ᶜ
    (isOpen_compl_singleton.mem_nhds (by simpa using hd.symm))
  have hGc : IsClosed (G : Set (Af D.host.F)) := G.isClosed_of_isOpen hGo
  have hcont : Continuous fun w => GlobalTheory.AfTensNbhd.coordEquiv D.host.F D.host.E w k -
      GlobalTheory.AfTensNbhd.coordEquiv D.host.F D.host.E x k :=
    ((continuous_apply k).comp (GlobalTheory.AfTensNbhd.continuous_coordEquiv _ _)).sub continuous_const
  refine ⟨(fun w => GlobalTheory.AfTensNbhd.coordEquiv D.host.F D.host.E w k -
      GlobalTheory.AfTensNbhd.coordEquiv D.host.F D.host.E x k) ⁻¹' G, ⟨hGc.preimage hcont, hGo.preimage hcont⟩, ?_, ?_⟩
  · simp
  · intro hy
    exact hGs hy rfl

theorem continuous_mul_left_fin (D : D7) (c : Af D.host.F ⊗[D.host.F] D.host.E) :
    Continuous fun y : Af D.host.F ⊗[D.host.F] D.host.E => c * y := by
  haveI : IsModuleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Af D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (Af D.host.F) _
  exact continuous_const.mul continuous_id

theorem sep_pts {θ : InfFam D} (hθ : IsInfFam θ) (hid : IsIdem S e) (he : e * e = e) {p q : Mx D a n}
    (hp : e • p = p) (hq : e • q = q) (hpq : p ≠ q) {B : Mx D a n → ℂ} (hB : B ∈ schwartzA θ a n) (hG : Good S e B)
    (hC : HasCompactSupport B) (Bp : B p = 1) (Bq : B q = 1) :
    ∃ Φ ∈ schwartzA θ a n, Good S e Φ ∧ HasCompactSupport Φ ∧ Φ p ≠ Φ q := by
  have hsm : ∀ (x : Mx D a n) i j, (e • x) i j = e * x i j := fun _ _ _ => rfl
  by_cases hf : p.map (finPart D) = q.map (finPart D)
  · have hi : ¬ ∀ τ, compAt θ τ p = compAt θ τ q := fun h => hpq (GlobalTheory.StabAtPlace.mx_ext hθ hf h)
    simp only [not_forall] at hi
    obtain ⟨τ, hτ⟩ := hi
    obtain ⟨i, j, hij⟩ : ∃ i j, compAt θ τ p i j ≠ compAt θ τ q i j := by
      by_contra hc
      simp only [not_exists, not_not] at hc
      exact hτ (Matrix.ext hc)
    let L : (D.what₂.Tau → Fin a → Fin n → ℂ) →L[ℝ] ℂ :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) j).comp
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin a => Fin n → ℂ) i).comp
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : D.what₂.Tau => Fin a → Fin n → ℂ) τ))
    refine ⟨_, GlobalTheory.CompanionTheory.WSum.mul_mem_schwartzA D θ a n L L.hasTemperateGrowth _ hB, ?_, hC.mul_left, ?_⟩
    · refine good_factor (M := fun x => L fun τ i j => compAt θ τ x i j) (fun x => ?_) hG
      show θ τ (infPart D (e * x i j)) = θ τ (infPart D (x i j))
      rw [map_mul, map_mul, theta_idem hθ hid, one_mul]
    · show compAt θ τ p i j * B p ≠ compAt θ τ q i j * B q
      rw [Bp, Bq, mul_one, mul_one]
      exact hij
  · obtain ⟨i, j, hij⟩ : ∃ i j, finPart D (p i j) ≠ finPart D (q i j) := by
      by_contra hc
      simp only [not_exists, not_not] at hc
      exact hf (Matrix.ext hc)
    obtain ⟨U, hU, hxU, hyU⟩ := clopen_sep D hij
    have hI : IsLocallyConstant (U.indicator fun _ => (1 : ℂ)) :=
      (LocallyConstant.indicator (LocallyConstant.const _ (1 : ℂ)) hU).isLocallyConstant
    let H : (Fin a → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ :=
      fun y => U.indicator (fun _ => (1 : ℂ)) (finPart D e * y i j)
    have hH : IsLocallyConstant H := hI.comp_continuous
      ((continuous_mul_left_fin D _).comp ((continuous_apply j).comp (continuous_apply i)))
    have hval : ∀ {x : Mx D a n}, e • x = x → H (fun i j => finPart D (x i j)) = U.indicator (fun _ => (1 : ℂ)) (finPart D (x i j)) := by
      intro x hx
      show U.indicator (fun _ => (1 : ℂ)) (finPart D e * finPart D (x i j)) = _
      rw [← map_mul, ← hsm, hx]
    refine ⟨_, fin_mul_mem θ hH hB, ?_, hC.mul_left, ?_⟩
    · refine good_factor (M := fun x => H fun i j => finPart D (x i j)) (fun x => ?_) hG
      show U.indicator (fun _ => (1 : ℂ)) (finPart D e * finPart D (e * x i j)) =
        U.indicator (fun _ => (1 : ℂ)) (finPart D e * finPart D (x i j))
      rw [← map_mul, ← map_mul, ← mul_assoc, he]
    · show (H fun i j => finPart D (p i j)) * B p ≠ (H fun i j => finPart D (q i j)) * B q
      rw [hval hp, hval hq, Bp, Bq, Set.indicator_of_mem hxU, Set.indicator_of_notMem hyU]
      simp

theorem bump_of (hBump : BumpEx) {θ : InfFam D} (hθ : IsInfFam θ) (hid : IsIdem S e) {C : Set (Mx D a n)}
    (hC : IsCompact C) (hCi : ∀ x ∈ C, e • x = x) :
    ∃ Φ ∈ schwartzA θ a n, Good S e Φ ∧ HasCompactSupport Φ ∧ (∀ x, 0 ≤ (Φ x).re ∧ (Φ x).im = 0) ∧ ∀ x ∈ C, Φ x = 1 := by
  obtain ⟨η, hη⟩ := hBump D θ hθ a n S e hid C hC (fun x hx => intOff_of_smul hid (hCi x hx))
  obtain ⟨m1, m2, m3⟩ := row_prod (S := S) (e := e) (θ := θ) a η (fun i => ⟨(hη i).1, (hη i).2.1, (hη i).2.2.1⟩)
  refine ⟨_, m1, m2, m3, fun x => ?_, fun x hx => Finset.prod_eq_one fun i _ => (hη i).2.2.2.2 x hx⟩
  have e1 : (∏ i, η i (x.submatrix (fun _ => i) id)) = ((∏ i, (η i (x.submatrix (fun _ => i) id)).re : ℝ) : ℂ) := by
    push_cast
    exact Finset.prod_congr rfl fun i _ => Complex.ext (by simp) (by simpa using (hη i).2.2.2.1 _ |>.2.2)
  show 0 ≤ (∏ i, η i (x.submatrix (fun _ => i) id)).re ∧ (∏ i, η i (x.submatrix (fun _ => i) id)).im = 0
  rw [e1, Complex.ofReal_re, Complex.ofReal_im]
  exact ⟨Finset.prod_nonneg fun i _ => ((hη i).2.2.2.1 _).1, rfl⟩

theorem smul_jn (hn : r + t = n) (x : Mx D a r) (v : Mx D a t) : e • jn hn x v = jn hn (e • x) (e • v) := by
  ext i j
  simp only [jn, Matrix.smul_apply, Matrix.submatrix_apply, id]
  generalize (finSumFinEquiv.trans (finCongr hn)).symm j = k
  cases k <;> simp

theorem isClosedEmbedding_jn (hn : r + t = n) (e : AE D) :
    Topology.IsClosedEmbedding (fun z : XS D a r t e => jn hn z.1.1 z.1.2) := by
  subst hn
  obtain ⟨-, -, h2, -⟩ := GlobalTheory.CompanionTheory.OrbUniq.mx_facts D a (r + t)
  obtain ⟨-, -, h2r, -⟩ := GlobalTheory.CompanionTheory.OrbUniq.mx_facts D a r
  obtain ⟨-, -, h2t, -⟩ := GlobalTheory.CompanionTheory.OrbUniq.mx_facts D a t
  haveI : IsTopologicalRing (AE D) := GlobalTheory.Doubling.isTopologicalRing_tens
  have hcl : IsClosed {z : Mx D a r × Mx D a t | e • z.1 = z.1 ∧ e • z.2 = z.2} :=
    (isClosed_eq ((continuous_const_smul e).comp continuous_fst) continuous_fst).inter
      (isClosed_eq ((continuous_const_smul e).comp continuous_snd) continuous_snd)
  have hs : Topology.IsClosedEmbedding (Subtype.val : XS D a r t e → Mx D a r × Mx D a t) := hcl.isClosedEmbedding_subtypeVal
  have hj : Continuous fun z : Mx D a r × Mx D a t => jn (rfl : r + t = r + t) z.1 z.2 := by
    refine continuous_matrix fun i j => ?_
    simp only [jn, Matrix.submatrix_apply, id]
    generalize (finSumFinEquiv.trans (finCongr (rfl : r + t = r + t))).symm j = k
    cases k with
    | inl k =>
      simp only [Matrix.fromCols_apply_inl]
      exact continuous_fst.matrix_elem i k
    | inr k =>
      simp only [Matrix.fromCols_apply_inr]
      exact continuous_snd.matrix_elem i k
  have hu : Continuous fun x : Mx D a (r + t) =>
      ((x.submatrix id (Fin.castAdd t) : Mx D a r), (x.submatrix id (Fin.natAdd r) : Mx D a t)) :=
    (continuous_id.matrix_submatrix _ _).prodMk (continuous_id.matrix_submatrix _ _)
  have hl : Function.LeftInverse (fun x : Mx D a (r + t) =>
      ((x.submatrix id (Fin.castAdd t) : Mx D a r), (x.submatrix id (Fin.natAdd r) : Mx D a t)))
      (fun z : Mx D a r × Mx D a t => jn (rfl : r + t = r + t) z.1 z.2) := by
    intro z
    refine Prod.ext ?_ ?_
    · ext i j
      simp [jn]
    · ext i j
      simp [jn]
  exact (hl.isClosedEmbedding hu hj).comp hs

theorem exists_of_mem_algA {θ : InfFam D} (hn : r + t = n) {f : XS D a r t e → ℂ}
    (hf : f ∈ algA (a := a) θ hn S e) :
    ∃ Φ ∈ schwartzA θ a n, Good S e Φ ∧ HasCompactSupport Φ ∧ f = fun z => Φ (jn hn z.1.1 z.1.2) := by
  induction hf using Submodule.span_induction with
  | mem f h => exact h
  | zero => exact ⟨fun _ => 0, (schwartzA θ a n).zero_mem, good_zero, HasCompactSupport.zero, rfl⟩
  | add f g _ _ h₁ h₂ =>
    obtain ⟨Φ, m1, g1, c1, rfl⟩ := h₁
    obtain ⟨Ψ, m2, g2, c2, rfl⟩ := h₂
    exact ⟨fun x => Φ x + Ψ x, (schwartzA θ a n).add_mem m1 m2, good_add g1 g2, c1.add c2, rfl⟩
  | smul c f _ h₁ =>
    obtain ⟨Φ, m1, g1, c1, rfl⟩ := h₁
    exact ⟨fun x => c * Φ x, (schwartzA θ a n).smul_mem c m1, good_smul c g1, c1.mul_left, rfl⟩

theorem algRich : IdemEx → BumpEx → TopX → AlgRich := by
  intro hI hBump _ D θ hθ a r t n hn S e hid
  have he : e * e = e := ((hI D S).2 e hid).1
  have hι := isClosedEmbedding_jn (D := D) (a := a) hn e
  have gen : ∀ Φ ∈ schwartzA θ a n, Good S e Φ → HasCompactSupport Φ →
      (fun z : XS D a r t e => Φ (jn hn z.1.1 z.1.2)) ∈ algA (a := a) θ hn S e :=
    fun Φ h1 h2 h3 => Submodule.subset_span ⟨Φ, h1, h2, h3, rfl⟩
  have hfix : ∀ z : XS D a r t e, e • jn hn z.1.1 z.1.2 = jn hn z.1.1 z.1.2 := fun z => by
    rw [smul_jn, z.2.1, z.2.2]
  refine ⟨⟨fun f hf => ?_, fun f hf g hg => ?_, fun f hf => ?_, fun x y hxy => ?_, fun C hC => ?_⟩,
    fun f hf => exists_of_mem_algA hn hf⟩
  · obtain ⟨Φ, h1, -, h3, rfl⟩ := exists_of_mem_algA hn hf
    exact ⟨(GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ a n Φ h1).1.comp hι.continuous,
      h3.comp_isClosedEmbedding hι⟩
  · obtain ⟨Φ, h1, h2, h3, rfl⟩ := exists_of_mem_algA hn hf
    obtain ⟨Ψ, k1, k2, k3, rfl⟩ := exists_of_mem_algA hn hg
    exact gen (fun x => Φ x * Ψ x) (mul_mem θ h1 k1) (good_mul h2 k2) h3.mul_right
  · obtain ⟨Φ, h1, h2, h3, rfl⟩ := exists_of_mem_algA hn hf
    exact gen (fun x => conj (Φ x)) (conj_mem θ h1) (good_conj h2) (h3.comp_left (map_zero _))
  · have hne : jn hn x.1.1 x.1.2 ≠ jn hn y.1.1 y.1.2 := fun h => hxy (hι.injective h)
    have hfin : ({jn hn x.1.1 x.1.2, jn hn y.1.1 y.1.2} : Set (Mx D a n)).Finite := by simp
    obtain ⟨B, b1, b2, b3, -, b5⟩ := bump_of hBump hθ hid hfin.isCompact (by
      rintro w (rfl | rfl)
      · exact hfix x
      · exact hfix y)
    obtain ⟨Φ, h1, h2, h3, h4⟩ := sep_pts hθ hid he (hfix x) (hfix y) hne b1 b2 b3 (b5 _ (by simp)) (b5 _ (by simp))
    exact ⟨_, gen Φ h1 h2 h3, h4⟩
  · obtain ⟨B, b1, b2, b3, b4, b5⟩ := bump_of hBump hθ hid (hC.image hι.continuous) (by
      rintro _ ⟨z, -, rfl⟩
      exact hfix z)
    exact ⟨_, gen B b1 b2 b3, fun z => b4 _, fun z hz => b5 _ ⟨z, hz, rfl⟩⟩

end GlobalTheory.CompanionTheory.AlgRich

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoverIntersectionGradedVanishStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cover_intersection_graded_vanish : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q]
    (U : Cov q) (a n : ℕ) (i : Fin (n + 1) → U.ι) (r : ℕ), r ≠ a → Subsingleton (HU (Fk q U a) (capT (Vk q U a) i) r) := by
  first | exact @GlobalTheory.CompanionTheory.CapVan.van | exact GlobalTheory.CompanionTheory.CapVan.van | (intros; apply GlobalTheory.CompanionTheory.CapVan.van <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalConvolutionCompact
section
open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC

namespace GlobalTheory.CompanionTheory.CuspidalCompact

theorem isCompactOperator_repOp_Rcusp (E : Type) [Field E] [NumberField E] [IsTotallyComplex E]
    (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (f : GA E a → ℂ)
    (hf : Continuous f) (hc : HasCompactSupport f) :
    IsCompactOperator (repOp (Rcusp μ) μ f) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact GlobalTheory.CompanionTheory.CuspRank.isCompactOperator_repOp_Rcusp_zero E μ f
  · let ν : Measure (GroundTheory.Automorphic.Reduction.normOneGL E a) := Measure.haar
    obtain ⟨Φ, c, hc0, hΦ, hint⟩ := GlobalTheory.T.cuspidal_L2_norm_one_isometry E a ha μ ν
    obtain ⟨f₁, hf₁⟩ := hint f hf hc
    exact GlobalTheory.CompanionTheory.CompactOperators.isCompactOperator_of_scaled_isometric_intertwiner (repOp (Rcusp μ) μ f) _ Φ c hc0 hΦ hf₁
      (GroundTheory.Automorphic.CuspidalSpectrum.isCompactOperator_cuspRep ν f₁)

end GlobalTheory.CompanionTheory.CuspidalCompact
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaConjInvariant
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.DeltaMap

theorem bijective_algHom (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) : Function.Bijective σ := by
  have hinj : Function.Injective σ := (σ : E →+* E).injective
  refine ⟨hinj, ?_⟩
  let τ : E →ₐ[ℚ] E := (σ : E →+* E).toRatAlgHom
  have h2 : Function.Injective τ.toLinearMap := hinj
  exact LinearMap.injective_iff_surjective.mp h2

theorem delta_map (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (c : Matrix (Fin n) (Fin n) E) : delta (c.map σ) = delta c := by
  classical
  let e : E ≃+* E := (AlgEquiv.ofBijective σ (bijective_algHom F E σ)).toRingEquiv
  let ψ : 𝓞 E ≃+* 𝓞 E := NumberField.RingOfIntegers.mapRingEquiv e
  have hψ : ∀ o : 𝓞 E, algebraMap (𝓞 E) E (ψ o) = σ (algebraMap (𝓞 E) E o) := fun o => rfl
  let φ : (Fin n → 𝓞 E) →+ (Fin n → 𝓞 E) :=
    { toFun := fun y i => ψ (y i)
      map_zero' := by
        funext i
        simp
      map_add' := by
        intro y z
        funext i
        simp }
  have hφ : ∀ y j, φ y j = ψ (y j) := fun y j => rfl
  have hvec : ∀ y : Fin n → 𝓞 E, (c.map σ) *ᵥ (fun j => algebraMap (𝓞 E) E (φ y j)) =
      fun i => σ ((c *ᵥ fun j => algebraMap (𝓞 E) E (y j)) i) := by
    intro y
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, hφ, hψ]
  have key : Kc c = (Kc (c.map σ)).comap φ := by
    ext y
    rw [AddSubgroup.mem_comap]
    show (∀ i, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = (c *ᵥ fun j => algebraMap (𝓞 E) E (y j)) i) ↔
      (∀ i, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = ((c.map σ) *ᵥ fun j => algebraMap (𝓞 E) E (φ y j)) i)
    rw [hvec]
    refine forall_congr' fun i => ⟨fun h => h.elim fun o ho => ⟨ψ o, by rw [hψ, ho]⟩,
      fun h => h.elim fun o ho => ⟨ψ.symm o, ?_⟩⟩
    apply e.injective
    show σ (algebraMap (𝓞 E) E (ψ.symm o)) = σ _
    rw [← hψ, RingEquiv.apply_symm_apply, ho]
  have hsurj : Function.Surjective φ := fun y =>
    ⟨fun i => ψ.symm (y i), funext fun i => ψ.apply_symm_apply (y i)⟩
  show (Kc (c.map σ)).index = (Kc c).index
  rw [key]
  first
    | exact (AddSubgroup.index_comap_of_surjective hsurj).symm
    | exact (AddSubgroup.index_comap_of_surjective _ hsurj).symm
    | exact (AddSubgroup.index_comap_of_surjective (H := Kc (c.map σ)) hsurj).symm

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.DeltaMap
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaPosIndex
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Fin

theorem delta_pos_index : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (c : Matrix (Fin n) (Fin n) E),
    delta c ≠ 0 :=
  fun _ _ _ _ c => GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DeltaIndex.delta_ne_zero c

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Fin
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedRestrictPullBijectiveStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_restrict_pull_bijective : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (𝒱 : Set X.Opens), sSup 𝒱 = ⊤ →
    ∀ (a s : ℕ), a < s → ∀ n : ℕ, Function.Bijective ((CH.Mor.restrict (HT.grT (smFun X q) a) (Pb.KS q s 𝒱).ι).pull n) := by
  first | exact @GlobalTheory.CompanionTheory.OmLoc.grT_restrict_bijective | exact GlobalTheory.CompanionTheory.OmLoc.grT_restrict_bijective | (intros; apply GlobalTheory.CompanionTheory.OmLoc.grT_restrict_bijective <;> assumption)
end

