import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1977
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterConductorCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1777
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLocalFieldDataExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0025
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0026
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0792
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0636
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0640
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0597

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixThA
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LFixTh

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

open PositivityTheory.Rg.Rsw.L

variable {D : D7} {n : ℕ}

theorem mat_mul (g h : G D n) : mat (g * h) = mat g * mat h := by simp [mat]

theorem mat_mul_inv (g : G D n) : mat g * mat g⁻¹ = 1 := by simp [mat]

theorem mat_proj (g : G D n) (v : Pl D) :
    ((matHom (Fv D.host.F v) D.sp.cm.sig (Jst D n) (proj D.sp.cm.sig (Jst D n) v g)).1 : Matrix _ _ _) =
      (mat g).map (cv D v) := rfl

theorem compInf_eq (w : InfinitePlace D.host.F) (x : AE D) :
    compInf D.host.F D.host.E w x = Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id D.host.F D.host.E)
      (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => rw [map_add, hx, hy, map_add, map_add]

theorem kOff_inf {S : Finset (Pl D)} {g : G D n} (hg : g ∈ KOff D n S) (w : InfinitePlace D.host.F) (i j : Fin (n + n)) :
    compInf D.host.F D.host.E w (mat g i j) = (1 : Matrix (Fin (n + n)) (Fin (n + n)) _) i j := by
  have h1 := (mem_levelOff.1 hg).1
  have h2 : (mat g).map (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom = 1 := by
    exact congrArg Units.val (MonoidHom.mem_ker.1 h1)
  have h3 := congrFun (congrFun h2 i) j
  simp only [Matrix.map_apply] at h3
  rw [compInf_eq]
  change _ = (1 : Matrix (Fin (n + n)) (Fin (n + n)) _) i j
  rw [show Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (mat g i j) = _ from h3]
  by_cases e : i = j
  · subst e; simp
  · simp [Matrix.one_apply_ne e]

theorem kOff_at {S : Finset (Pl D)} {g : G D n} (hg : g ∈ KOff D n S) {v : Pl D} (hv : v ∈ S) (i j : Fin (n + n)) :
    cv D v (mat g i j) = (1 : Matrix (Fin (n + n)) (Fin (n + n)) _) i j := by
  have h := (mem_levelOff.1 hg).2.1 v hv
  have := congrArg (fun x => ((matHom (Fv D.host.F v) D.sp.cm.sig (Jst D n) x).1 : Matrix _ _ _)) h
  simp only [mat_proj, map_one, Units.val_one] at this
  have := congrFun (congrFun this i) j
  simpa using this

theorem kOff_int {S : Finset (Pl D)} {g : G D n} (hg : g ∈ KOff D n S) {v : Pl D} (hv : v ∉ S) (i j : Fin (n + n)) :
    cv D v (mat g i j) ∈ intLoc D.host.F D.host.E v ∧ cv D v (mat g⁻¹ i j) ∈ intLoc D.host.F D.host.E v := by
  have h := (mem_levelOff.1 hg).2.2 v hv
  have hs : ∀ y, y ∈ latLoc D.host.F (stdLattice D.host.E (n + n)) v ↔
      (mat g).map (cv D v) *ᵥ y ∈ latLoc D.host.F (stdLattice D.host.E (n + n)) v := h
  have he : ∀ k : Fin (n + n), (Pi.single k 1 : Fin (n + n) → Fv D.host.F v ⊗[D.host.F] D.host.E) ∈
      latLoc D.host.F (stdLattice D.host.E (n + n)) v := fun k => by
    rw [mem_latLoc_stdLattice]
    intro l
    by_cases e : l = k
    · subst e; simp
    · simp [Pi.single_eq_of_ne e]
  have hM : (mat g).map (cv D v) * (mat g⁻¹).map (cv D v) = 1 := by
    have := (RingHom.mapMatrix (cv D v)).map_mul (mat g) (mat g⁻¹)
    rw [mat_mul_inv, map_one] at this
    exact this.symm
  constructor
  · have := mem_latLoc_stdLattice.1 ((hs _).1 (he j)) i
    simpa [Matrix.mulVec_single_one] using this
  · have h2 : (mat g⁻¹).map (cv D v) *ᵥ Pi.single j 1 ∈ latLoc D.host.F (stdLattice D.host.E (n + n)) v := by
      refine (hs _).2 ?_
      rw [Matrix.mulVec_mulVec, hM, Matrix.one_mulVec]
      exact he j
    have := mem_latLoc_stdLattice.1 h2 i
    simpa [Matrix.mulVec_single_one] using this

end PositivityTheory.Rg.Rsw.L.LFixTh

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LLatBound
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LLatBound

variable {D : D7}

theorem gen_all {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (n : ℕ)
    (f : SchwartzMap (D.what₂.Tau → Fin V.rank → Fin n → ℂ) ℂ)
    (g : (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ)
    (hg : g ∈ GlobalTheory.WeilM.SB (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E)) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ h : GA D V,
      ∑' x : {x : Matrix (Fin V.rank) (Fin n) D.host.E // x.rank = V.rank},
        ‖(fun X : Mx D V.rank n => f (fun τ i j => compAt θ τ X i j) * g (fun i j => finPart D (X i j)))
          (mm (mt V h⁻¹) (rat x.1))‖ₑ ≤ C := by
  obtain ⟨U, hUo, hU⟩ := exists_intOpen V
  obtain ⟨S, -, hS⟩ := GlobalTheory.Size.exists_finset_doubleCosets V U hUo
  choose C hC hb using fun x₀ : GA D V => gen_bound_col hθ V n x₀⁻¹ f g hg
  refine ⟨∑ x₀ ∈ S, C x₀, ENNReal.sum_lt_top.2 fun x _ => hC x, fun h => ?_⟩
  obtain ⟨γ, hγ, x₀, hx₀, a, ha, k, hk, hkf, rfl⟩ := hS h
  have e : (γ * x₀ * a * k)⁻¹ = (k⁻¹ * a⁻¹ * x₀⁻¹) * γ⁻¹ := by group
  have e2 : ∀ X : Mx D V.rank n, mm (mt V (γ * x₀ * a * k)⁻¹) X = mm (mt V (k⁻¹ * a⁻¹ * x₀⁻¹)) (mm (mt V γ⁻¹) X) := by
    intro X
    rw [e, mtL_mul]
    exact Matrix.mul_assoc _ _ _
  simp_rw [e2]
  rw [tsum_GQ V n γ⁻¹ (inv_mem hγ) (fun X => ‖f (fun τ i j => compAt θ τ (mm (mt V (k⁻¹ * a⁻¹ * x₀⁻¹)) X) i j) *
    g (fun i j => finPart D ((mm (mt V (k⁻¹ * a⁻¹ * x₀⁻¹)) X) i j))‖ₑ)]
  refine (hb x₀ a⁻¹ (inv_mem ha) k⁻¹ (inv_mem hkf) ?_).trans
    (Finset.single_le_sum (f := C) (fun _ _ => zero_le) hx₀)
  simpa using hU k hk

end PositivityTheory.Rg.Rsw.L.LLatBound

namespace PositivityTheory.Rg.Rsw.L

theorem latBound : LatBound := by
  intro D θ hθ V n M hM
  suffices h : ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ h : GA D V,
      ∑' x : {x : Matrix (Fin V.rank) (Fin n) D.host.E // x.rank = V.rank}, ‖M (mm (mt V h⁻¹) (rat x.1))‖ₑ ≤ C by
    obtain ⟨C, hC, h⟩ := h
    exact ⟨C.toNNReal, fun g => (h g).trans (by rw [ENNReal.coe_toNNReal hC.ne])⟩
  induction hM using Submodule.span_induction with
  | mem Φ hΦ =>
    obtain ⟨f, g, hg, rfl⟩ := hΦ
    exact LLatBound.gen_all hθ V n f g hg
  | zero => exact ⟨0, by simp, fun _ => by simp⟩
  | add f g _ _ hf hg =>
    obtain ⟨C₁, h₁, hf⟩ := hf
    obtain ⟨C₂, h₂, hg⟩ := hg
    refine ⟨C₁ + C₂, ENNReal.add_lt_top.2 ⟨h₁, h₂⟩, fun h => ?_⟩
    calc _ ≤ ∑' x : {x : Matrix (Fin V.rank) (Fin n) D.host.E // x.rank = V.rank},
          (‖f (mm (mt V h⁻¹) (rat x.1))‖ₑ + ‖g (mm (mt V h⁻¹) (rat x.1))‖ₑ) :=
          ENNReal.tsum_le_tsum fun x => enorm_add_le _ _
      _ = _ := ENNReal.tsum_add
      _ ≤ _ := add_le_add (hf h) (hg h)
  | smul c f _ hf =>
    obtain ⟨C₁, h₁, hf⟩ := hf
    refine ⟨‖c‖ₑ * C₁, ENNReal.mul_lt_top enorm_lt_top h₁, fun h => ?_⟩
    calc _ = ∑' x : {x : Matrix (Fin V.rank) (Fin n) D.host.E // x.rank = V.rank}, ‖c‖ₑ * ‖f (mm (mt V h⁻¹) (rat x.1))‖ₑ :=
          tsum_congr fun x => by simp [enorm_mul]
      _ = _ := ENNReal.tsum_mul_left
      _ ≤ _ := by gcongr; exact hf h

end PositivityTheory.Rg.Rsw.L

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LThProdA
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

open PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.ThTot GlobalTheory.CompanionTheory.ThTot.OneRow

namespace PositivityTheory.Rg.Rsw.L.LThProd

variable {D : D7}

theorem oneTh (hW : L.WMaj) {p : ℕ} (μ : Measure (Mx D 1 p)) (𝓕 : Set (Mx D 1 p)) (hμ : IsCovolOne (ratMx D 1 p) μ 𝓕)
    {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D 1) (hdet : b₀.1.det ≠ 0)
    {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (hr : ResEta D χ 1) {θ : InfFam D} (hθ : IsInfFam θ)
    (η : Mx D 1 p → ℂ) (hη : η ∈ schwartzA θ 1 p) :
    ∃ Ω, IsTh ψ χ θ b₀ μ Ω ∧ Ω 1 = η := by
  obtain ⟨c, hc0, hc⟩ := exists_base b₀ hdet
  obtain ⟨ψ₀, h₀, lam, hlam0, hlam⟩ := GlobalTheory.ThetaAllChar.exists_std hψ
  have hne : lam * c ≠ 0 := mul_ne_zero hlam0 hc0
  obtain ⟨hψ₁, -⟩ := exists_par ψ₀ h₀ θ hθ (lam * c) hne
  have hs : ∀ t, shift ψ₀ (lam * c) t = ψ (algebraMap D.host.F (AF D.host.F) c * t) := by
    intro t
    rw [hlam]
    simp [shift, AddChar.mulShift_apply, map_mul, mul_assoc]
  obtain ⟨ω, hω⟩ := GlobalTheory.StdUnn.Inhab.weil_exists D p (V1 D) ψ₀ h₀ (lam * c) hne χ hχ hr θ hθ μ 𝓕 hμ
  let Φ : schwartzA θ (V1 D).rank p := ⟨η, hη⟩
  have hM := hW D p (V1 D) _ hψ₁ χ hχ hr θ hθ μ ⟨𝓕, hμ⟩ ω hω Φ
  have e : ∀ g h : G D p, ω (g * h) Φ = ω g (ω h Φ) := fun g h => by rw [map_mul]; rfl
  refine ⟨fun h => (ω h Φ).1,
    { mem := fun h => (ω h Φ).2
      cont := hM.1
      maj := hM.2
      levi := by
        intro g a hg h y
        show (ω (g * h) Φ).1 y = _
        rw [e]
        exact hω.levi g a hg _ y
      unip := by
        intro g b hg h y
        show (ω (g * h) Φ).1 y = _
        rw [e, hω.unip g b hg _ y, hs, pr_eq b₀ c hc, Matrix.mul_smul, Matrix.trace_smul, halfTr_smul]
      weyl := by
        intro g hg h x
        show (ω (g * h) Φ).1 x = _
        rw [e, hω.weyl g hg _ x]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        show _ * shift ψ₀ (lam * c) _ = _ * ψ _
        rw [hs, pr_eq b₀ c hc x y, Matrix.trace_smul, trA_smul] }, ?_⟩
  show (ω 1 Φ).1 = η
  rw [map_one]
  rfl

theorem hecke_mul_inv {χ ε : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (hε : IsHeckeChar D ε) :
    IsHeckeChar D (χ * ε⁻¹) := by
  have e : ⇑(χ * ε⁻¹) = fun x => χ x * (ε x)⁻¹ := by
    funext x
    simp
  refine ⟨?_, fun x => ?_⟩
  · rw [e]
    exact hχ.1.mul hε.1.inv
  · rw [e]
    simp only [hχ.2 x, hε.2 x, inv_one, mul_one]

theorem resEta_mul_inv {χ ε : (AE D)ˣ →* Circle} {k : ℕ} (hχ : ResEta D χ (k + 1)) (hε : ResEta D ε 1) :
    ResEta D (χ * ε⁻¹) k := by
  refine ⟨hχ.1, fun η hη a => ?_⟩
  have h1 := hχ.2 η hη a
  have h2 := hε.2 η hη a
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, h1, h2, pow_succ, pow_one, mul_inv_cancel_right]

def topH {m : ℕ} (b : HermE D (m + 1)) : HermE D m :=
  ⟨b.1.submatrix Fin.castSucc Fin.castSucc, by
    funext i j
    exact congrFun (congrFun b.2 (Fin.castSucc i)) (Fin.castSucc j)⟩

def botH {m : ℕ} (b : HermE D (m + 1)) : HermE D 1 :=
  ⟨b.1.submatrix (fun _ => Fin.last m) (fun _ => Fin.last m), by
    funext i j
    exact congrFun (congrFun b.2 (Fin.last m)) (Fin.last m)⟩

theorem diag_ne {m : ℕ} {b : HermE D m} (h : IsDiagInv b) (i : Fin m) : b.1 i i ≠ 0 := by
  have e : Matrix.diagonal (Matrix.diag b.1) = b.1 := h.1.diagonal_diag
  have hd := h.2
  rw [← e, Matrix.det_diagonal] at hd
  exact (Finset.prod_ne_zero_iff.1 hd) i (Finset.mem_univ _)

theorem topH_diag {m : ℕ} {b : HermE D (m + 1)} (h : IsDiagInv b) : IsDiagInv (topH b) := by
  refine ⟨h.1.submatrix (Fin.castSucc_injective m), ?_⟩
  have e : Matrix.diagonal (Matrix.diag (topH b).1) = (topH b).1 := (h.1.submatrix (Fin.castSucc_injective m)).diagonal_diag
  rw [← e, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.2 fun i _ => diag_ne h _

theorem botH_det {m : ℕ} {b : HermE D (m + 1)} (h : IsDiagInv b) : (botH b).1.det ≠ 0 := by
  rw [Matrix.det_fin_one]
  exact diag_ne h (Fin.last m)

theorem natAdd_one {m : ℕ} (a : Fin 1) : Fin.natAdd m a = Fin.last m := by
  ext
  simp [Fin.fin_one_eq_zero a]

theorem diagonal_hermitian_is_block {m : ℕ} {b : HermE D (m + 1)} (h : IsDiagInv b) : IsBlockSL2Embedding (r := m) (s := 1) b (topH b) (botH b) := by
  refine ⟨fun i j => rfl, fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
  · show b.1 _ _ = b.1 _ _
    rw [natAdd_one, natAdd_one]
  · refine h.1 ?_
    intro e
    have := congrArg Fin.val e
    simp at this
    omega
  · refine h.1 ?_
    intro e
    have := congrArg Fin.val e
    simp at this
    omega

end PositivityTheory.Rg.Rsw.L.LThProd

end
end

