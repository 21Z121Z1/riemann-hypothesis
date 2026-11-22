import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0075
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0181
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0187
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0182
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0173
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0183
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0177
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0155
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0046
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwasawaBlockTriangular
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0185
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.Bundle0004
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0001
import Formalism.SatakeDualWeyl.KpqSubgroupCompact

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledThetaSeriesLawAndLevel
section
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW
open scoped ContDiff

noncomputable section

namespace GlobalTheory.ThetaSeriesLaw

open Filter Topology
open scoped TensorProduct

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)

def bt (x y : Mx D T.rank ρ) : AF D.host.F := symplOH S T (d.extX T x) (d.extY T y)

theorem bt_add_left (x x' y : Mx D T.rank ρ) : bt d T (x + x') y = bt d T x y + bt d T x' y := by
  rw [bt, map_add, GlobalTheory.OrientedHeis.symplOH_add_left]; rfl

theorem bt_add_right (x y y' : Mx D T.rank ρ) : bt d T x (y + y') = bt d T x y + bt d T x y' := by
  rw [bt, map_add, GlobalTheory.OrientedHeis.symplOH_add_right]; rfl

theorem bt_zero_right (x : Mx D T.rank ρ) : bt d T x 0 = 0 := by
  rw [bt, map_zero, GlobalTheory.FinTranslate.symplOH_zero_right]

theorem symplO_bt (x y : Mx D T.rank ρ) : symplO S T (d.extX T x) (d.extY T y) = bt d T x y + bt d T x y := by
  have h2 : algebraMap D.host.F (AF D.host.F) (1 / 2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]
    norm_num
  unfold bt symplOH
  linear_combination (-symplO S T (d.extX T x) (d.extY T y)) * h2

theorem psi_bt_rat {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ)
    (ξ η : Matrix (Fin T.rank) (Fin ρ) D.host.E) : ψ (bt d T (rat ξ) (rat η)) = 1 := by
  obtain ⟨a, ha⟩ := GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_rat D S T (ξ * d.qX) (η * d.qY)
  rw [ratW_eq, ratW_eq, rat_mul, rat_mul] at ha
  have : bt d T (rat ξ) (rat η) = algebraMap D.host.F (AF D.host.F) (1 / 2 * a) := by
    rw [map_mul, ← ha]; rfl
  rw [this]; exact hψ.2.2.1 _

theorem symplOH_coord (h0 : d.j0 = 0) (w w' : WO S T) :
    symplOH S T w w' = bt d T (w ⬝ d.jX) (w' ⬝ d.jY) - bt d T (w' ⬝ d.jX) (w ⬝ d.jY) := by
  have h : ∀ w : WO S T, w = d.extX T (w ⬝ d.jX) + d.extY T (w ⬝ d.jY) := fun w => by
    have := (d.coordS T).left_inv w
    change d.extX T (w ⬝ d.jX) + d.ext0 T (w ⬝ d.j0) + d.extY T (w ⬝ d.jY) = w at this
    rw [h0, Matrix.mul_zero, map_zero, add_zero] at this
    exact this.symm
  conv_lhs => rw [h w, h w']
  rw [GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_right, GlobalTheory.OrientedHeis.symplOH_add_right,
    d.symplOH_extX_extX, d.symplOH_extY_extY, symplOH_skew S T (d.extX T (w' ⬝ d.jX)), zero_add, add_zero,
    sub_eq_add_neg]
  rfl

theorem map_mul_zero {R : Type} [CommRing R] (q : AE D →+* R) {l m n : ℕ} {x : Mx D l m} (hx : x.map q = 0)
    (y : Mx D m n) : (x ⬝ y : Mx D l n).map q = 0 := by
  rw [Matrix.map_mul, hx, Matrix.zero_mul]

theorem snd_bt {x : Mx D T.rank ρ} (hx : x.map (finPart D) = 0) (y : Mx D T.rank ρ) : (bt d T x y).2 = 0 := by
  have h := GlobalTheory.OrientedHeis.snd_symplO (S := S) (T := T) (x := d.extX T x) (y := d.extY T y)
    (Or.inl (map_mul_zero _ hx _))
  change _ * sndA D.host.F (symplO S T (d.extX T x) (d.extY T y)) = 0
  rw [h, mul_zero]

theorem bt_eq_pair (x : Mx D T.rank ρ) {y : Mx D T.rank ρ} (hy : y.map (infPart D) = 0) :
    bt d T x y = pairA D.host.F 0 (bt d T x y).2 := by
  have h := GlobalTheory.OrientedHeis.fst_symplO (S := S) (T := T) (x := d.extX T x) (y := d.extY T y)
    (Or.inr (map_mul_zero _ hy _))
  refine Prod.ext ?_ rfl
  change _ * fstA D.host.F (symplO S T (d.extX T x) (d.extY T y)) = 0
  rw [h, mul_zero]

theorem exists_section (D : D7) : ∃ s : Af D.host.F ⊗[D.host.F] D.host.E → AE D, Continuous s ∧
    ∀ z, finPart D (s z) = z := by
  obtain ⟨e, he, -, hc⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  refine ⟨fun z => e.symm (0, z), hc.comp (continuous_const.prodMk continuous_id), fun z => ?_⟩
  have := (he (e.symm (0, z))).2
  rw [e.apply_symm_apply] at this
  exact this.symm

theorem exists_open_ann {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (Z : Set (Mx D T.rank ρ))
    {K : Set (Matrix (Fin T.rank) (Fin ρ) (Af D.host.F ⊗[D.host.F] D.host.E))} (hK : IsCompact K)
    (hZ : ∀ z ∈ Z, z.map (finPart D) ∈ K) :
    ∃ V : AddSubgroup (Mx D T.rank ρ), IsOpen (V : Set (Mx D T.rank ρ)) ∧
      ∀ b ∈ V, b.map (infPart D) = 0 → ∀ z ∈ Z, ψ (bt d T z b) = 1 := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  obtain ⟨s, hs, hsf⟩ := exists_section D
  have hadd : ∀ z a b, ψ (pairA D.host.F 0 (bt d T z (a + b)).2) =
      ψ (pairA D.host.F 0 (bt d T z a).2) * ψ (pairA D.host.F 0 (bt d T z b).2) := fun z a b => by
    rw [← AddChar.map_add_eq_mul, bt_add_right]
    congr 1
    exact Prod.ext (add_zero _).symm rfl
  have hzero : ∀ z, ψ (pairA D.host.F 0 (bt d T z 0).2) = 1 := fun z => by
    rw [bt_zero_right]; exact ψ.map_zero_eq_one
  let V : AddSubgroup (Mx D T.rank ρ) :=
    { carrier := {b | ∀ z ∈ Z, ψ (pairA D.host.F 0 (bt d T z b).2) = 1}
      zero_mem' := fun z _ => hzero z
      add_mem' := fun {a b} ha hb z hz => by rw [hadd, ha z hz, hb z hz, one_mul]
      neg_mem' := fun {a} ha z hz => by
        have := hadd z a (-a)
        rw [add_neg_cancel, hzero, ha z hz, one_mul] at this
        exact this.symm }
  refine ⟨V, V.isOpen_of_mem_nhds (g := 0) ?_, fun b hb h0 z hz => ?_⟩
  · have hK' : IsCompact ((fun k => k.map s) '' K) := hK.image (continuous_id.matrix_map hs)
    have hc : Continuous fun p : Mx D T.rank ρ × Mx D T.rank ρ => (bt d T p.2 p.1).2 :=
      continuous_snd.comp (GlobalTheory.OrientedHeis.continuous_symplOH (continuous_snd.matrix_mul continuous_const)
        (continuous_fst.matrix_mul continuous_const))
    have hev : ∀ᶠ b in 𝓝 (0 : Mx D T.rank ρ), ∀ z ∈ (fun k => k.map s) '' K,
        ψ (pairA D.host.F 0 (bt d T z b).2) = 1 := by
      refine hK'.eventually_forall_of_forall_eventually fun z _ => ?_
      exact hc.continuousAt.preimage_mem_nhds (x := (0, z)) (t := {a | ψ (pairA D.host.F 0 a) = 1})
        (by rw [bt_zero_right]; exact GlobalTheory.FinTranslate.ker_mem_nhds hψ.1 hψ.2.1)
    refine Filter.mem_of_superset hev fun b hb z hz => ?_
    have h1 := hb _ ⟨_, hZ z hz, rfl⟩
    have h2 : (z - (z.map (finPart D)).map s).map (finPart D) = 0 := by
      ext i j
      exact (RingHom.map_sub _ _ _).trans (sub_eq_zero.2 (hsf _).symm)
    have h3 : (bt d T z b).2 = (bt d T ((z.map (finPart D)).map s) b).2 := by
      have h4 := bt_add_left d T (z - (z.map (finPart D)).map s) ((z.map (finPart D)).map s) b
      rw [sub_add_cancel] at h4
      rw [h4]
      exact (congrArg (· + _) (snd_bt d T h2 b)).trans (zero_add _)
    rw [h3]; exact h1
  · rw [bt_eq_pair d T z h0]; exact hb z hz

variable {d T} {ψ : AddChar (AF D.host.F) ℂ} {φ : Mx D T.rank ρ → ℂ} {f : WO S T → ℂ}

theorem addChar_theta_law_rearrangement_identity {R : Type} [AddCommGroup R] (χ : AddChar R ℂ) (a b c e g h : R) (t : ℂ) (ha : χ a = 1) (hg : χ g = 1) :
    χ (-(a + b + (c + e))) * (χ (c + e + (g + h) + (c + e + (g + h))) * t) =
      χ (-(b - c)) * χ (-e) * (χ (e + h + (e + h)) * t) := by
  rw [← mul_assoc, ← mul_assoc]
  congr 1
  rw [← one_mul (χ _ * χ _ * χ _), ← hg, ← one_mul (χ _ * (χ _ * χ _ * χ _)), ← hg, ← one_mul (χ (-_) * χ _), ← ha]
  simp only [← AddChar.map_add_eq_mul]
  congr 1
  abel

theorem law (hψ : IsCharAF D.host.F ψ) (h0 : d.j0 = 0)
    (hf : ∀ w : WO S T, f w = ψ (-(bt d T (w ⬝ d.jX) (w ⬝ d.jY))) * ∑' ξ : Matrix (Fin T.rank) (Fin ρ) D.host.E,
      ψ (symplO S T (d.extX T (w ⬝ d.jX + rat ξ)) (d.extY T (w ⬝ d.jY))) * φ (w ⬝ d.jX + rat ξ))
    (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (w : WO S T) :
    f (rat γ + w) = ψ (-(symplOH S T (rat γ) w)) * f w := by
  have hX : (rat γ ⬝ d.jX : Mx D T.rank ρ) = rat (γ * d.e) := (rat_mul _ _).symm
  have hY : (rat γ ⬝ d.jY : Mx D T.rank ρ) = rat (γ * d.e') := (rat_mul _ _).symm
  rw [hf, hf, symplOH_coord d T h0, Matrix.add_mul, Matrix.add_mul, hX, hY]
  generalize γ * d.e = ξ₀
  generalize γ * d.e' = η₀
  generalize (w ⬝ d.jX : Mx D T.rank ρ) = x
  generalize (w ⬝ d.jY : Mx D T.rank ρ) = y
  rw [← mul_assoc, ← tsum_mul_left, ← tsum_mul_left]
  refine Eq.trans (tsum_congr fun ξ => ?_) ((Equiv.addLeft ξ₀).tsum_eq _)
  have e : rat ξ₀ + x + rat ξ = x + rat (Equiv.addLeft ξ₀ ξ) := by
    rw [Equiv.coe_addLeft, rat_add]; abel
  rw [e]
  generalize Equiv.addLeft ξ₀ ξ = ζ
  have h1 := psi_bt_rat d T hψ ξ₀ η₀
  have h2 := psi_bt_rat d T hψ ζ η₀
  simp only [symplO_bt, bt_add_left]
  simp only [bt_add_right]
  exact addChar_theta_law_rearrangement_identity ψ _ _ _ _ _ _ _ h1 h2

theorem level (hψ : IsCharAF D.host.F ψ) (h0 : d.j0 = 0) (hφ : GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ)
    (hf : ∀ w : WO S T, f w = ψ (-(bt d T (w ⬝ d.jX) (w ⬝ d.jY))) * ∑' ξ : Matrix (Fin T.rank) (Fin ρ) D.host.E,
      ψ (symplO S T (d.extX T (w ⬝ d.jX + rat ξ)) (d.extY T (w ⬝ d.jY))) * φ (w ⬝ d.jX + rat ξ)) :
    ∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧
      ∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ S T u f = f := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  obtain ⟨U, hU, hUφ⟩ := hφ.level
  obtain ⟨K, hK, hKφ⟩ := hφ.supp
  obtain ⟨V, hV, hVψ⟩ := exists_open_ann d T hψ {z | φ z ≠ 0} hK hKφ
  let rX : WO S T →+ Mx D T.rank ρ := AddMonoidHom.mk' (fun w => w ⬝ d.jX) fun _ _ => Matrix.add_mul _ _ _
  let rY : WO S T →+ Mx D T.rank ρ := AddMonoidHom.mk' (fun w => w ⬝ d.jY) fun _ _ => Matrix.add_mul _ _ _
  have cX : Continuous rX := continuous_id.matrix_mul continuous_const
  have cY : Continuous rY := continuous_id.matrix_mul continuous_const
  refine ⟨U.comap rX ⊓ V.comap rY, (hU.preimage cX).inter (hV.preimage cY), fun u hu hi => ?_⟩
  have ha := hUφ (u ⬝ d.jX) hu.1 (map_mul_zero _ hi _)
  have hb := hVψ (u ⬝ d.jY) hu.2 (map_mul_zero _ hi _)
  funext w
  rw [heisO, hf, hf, symplOH_coord d T h0, Matrix.add_mul, Matrix.add_mul]
  generalize (u ⬝ d.jX : Mx D T.rank ρ) = a at ha ⊢
  generalize (u ⬝ d.jY : Mx D T.rank ρ) = b at hb ⊢
  generalize (w ⬝ d.jX : Mx D T.rank ρ) = x
  generalize (w ⬝ d.jY : Mx D T.rank ρ) = y
  rw [← mul_assoc, ← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun ξ => ?_
  rw [add_right_comm x a, ha]
  generalize x + rat ξ = z
  by_cases hz : φ z = 0
  · simp only [hz, mul_zero]
  have h1 := hb z hz
  have h2 := hb (z + a) (by rwa [Set.mem_setOf_eq, ha])
  rw [← mul_assoc, ← mul_assoc]
  congr 1
  rw [← one_mul (ψ (-bt d T x y) * ψ _), ← h1, ← one_mul (ψ (bt d T z b) * _), ← h2]
  simp only [← AddChar.map_add_eq_mul, symplO_bt, bt_add_left, bt_add_right]
  congr 1
  abel

theorem law_and_level : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A B : HSp D) (φ : Mx D B.rank A.rank → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ → ∀ f : WO (dblSp A) B → ℂ, (∀ w : WO (dblSp A) B, f w = ψ (-(symplOH (dblSp A) B ((dblDec A).extX B (HMul.hMul w (dblDec A).jX)) ((dblDec A).extY B (HMul.hMul w (dblDec A).jY)))) * ∑' ξ : Matrix (Fin B.rank) (Fin A.rank) D.host.E, ψ (symplO (dblSp A) B ((dblDec A).extX B (HMul.hMul w (dblDec A).jX + rat ξ)) ((dblDec A).extY B (HMul.hMul w (dblDec A).jY))) * φ (HMul.hMul w (dblDec A).jX + rat ξ)) → (∀ γ w, f (ratW B (dblSp A) γ + w) = ψ (-(symplOH (dblSp A) B (ratW B (dblSp A) γ) w)) * f w) ∧ ∃ U : AddSubgroup (WO (dblSp A) B), IsOpen (U : Set (WO (dblSp A) B)) ∧ ∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ (dblSp A) B u f = f := by
  intro D ψ hψ A B φ hφ f hf
  have h0 : (dblDec A).j0 = 0 := rat_zero
  exact ⟨law hψ.1 h0 hf, level hψ.1 h0 hφ hf⟩

end GlobalTheory.ThetaSeriesLaw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingHeightAtRealPlaceContinuousPosLeOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Corev.RealHeight

theorem continuous_hgtW (D : D7) (V : HSp D) (a : GL (Fin V.rank) (AE D)) (w : InfinitePlace D.host.F)
    (hI : GlobalTheory.Doubling.HasIwasawa D.sp.cm.sig (GlobalTheory.Doubling.dblSp V).gram
      (GlobalTheory.Doubling.KArch D.sp.cm.sig (GlobalTheory.Doubling.dblSp V).gram w (Formalism.UG.bc (GlobalTheory.AdelicU.compInf D.host.F D.host.E w) a))) :
    Continuous (GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW V a w) := by
  have hc := GlobalTheory.AdelicU.isCMExt_host D
  have hK := GlobalTheory.Doubling.isCompact_KArch (Q := (GlobalTheory.Doubling.dblSp V).gram) hc w
    (Formalism.UG.bc (GlobalTheory.AdelicU.compInf D.host.F D.host.E w) a)
  have h1 := hI.continuous_hgtH (GlobalTheory.Doubling.continuous_absEw w) hK
  have h2 := GlobalTheory.Doubling.continuous_ioH (R := w.Completion) (σ := D.sp.cm.sig) (GlobalTheory.Doubling.gram_hdbl V)
  have h3 : Continuous fun g : GlobalTheory.Doubling.Gw V w => ((GlobalTheory.Doubling.hgtArch D.sp.cm.sig (GlobalTheory.Doubling.dblSp V).gram w
      (Formalism.UG.bc (GlobalTheory.AdelicU.compInf _ _ w) a) (GlobalTheory.Doubling.ioH _ D.sp.cm.sig (GlobalTheory.Doubling.gram_hdbl V) (g, 1)) : ℝ)) :=
    NNReal.continuous_coe.comp (h1.comp (h2.comp (continuous_id.prodMk continuous_const)))
  exact h3

theorem hgtW_pos (D : D7) (V : HSp D) (a : GL (Fin V.rank) (AE D)) (w : InfinitePlace D.host.F) (g : GlobalTheory.Doubling.Gw V w) :
    0 < GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW V a w g := by
  have h : 0 < ((GlobalTheory.Doubling.hgtArch D.sp.cm.sig (GlobalTheory.Doubling.dblSp V).gram w
      (Formalism.UG.bc (GlobalTheory.AdelicU.compInf _ _ w) a) (GlobalTheory.Doubling.ioH _ D.sp.cm.sig (GlobalTheory.Doubling.gram_hdbl V) (g, 1)) : ℝ)) :=
    NNReal.coe_pos.2 (GlobalTheory.Doubling.hgtH_pos _)
  exact h

theorem hgtW_cont_pos_le_one : ∀ (D : D7) (V : HSp D) (a : GL (Fin V.rank) (AE D)), GlobalTheory.Doubling.IsMaj V a → ∀ w, Continuous (GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW V a w) ∧ ∀ g, 0 < GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW V a w g ∧ GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW V a w g ≤ 1 := fun D V a ha w =>
  ⟨continuous_hgtW D V a w (GlobalTheory.T.iwasawa_doubled_hermitian_space_real_place D V a ha w), fun g => ⟨hgtW_pos D V a w g, GlobalTheory.T.doublingHeightAtRealPlace_le_one D V a ha w g⟩⟩

end GlobalTheory.Corev.RealHeight
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSiegelEqLeviMulUnipotentStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
open GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doublingSiegel_eq_levi_mul_unipotent : ∀ (D : D7) (A : HSp D) (p : siegel A), ∃ (a : GL (Fin A.rank) (AE D)) (c : skewA D A.rank), (p : GA D (dblSp A)) = (dblDec A).levi a * (dblDec A).nC c := by
  first | exact @GlobalTheory.Core.Rk.SWLaw.siegel_eq_levi_nC | exact GlobalTheory.Core.Rk.SWLaw.siegel_eq_levi_nC | (intros; apply GlobalTheory.Core.Rk.SWLaw.siegel_eq_levi_nC <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSiegelLeviDetHomLeviMulUnipotentStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
open GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doublingSiegelLeviDetHom_levi_mul_unipotent : ∀ (D : D7) (A : HSp D) (p : siegel A) (a : GL (Fin A.rank) (AE D)) (c : skewA D A.rank), (p : GA D (dblSp A)) = (dblDec A).levi a * (dblDec A).nC c → aP A p = Matrix.GeneralLinearGroup.det a := by
  first | exact @GlobalTheory.Core.Rk.SWLaw.aP_levi_mul_nC | exact GlobalTheory.Core.Rk.SWLaw.aP_levi_mul_nC | (intros; apply GlobalTheory.Core.Rk.SWLaw.aP_levi_mul_nC <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EulerProductConjugationStableParametersPos
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerConjPos

open GlobalTheory.LFun GlobalTheory.LPositivity Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitarySphericalReps (IsPosReal)

theorem lsd_pos : ∀ (D : D7) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (B : GlobalTheory.LFun.Fam D.host.E) (μ : (AE D)ˣ →* Circle) (r : ℕ) (κ s : ℝ), IsHeckeChar D μ → ResEta D μ 0 → GlobalTheory.LFun.UnrOff (F := D.host.F) μ (S : Set (HeightOneSpectrum (𝓞 D.host.F))) → GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (S : Set (HeightOneSpectrum (𝓞 D.host.F)))) B r κ → κ + 1 < s → (∀ w ∉ GlobalTheory.LFun.above D.host.E (S : Set (HeightOneSpectrum (𝓞 D.host.F))), (∀ w' : HeightOneSpectrum (𝓞 D.host.E), w'.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) → w ≠ w' → B w' = (B w).map star) ∧ (¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (w.under (𝓞 D.host.F)) → (B w).map star = B w)) → ∃ l : ℝ, 0 < l ∧ GlobalTheory.LFun.LSD D S B μ (s : ℂ) = l := by
  intro D S B μ r κ s _ hb hμ hB hs hst
  classical
  have hc := isCMExt_host D
  have hb' := (resEta_iff μ 0).1 hb
  have hcv : Converges (above D.host.E (S : Set (HeightOneSpectrum (𝓞 D.host.F)))) (twist B (val μ)⁻¹) (s : ℂ) :=
    hB.converges_twist_val μ (by simpa using hs)
  have hpos : IsPosReal (LS (S : Set (HeightOneSpectrum (𝓞 D.host.F))) (twist B (val μ)⁻¹) (s : ℂ)) := by
    refine isPosReal_of_hasProd (hasProd_Lv hcv) hcv.ne_zero fun v => ?_
    have hnot : ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v.1 →
        w ∉ above D.host.E (S : Set (HeightOneSpectrum (𝓞 D.host.F))) := fun w hw e => v.2 (hw ▸ e)
    have hlt : ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v.1 →
        ∀ x ∈ twist B (val μ)⁻¹ w, ‖(x : ℂ) * npow w (-(s : ℂ))‖ < 1 := fun w hw =>
      norm_lt_one_of_bounded (hB.twist fun u _ => by simp [norm_val]) (by rw [Complex.ofReal_re]; linarith)
        (hnot w hw)
    have hun : ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v.1 → UnrAt μ w := fun w hw =>
      hμ w (hnot w hw)
    by_cases hv : IsSplit (E := D.host.E) v.1
    · obtain ⟨w, hw⟩ : ∃ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v.1 := by
        obtain ⟨P, -, -, hP, -⟩ := hv
        exact ⟨P, HeightOneSpectrum.ext hP⟩
      obtain ⟨w', hne, hall, hN, hN', -⟩ := SplitChart.exists_conj_place hc hw hv
      have hw' := (hall w').2 (Or.inr rfl)
      have e : Formalism.L2.Host.aboveF (L := D.host.E) D.host.F v.1 = {w, w'} := by ext u; simp [mem_aboveF, hall]
      have e2 : npow w' (-(s : ℂ)) = npow w (-(s : ℂ)) := by rw [npow, npow, hN, hN']
      have e3 : twist B (val μ)⁻¹ w' = (twist B (val μ)⁻¹ w).map star := by
        have hm := GlobalTheory.T.quadraticPowerCharacter_splitPlaces_values_inverse _ _ _ hc μ 0 hb' w w' (hw.trans hw'.symm) hne (hun w hw) (hun w' hw')
        have hs' : (val μ w')⁻¹ = star (val μ w)⁻¹ := by
          rw [star_inv, star_eq_inv (norm_val μ w), inv_inv, eq_comm, eq_inv_iff_mul_eq_one, hm]
        simp only [twist, Pi.inv_apply, hs', Multiset.map_map, Function.comp_def, star_mul',
          (hst w (hnot w hw)).1 w' (hw'.trans hw.symm) hne]
      rw [Lv, e, Finset.prod_pair hne, locL, locL, e2, ← eulerFac_add]
      refine isPosReal_eulerFac (by
        rw [e3, Multiset.map_add, Multiset.map_map, add_comm]
        simp only [Function.comp_def, star_star, Multiset.map_id']) (star_npow _ _) fun x hx => ?_
      exact (Multiset.mem_add.1 hx).elim (hlt w hw x) (e2 ▸ hlt w' hw' x)
    · refine isPosReal_prod _ fun w hw => ?_
      have hw := mem_aboveF.1 hw
      have hi : IsInertAt D.host.F D.host.E v.1 w := hw ▸ (split_or_inert D w).resolve_left (hw ▸ hv)
      refine isPosReal_eulerFac ?_ (star_npow _ _) (hlt w hw)
      have hs' : star (val μ w)⁻¹ = (val μ w)⁻¹ := by
        rw [star_inv, star_eq_inv (norm_val μ w), inv_inv, eq_inv_iff_mul_eq_one, ← sq,
          GlobalTheory.T.sq_value_eq_one_at_inert_place_of_restrictsToQuadratic _ _ _ hc μ 0 hb' _ w hi (hun w hw)]
      have hBw := (hst w (hnot w hw)).2 (by rw [hw]; exact hv)
      conv_rhs => rw [twist, ← hBw]
      simp only [twist, Pi.inv_apply, hs', Multiset.map_map, Function.comp_def, star_mul']
  obtain ⟨l, hl, e⟩ := isPosReal_iff.1 hpos
  exact ⟨l, hl, e⟩

end GlobalTheory.EulerConjPos

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBorelSphericalSameDoubleCosetSumsZonal
section
open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.GLDoubling

noncomputable section

namespace GlobalTheory.ZonalBorel

open GlobalTheory.PRep Formalism.UG

section Abstract

variable {G X V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup X] [Module ℂ X]
  [AddCommGroup V] [Module ℂ V]

theorem exists_fixed_sum_eq {ρ : Representation ℂ G X} {π : Representation ℂ G V} (hρ : IsSmooth ρ)
    {K : Subgroup G} (hK : IsCompact (K : Set G)) (f : ρ.IntertwiningMap π) (hf : Function.Surjective f)
    (E : X →ₗ[ℂ] ℂ) (hE : ∀ u : X, (∀ x ∈ K, ρ x u = u) → E u = 0 → u = 0) {v : V} (hv : v ∈ fixed π K)
    (l : Module.Dual ℂ V) (hlv : l v = 1) :
    ∃ z : X, (∀ x ∈ K, ρ x z = z) ∧ E z = 1 ∧ ∀ S : Finset (G ⧸ K), (∀ x ∈ K, ∀ c ∈ S, x • c ∈ S) →
      ∑ c ∈ S, l (π c.out v) = ∑ c ∈ S, E (ρ c.out z) := by
  obtain ⟨u, rfl⟩ := hf v
  obtain ⟨w, hw, hfw⟩ := IwahoriOnto.exists_fixed_map_eq hρ hK f.toLinearMap u fun h hh => by
    show f (ρ h u) = f u
    rw [f.isIntertwining]
    simpa using hv ⟨h, hh⟩
  have hw' : ∀ x ∈ K, ρ x w = w := fun x hx => by simpa using hw ⟨x, hx⟩
  have hfw' : f w = f u := hfw
  have hEw : E w ≠ 0 := fun h => by
    have h0 := hE w hw' h
    rw [h0, map_zero] at hfw'
    rw [← hfw', map_zero] at hlv
    exact zero_ne_one hlv
  refine ⟨(E w)⁻¹ • w, fun x hx => by rw [map_smul, hw' x hx], by simp [hEw], fun S hS => ?_⟩
  set z := (E w)⁻¹ • w with hz
  have hzK : ∀ x ∈ K, ρ x z = z := fun x hx => by rw [hz, map_smul, hw' x hx]
  have hEz : E z = 1 := by simp [hz, hEw]
  have hfz : f z = (E w)⁻¹ • f u := by rw [hz, map_smul, hfw']
  have h1 := hE (∑ c ∈ S, ρ c.out z - (∑ c ∈ S, E (ρ c.out z)) • z)
    (fun x hx => by rw [map_sub, Rep.sum_fixed ρ K hzK S hS x hx, map_smul, hzK x hx])
    (by rw [map_sub, map_sum, map_smul, hEz, smul_eq_mul, mul_one, sub_self])
  have h2 := congrArg (fun y => l (f y)) (sub_eq_zero.1 h1)
  have hI : ∀ c : G ⧸ K, f (ρ c.out z) = π c.out (f z) := fun c => f.isIntertwining _ _ _ _
  simp only [map_sum, map_smul, hI, hfz, smul_eq_mul, hlv, mul_one] at h2
  rw [← Finset.mul_sum] at h2
  exact (mul_right_injective₀ (inv_ne_zero hEw)).eq_iff.1 (h2.trans (mul_comm _ _))

end Abstract

theorem exists_isBorelSph_hAct_eq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (α : Fin n → ℂˣ), HasSatake π α → ∀ ω : GL (Fin n) k → ℂ, IsZonal π (KO k (Fin n)) ω → ∃ φ : GL (Fin n) k → ℂ, IsBorelSph k (fun i : Fin n => (α i : ℂ) * (((resCard k : ℝ) ^ (((i : ℕ) : ℝ) - ((n : ℝ) - 1) / 2) : ℝ) : ℂ)) φ ∧ ∀ g, Formalism.UG.hAct (KO k (Fin n)) (Formalism.UG.dosetInd ℂ (KO k (Fin n)) g) ω 1 = Formalism.UG.hAct (KO k (Fin n)) (Formalism.UG.dosetInd ℂ (KO k (Fin n)) g) φ 1 := by
  intro k _ _ _ _ n V _ _ π α ⟨_, _hs, S, f, hf⟩ ω ⟨v, hv, l, _hl, hlv, hω⟩
  have hsm : IsSmooth S.toRepresentation :=
    IsSubquotient.isSmooth ⟨S, .id _, Function.surjective_id⟩ (isSmooth_parInd _ _)
  let E : S.toSubmodule →ₗ[ℂ] ℂ := ⟨⟨fun u => u.1.1.1 1, fun _ _ => rfl⟩, fun _ _ => rfl⟩
  have hr : ∀ u : S.toSubmodule, (∀ x ∈ KO k (Fin n), S.toRepresentation x u = u) →
      ∀ g, ∀ x ∈ KO k (Fin n), u.1.1.1 (g * x) = u.1.1.1 g := fun u h g x hx =>
    congrArg (fun z : S.toSubmodule => z.1.1.1 g) (h x hx)
  obtain ⟨z, hzK, hEz, key⟩ := exists_fixed_sum_eq hsm SplitFlip.isCompact_KO f hf E (fun u h h0 => by
    refine Subtype.ext (Subtype.ext (Subtype.ext (funext fun g => ?_)))
    obtain ⟨b, hb, x, hx, rfl⟩ := iwasawa_blockTriangular k (Fin n) Fin.val g
    have h1 := parInd_law _ _ u.1 ⟨b, (mem_borel _).2 hb⟩ 1
    have h2 : u.1.1.1 1 = 0 := h0
    rw [h2, map_zero, smul_zero, mul_one] at h1
    exact (hr u h b x hx).trans h1) hv l hlv
  refine ⟨fun g => z.1.1.1 g, ⟨hr z hzK, fun b hb t ht => ?_⟩, fun g => ?_⟩
  · have h1 := Rep.law α z.1 b hb t ht 1
    have h2 : z.1.1.1 1 = 1 := hEz
    rwa [h2, mul_one, mul_one] at h1
  · have hK : IsCommensurated (KO k (Fin n)) :=
      PI.UnitaryGroupMassFormula.AdIndexEq.commensurated_of_isOpen_isCompact _ SplitFlip.isOpen_KO SplitFlip.isCompact_KO
    have hfin := Formalism.UG.P.finite_support_cosets hK (Formalism.UG.Final.DosetIndMem _ (KO k (Fin n)) ℂ g).2
    have hmem : ∀ c : GL (Fin n) k ⧸ KO k (Fin n), c ∈ hfin.toFinset ↔
        c.out ∈ DoubleCoset.doubleCoset g (KO k (Fin n) : Set (GL (Fin n) k)) (KO k (Fin n)) := fun c => by
      simp [dosetInd]
    have hT : ∀ x ∈ KO k (Fin n), ∀ c ∈ hfin.toFinset, x • c ∈ hfin.toFinset := by
      intro x hx c hc
      obtain ⟨a, ha, rfl⟩ := (GlobalTheory.ChainOnto.out_mem_doubleCoset_iff g c).1 ((hmem c).1 hc)
      refine (hmem _).2 ((GlobalTheory.ChainOnto.out_mem_doubleCoset_iff g _).2 ⟨x * a, mul_mem hx ha, ?_⟩)
      rw [mul_assoc]
      rfl
    have e : ∀ F : GL (Fin n) k → ℂ, hAct (KO k (Fin n)) (dosetInd ℂ (KO k (Fin n)) g) F 1 =
        ∑ c ∈ hfin.toFinset, F c.out := by
      intro F
      rw [hAct, finsum_eq_sum_of_support_subset (s := hfin.toFinset)]
      · refine Finset.sum_congr rfl fun c hc => ?_
        rw [dosetInd, Set.indicator_of_mem ((hmem c).1 hc), one_mul, Pi.one_apply, one_smul]
      · intro c hc
        rw [Function.mem_support] at hc
        refine (hmem c).2 ?_
        by_contra h
        rw [dosetInd, Set.indicator_of_notMem h, zero_smul] at hc
        exact hc rfl
    rw [e, e]
    refine ((Finset.sum_congr rfl fun c _ => hω c.out).trans (key _ hT)).trans
      (Finset.sum_congr rfl fun c _ => ?_)
    show z.1.1.1 (1 * c.out) = _
    rw [one_mul]

end GlobalTheory.ZonalBorel
end
end

