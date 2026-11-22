import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StabOrd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0346
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0106
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0345
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0113
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0281
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RelIndexHomLatticeInertMoveSource
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFinWeil
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0264
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0201
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0347

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OmPureTensorOOnb
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexOrder

namespace GlobalTheory.KJRealOnb

variable {D : D7}

theorem det_ne_zero_of_onb {k : ℕ} {G B : Matrix (Fin k) (Fin k) ℂ} (hG : IsCartanInv G 1)
    (hB : ∃ p, IsONBasis G 1 B p) : G.det ≠ 0 ∧ B.det ≠ 0 := by
  have hP : G.PosDef := by simpa using hG.2.2
  have hGd : G.det ≠ 0 := hP.det_pos.ne'
  refine ⟨hGd, fun h0 => ?_⟩
  obtain ⟨p, ε, hε, h1, -⟩ := hB
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_mul, h0, mul_zero, Matrix.det_diagonal] at h2
  refine (Finset.prod_ne_zero_iff.2 fun a _ => ?_) h2.symm
  rcases hε a with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]

theorem det_inB (θ : InfFam D) (V : HSp D) (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (g : GA D V)
    (τ : D.what₂.Tau) (hB : (B τ).det ≠ 0) : (inB θ V B g τ).det = (compAt θ τ (mt V g)).det := by
  unfold inB
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, ← Matrix.det_mul, Matrix.mul_nonsing_inv _ (Ne.isUnit hB), Matrix.det_one, one_mul]

theorem comp_eq_mul_inB (θ : InfFam D) (V : HSp D) (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (g : GA D V)
    (hB : ∀ τ, (B τ).det ≠ 0) : (fun τ => compAt θ τ (mt V g) * B τ) = fun τ => B τ * inB θ V B g τ := by
  funext τ
  unfold inB
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (Ne.isUnit (hB τ)), Matrix.one_mul]

end GlobalTheory.KJRealOnb

namespace GlobalTheory.KJReal

open GlobalTheory.KJRealOnb in

theorem om_pureTensorO_onb : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (x : DefSp S) (y : DefSp T) (μ : (AE D)ˣ →* Circle) (om : Om S T), IsInfFam θ → x.Is → y.Is → x.s = (fun _ => 1) → y.s = (fun _ => 1) → Even S.rank → Even T.rank → IsWeilDatumO ψ S T μ μ om → ∀ e : D.what₂.Tau → ℤ, (∀ τ, HasInfExp D μ τ (e τ)) → ∀ f, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 1) f) → ∀ k ∈ GinfC S, ∀ k' ∈ GinfC T, ∀ P, om (k, k') (pureTensorO ψ θ S T x.s y.s x.B y.B f P) = (∏ τ, (inB θ S x.B k τ).det ^ (-e τ - T.rank / 2 : ℤ) * (inB θ T y.B k' τ).det ^ (e τ + S.rank / 2 : ℤ)) • pureTensorO ψ θ S T x.s y.s x.B y.B f (mvZ (fun τ => (inB θ S x.B k τ)⁻¹) (inB θ T y.B k') P) := by
  intro D ψ θ S T x y μ om hθ hx hy hxs hys eS eT hom e he f hf hv k hk k' hk' P
  obtain ⟨mS, hmS⟩ := eS
  obtain ⟨mT, hmT⟩ := eT
  obtain ⟨η, hη⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  have hψ := hom.std
  have cS : ∀ τ, IsCartanInv (gramAt D S τ) 1 := fun τ => by have h := hx.cart τ; rw [hxs] at h; exact h
  have cT : ∀ τ, IsCartanInv (gramAt D T τ) 1 := fun τ => by have h := hy.cart τ; rw [hys] at h; exact h
  have dS : ∀ τ, (gramAt D S τ).det ≠ 0 ∧ (x.B τ).det ≠ 0 := fun τ =>
    det_ne_zero_of_onb (cS τ) (by have h := hx.onb τ; rw [hxs] at h; exact h)
  have dT : ∀ τ, (gramAt D T τ).det ≠ 0 ∧ (y.B τ).det ≠ 0 := fun τ =>
    det_ne_zero_of_onb (cT τ) (by have h := hy.onb τ; rw [hys] at h; exact h)
  obtain ⟨xr, hxr, hxv⟩ := GlobalTheory.OneMapRef.RealMove.exists_root hθ S (fun τ => (dS τ).1) k hk
  obtain ⟨yr, hyr, hyv⟩ := GlobalTheory.OneMapRef.RealMove.exists_root hθ T (fun τ => (dT τ).1) k' hk'
  have hvac := GlobalTheory.WeilVacChar.vacuum_character D ψ hψ S T θ hθ μ μ om η hη hom (fun _ => 1) (fun _ => 1)
    cS cT k hk k' hk' (fun τ => by rw [Matrix.one_mul, Matrix.mul_one])
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) xr yr hxr hyr f hf hv
  have expT : ∀ τ, HasInfExp D (μ * (η ^ T.rank)⁻¹) τ ((e τ - mT : ℤ) : ℚ) := fun τ => by
    have h1 := GlobalTheory.OneMapRef.RealMove.hasInfExp_twist (he τ) (hη.2.2.2 τ) T.rank
    convert h1 using 1
    rw [hmT]; push_cast; ring
  have expS : ∀ τ, HasInfExp D (μ * (η ^ S.rank)⁻¹) τ ((e τ - mS : ℤ) : ℚ) := fun τ => by
    have h1 := GlobalTheory.OneMapRef.RealMove.hasInfExp_twist (he τ) (hη.2.2.2 τ) S.rank
    convert h1 using 1
    rw [hmS]; push_cast; ring
  have vx := hxv _ (fun τ => e τ - mT) expT
  have vy := hyv _ (fun τ => e τ - mS) expS
  have hmain := (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T μ μ om hom hθ (fun _ => 1) (fun _ => 1) x.B
    (fun τ => compAt θ τ (mt S k) * x.B τ) (fun _ => 1) (fun _ => 1) y.B
    (fun τ => compAt θ τ (mt T k') * y.B τ) k k' (fun τ => by rw [Matrix.one_mul, Matrix.mul_one])
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) (fun τ => rfl) (fun τ => rfl) f hf P).2
  rw [hxs, hys, hmain, hvac, GlobalTheory.FiniteFock.pureTensorO_smul, comp_eq_mul_inB θ S x.B k (fun τ => (dS τ).2),
    comp_eq_mul_inB θ T y.B k' (fun τ => (dT τ).2),
    GlobalTheory.FockBaseChange.pureTensorO_subst D ψ θ S T hψ hθ x.B (inB θ S x.B k) y.B (inB θ T y.B k') f hf P]
  congr 1
  · rw [Circle.coe_mul, Circle.coe_inv, vx, vy, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    have inv := congrArg Matrix.det (GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := θ) τ k)
    rw [Matrix.det_mul, Matrix.det_one] at inv
    have g0 := left_ne_zero_of_mul_eq_one inv
    have inv' := congrArg Matrix.det (GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := θ) τ k')
    rw [Matrix.det_mul, Matrix.det_one] at inv'
    have g0' := left_ne_zero_of_mul_eq_one inv'
    rw [GlobalTheory.KJReal.detPlus_one_one, eq_inv_of_mul_eq_one_right inv, det_inB θ S x.B k τ (dS τ).2,
      det_inB θ T y.B k' τ (dT τ).2]
    have a1 : -e τ - (T.rank : ℤ) / 2 = -e τ - mT := by omega
    have a2 : e τ + (S.rank : ℤ) / 2 = e τ + mS := by omega
    rw [a1, a2]
    exact GlobalTheory.KJReal.exp_identity _ _ g0 g0' (e τ) mS mT S.rank T.rank (by rw [hmS]; push_cast; ring)
      (by rw [hmT]; push_cast; ring)

end GlobalTheory.KJReal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacewiseToAdelicDecompositionForall
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.PlacesAdeles

variable {D : D7}

theorem mem_congGrp {V : HSp D} {I : Ideal (AE D)} {g : GA D V} :
    g ∈ congGrp V I ↔ ∀ i j, mt V g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j ∈ I := by
  unfold congGrp
  rw [MonoidHom.mem_ker]
  constructor
  · intro h i j
    have := congrArg (fun x : GL (Fin V.rank) (AE D ⧸ I) => x.1 i j) h
    rw [← Ideal.Quotient.eq]
    simp [Formalism.L2.Theta.mt, Matrix.one_apply] at this ⊢
    exact this
  · intro h
    ext i j
    have := h i j
    rw [← Ideal.Quotient.eq] at this
    simp [Formalism.L2.Theta.mt, Matrix.one_apply] at this ⊢
    exact this

theorem idAt_single_le {P : Pl D → Prop} {v : Pl D} (hv : P v) : idAt D (· = v) ≤ idAt D P := by
  intro a ha
  unfold idAt at ha ⊢
  simp only [Submodule.mem_inf, Submodule.mem_iInf] at ha ⊢
  refine ⟨ha.1, fun w => ha.2 ⟨w.1, fun h => w.2 (by rw [h]; exact hv)⟩⟩

theorem idAt_le_idOff {v w : Pl D} (h : v ≠ w) : idAt D (· = w) ≤ idOff D (· = v) := by
  intro a ha
  unfold idAt at ha
  unfold idOff
  simp only [Submodule.mem_inf, Submodule.mem_iInf] at ha ⊢
  intro u
  have hu : u.1 = v := u.2
  exact ha.2 ⟨u.1, fun e => h (hu.symm.trans e)⟩

theorem idOff_le_single {P : Pl D → Prop} {v : Pl D} (hv : P v) : idOff D P ≤ idOff D (· = v) := by
  intro a ha
  unfold idOff at ha ⊢
  simp only [Submodule.mem_iInf] at ha ⊢
  intro u
  have hu : u.1 = v := u.2
  exact ha ⟨u.1, by rw [hu]; exact hv⟩

theorem congGrp_mono {V : HSp D} {I J : Ideal (AE D)} (h : I ≤ J) : congGrp V I ≤ congGrp V J := by
  intro g hg
  rw [mem_congGrp] at hg ⊢
  exact fun i j => h (hg i j)

theorem eq_zero_of_at_off (P : Pl D → Prop) {a : AE D} (h1 : a ∈ idAt D P) (h2 : a ∈ idOff D P) : a = 0 := by
  obtain ⟨ε, -, -, -, hA, hO⟩ := (GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D P).1
  rw [← (hA a).1 h1]
  exact (hO a).1 h2

theorem mt_mul (S : HSp D) (a b : GA D S) : mt S (a * b) = mt S a * mt S b := by
  simp [Formalism.L2.Theta.mt, map_mul]

theorem mt_one (S : HSp D) : mt S 1 = 1 := by
  simp [Formalism.L2.Theta.mt]

theorem supp_mulVec (S : HSp D) (P : Pl D → Prop) (g : GA D S) {y : Fin S.rank → AE D}
    (hy : ∀ i, y i ∈ idAt D P) : ∀ i, (mt S g *ᵥ y) i ∈ idAt D P := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)

theorem mulVec_off {S : HSp D} {P : Pl D → Prop} {b : GA D S} (hb : b ∈ grpOff S P) {y : Fin S.rank → AE D}
    (hy : ∀ i, y i ∈ idAt D P) : mt S b *ᵥ y = y := by
  rw [grpOff, mem_congGrp] at hb
  have key : (mt S b - 1) *ᵥ y = 0 := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    apply eq_zero_of_at_off P
    · exact Ideal.mul_mem_left _ _ (hy j)
    · exact Ideal.mul_mem_right _ _ (by simpa using hb i j)
  rw [Matrix.sub_mulVec, sub_eq_zero, Matrix.one_mulVec] at key
  exact key

theorem moves_mul {S : HSp D} {L : Lat S} {P : Pl D → Prop} {x x' : GA D S} (hx : Moves S x L L P)
    (hx' : Moves S x' L L P) : Moves S (x * x') L L P := by
  intro y hy
  rw [mt_mul, ← Matrix.mulVec_mulVec, hx' y hy]
  exact hx _ (supp_mulVec S P x' hy)

theorem moves_inv {S : HSp D} {L : Lat S} {P : Pl D → Prop} {x : GA D S} (hx : Moves S x L L P) :
    Moves S x⁻¹ L L P := by
  intro y hy
  have h1 := hx (mt S x⁻¹ *ᵥ y) (supp_mulVec S P _ hy)
  rw [Matrix.mulVec_mulVec, ← mt_mul, mul_inv_cancel, mt_one, Matrix.one_mulVec] at h1
  exact h1.symm

theorem moves_off {S : HSp D} {L : Lat S} {P : Pl D → Prop} {b : GA D S} (hb : b ∈ grpOff S P) :
    Moves S b L L P := by
  intro y hy
  rw [mulVec_off hb hy]

theorem latV_eq_ae : ∀ (D : D7) (S : HSp D) (L M : Lat S), Submodule.IsLattice D.host.E L → Submodule.IsLattice D.host.E M → ∃ T : Finset (Pl D), ∀ v, v ∉ T → latV S L (· = v) = latV S M (· = v) := GlobalTheory.T.lattices_agree_almost_everywhere

end GlobalTheory.FinPl.PlacesAdeles

namespace GlobalTheory.FinPl

open GlobalTheory.FinPl.PlacesAdeles in

theorem placesToAdeles (D : D7) : PlacesToAdeles D := by
  classical
  intro S L P hL R h hyp
  obtain ⟨M, hM, hmove⟩ := (GlobalTheory.T.selfDual_image_adelicPoint_wittCore D S L hL).1 h
  obtain ⟨T, hT⟩ := latV_eq_ae D S L M hL.1 hM.1
  have hfar : ∀ v, v ∉ T → Moves S h L L (· = v) := by
    intro v hv y hy
    have := hmove (· = v) y hy
    rwa [← hT v hv] at this
  have hloc : ∀ v, P v → ∃ r ∈ R, r ∈ grpAt S (· = v) ∧ Moves S (r⁻¹ * h) L L (· = v) := by
    intro v hv
    obtain ⟨hv', -, h', hh', hdec, r, hr, hrv, κ, hκ, hvk⟩ := hyp v hv
    refine ⟨r, hr, hrv, ?_⟩
    have : r⁻¹ * h = κ * h' := by rw [hdec, hvk]; group
    rw [this]
    exact moves_mul hκ.2 (moves_off hh')
  have key : ∀ T' : Finset (Pl D), (∀ v ∈ T', P v) → ∃ r ∈ R, r ∈ grpAt S P ∧
      (∀ v, v ∉ T' → r ∈ grpOff S (· = v)) ∧ ∀ v ∈ T', Moves S (r⁻¹ * h) L L (· = v) := by
    intro T'
    induction T' using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨1, R.one_mem, (grpAt S P).one_mem, fun _ _ => Subgroup.one_mem _, by simp⟩
    | insert v₀ T' hv₀ ih =>
      intro hP
      obtain ⟨r, hr, hrP, hroff, hrm⟩ := ih (fun v hv => hP v (Finset.mem_insert_of_mem hv))
      have hP₀ : P v₀ := hP v₀ (Finset.mem_insert_self _ _)
      obtain ⟨r₀, hr₀, hr₀v, hm₀⟩ := hloc v₀ hP₀
      refine ⟨r * r₀, R.mul_mem hr hr₀, (grpAt S P).mul_mem hrP (congGrp_mono (idAt_single_le hP₀) hr₀v), ?_, ?_⟩
      · intro v hv
        have hne : v ≠ v₀ := fun e => hv (e ▸ Finset.mem_insert_self _ _)
        exact (grpOff S _).mul_mem (hroff v fun h => hv (Finset.mem_insert_of_mem h))
          (congGrp_mono (idAt_le_idOff hne) hr₀v)
      · intro v hv
        rw [_root_.mul_inv_rev, mul_assoc]
        rcases Finset.mem_insert.1 hv with rfl | hv
        · have hroff0 := hroff v hv₀
          have hcomm : r₀⁻¹ * r⁻¹ = r⁻¹ * r₀⁻¹ :=
            ((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· = v)).2 S).2.1 _ (inv_mem hr₀v) _ (inv_mem hroff0)
          rw [← mul_assoc, hcomm, mul_assoc]
          exact moves_mul (moves_off (inv_mem hroff0)) hm₀
        · have hne : v ≠ v₀ := fun e => hv₀ (e ▸ hv)
          exact moves_mul (moves_off (inv_mem (congGrp_mono (idAt_le_idOff hne) hr₀v))) (hrm v hv)
  obtain ⟨r, hr, hrP, hroff, hrm⟩ := key (T.filter P) (fun v hv => (Finset.mem_filter.1 hv).2)
  have hall : ∀ v, P v → Moves S (r⁻¹ * h) L L (· = v) := by
    intro v hv
    by_cases hvT : v ∈ T
    · exact hrm v (Finset.mem_filter.2 ⟨hvT, hv⟩)
    · exact moves_mul (moves_off (inv_mem (hroff v (fun h => hvT (Finset.mem_filter.1 h).1)))) (hfar v hvT)
  obtain ⟨hdec, hcomm, -, hlat⟩ := (GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D P).2 S
  obtain ⟨κ, hκ, g, hg, hx⟩ := hdec (r⁻¹ * h)
  have hκv : ∀ v, P v → Moves S κ L L (· = v) := by
    intro v hv
    have : κ = (r⁻¹ * h) * g⁻¹ := by rw [hx]; group
    rw [this]
    exact moves_mul (hall v hv) (moves_off (inv_mem (congGrp_mono (idOff_le_single hv) hg)))
  refine ⟨r, hr, hrP, g, hg, κ, ⟨hκ, ?_⟩, ?_⟩
  · intro y hy
    rw [hlat L y hL.1, hlat L _ hL.1]
    have hy' := supp_mulVec S P κ hy
    have hey : ∀ v e, e ∈ intAt D (· = v) → ∀ i, (e • y) i ∈ idAt D (· = v) := fun v e he i => by
      simpa [smul_eq_mul] using Ideal.mul_mem_right (y i) _ he.1
    constructor
    · rintro ⟨-, h2⟩
      refine ⟨hy', fun v hv e he => ?_⟩
      rw [← Matrix.mulVec_smul]
      exact (hκv v hv _ (hey v e he)).1 (h2 v hv e he)
    · rintro ⟨-, h2⟩
      refine ⟨hy, fun v hv e he => ?_⟩
      have := h2 v hv e he
      rw [← Matrix.mulVec_smul] at this
      exact (hκv v hv _ (hey v e he)).2 this
  · calc h = r * (r⁻¹ * h) := by group
      _ = r * (κ * g) := by rw [hx]
      _ = r * g * κ := by rw [hcomm κ hκ g hg, mul_assoc]

theorem placesToAdeles_all : ∀ D : D7, PlacesToAdeles D := placesToAdeles

end GlobalTheory.FinPl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalFinitePartMemHomLatticeCompletionIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.RatLat

open GlobalTheory.LatVac

variable {D : D7}

theorem eq_of_parts {m n : ℕ} {u u' : Formalism.IndefR.Datum.Mx D m n} (h1 : u.map (infPart D) = u'.map (infPart D))
    (h2 : u.map (finPart D) = u'.map (finPart D)) : u = u' := by
  ext i j
  rw [← sub_eq_zero]
  apply eq_zero_of_parts
  · rw [RingHom.map_sub, sub_eq_zero]; exact congrFun (congrFun h1 i) j
  · rw [RingHom.map_sub, sub_eq_zero]; exact congrFun (congrFun h2 i) j

theorem finTens_mem_iff {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    finTens 1 M ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ↔
      M ∈ latRat S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) := by
  refine ⟨fun h => ?_, finTens_mem_latO (one_mem_intAf _)⟩
  refine (GlobalTheory.T.rationalHermitianRankOneLattice_selfDual D S T ΛS ΛT hS hT (GlobalTheory.T.exists_dual_family_selfDual_hermitianSpace D S ΛS hS) _).2 fun ℓ hℓ => ?_
  have h1 := char_sympl_eq_one hψ hS hT h (finTens_mem_latO (one_mem_intAf _) hℓ)
  rw [symplO_finTens, one_mul, one_mul] at h1
  exact (char_rat hψ _).1 h1

theorem genMap_mulVec (S T : HSp D) (a : D.host.E) (s y : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) :
    genMap S T a s t *ᵥ y = a • (∑ i, ∑ j, star (s i) * S.gram i j * y j) • t := by
  funext i
  simp only [genMap, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem mem_latRat_iff_perO {S T : HSp D}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (hS : IsSelfDualC S ΛS) (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    M ∈ latRat S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) ↔
      Matrix.toLin' M ∈ perO (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) ΛS ΛT := by
  constructor
  · intro h
    induction h using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a, ha, s, hs, t, ht, rfl⟩ := hw
      refine Submodule.subset_span ⟨a, ha, Matrix.toLin' (genMap S T 1 s t), fun y hy => ?_, ?_⟩
      · obtain ⟨b, hb⟩ := (hS.2 y).1 hy s hs
        rw [Matrix.toLin'_apply, genMap_mulVec, one_smul, ← hb]
        exact ΛT.smul_mem b ht
      · refine LinearMap.ext fun y => ?_
        rw [LinearMap.smul_apply, Matrix.toLin'_apply, Matrix.toLin'_apply, genMap_mulVec, genMap_mulVec, one_smul]
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | neg x _ hx => rw [map_neg]; exact neg_mem hx
  · intro h
    obtain ⟨n, s, s', hs, hd⟩ := GlobalTheory.T.exists_dual_family_selfDual_hermitianSpace D S ΛS hS
    have key : ∀ z ∈ perO (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) ΛS ΛT,
        LinearMap.toMatrix' z ∈ latRat S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨r, hr, x, hx, rfl⟩ := hw
        have e : LinearMap.toMatrix' (r • x) = ∑ k, genMap S T r (s' k) (x (s k)) := by
          refine Matrix.ext fun i j => ?_
          have e1 : (Pi.single j 1 : Fin S.rank → D.host.E) = ∑ k, (∑ l, star (s' k l) * S.gram l j) • s k := by
            funext c
            rw [Finset.sum_apply, Pi.single_apply, ← hd c j]
            exact Finset.sum_congr rfl fun k _ => mul_comm (s k c) _
          have e2 : LinearMap.toMatrix' (r • x) i j = r * x (Pi.single j 1) i := by
            rw [LinearMap.toMatrix'_apply]
            first
              | rfl
              | (congr 3; funext c; simp [Pi.single_apply])
          rw [e2, e1, map_sum, Matrix.sum_apply, Finset.sum_apply, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          rw [LinearMap.map_smul]
          change r * ((∑ l, star (s' k l) * S.gram l j) * x (s k) i) = r * x (s k) i * ∑ l, star (s' k l) * S.gram l j
          ring
        refine e ▸ AddSubgroup.sum_mem _ fun k _ => ?_
        exact AddSubgroup.subset_closure ⟨r, hr, _, (hs k).2, _, hx _ (hs k).1, rfl⟩
      | zero => rw [map_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | smul c x _ hx =>
        have e : LinearMap.toMatrix' (c • x) = (c : D.host.E) • LinearMap.toMatrix' x := by
          rw [← map_smul]; rfl
        rw [e]
        exact smul_mem_latRat c hx
    have := key _ h
    rwa [LinearMap.toMatrix'_toLin'] at this

theorem AA_eq (h : D.host.ccK = ⊤) : D.host.AA = D.host.AA0 := by
  rw [Host.AA, Host.ccE, h, Ideal.map_top, FractionalIdeal.coeIdeal_top, one_mul]

theorem finOf_mem_iff : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) N N', (ΛS : Set (Fin S.rank → D.host.E)) = latFr S hS N → (ΛT : Set (Fin T.rank → D.host.E)) = latFr T hT N' → IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ γ v, GlobalTheory.AdTh.IsFinOf S T γ v → (v ∈ (latO S T (latFr S hS N) (latFr T hT N') fun _ => True) ↔ toHom S T hS hT γ ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') := by
  intro D ψ θ S T a b hS hT δ sc hP ΛS ΛT N N' h1 h2 hΛS hΛT γ v hv
  subst hS hT
  have e1 : N = ΛS := (SetLike.coe_injective h1).symm
  have e2 : N' = ΛT := (SetLike.coe_injective h2).symm
  have : v = finTens 1 γ :=
    eq_of_parts (hv.1.trans (Matrix.ext fun i j => (infPart_pair _ _).symm)) (hv.2.trans rfl)
  rw [← h1, ← h2, this, finTens_mem_iff hP.std hΛS hΛT, mem_latRat_iff_perO ΛT hΛS, AA_eq hP.cc, e1, e2]
  rfl

end GlobalTheory.AdForm.RatLat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealEqualityOfColumns
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam

theorem realEq_of_colOK : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ f : FamCh W u, f.ColOK → RealEq f.t := by
  intro D L hT Gi Gl Kc Yd cX ex W u _ f hf j hj s s' a ha b hb φ hφ
  obtain ⟨θ, hθ⟩ := GlobalTheory.DualPairCompare.exists_infFam D
  have hL := W.Q.charW.base.lev
  let k : Fin D.R.m := ⟨j, hj⟩
  have hexp : ∀ τ, ∃ e : ℚ, HasInfExp D ((pk W).toLevCh.mu s (j + 1)) τ e ∧
      HasInfExp D ((pk W).toLevCh.mu s' (j + 1)) τ e := by
    intro τ
    obtain ⟨n, hn, ho⟩ := hL.xi_fin s
    obtain ⟨n', hn', ho'⟩ := hL.xi_fin s'
    have h0 := GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (hL.mu0 k)
      (GlobalTheory.Chain.StepVac.hasInfQ_tau ((pk W).C.isMu0 k).inf) τ
    exact ⟨_, GlobalTheory.Chain.StepVac.hasInfExp_mul h0 (GlobalTheory.Chain.StepVac.hasInfExp_of_order hθ (hL.xi s) hn ho τ),
      GlobalTheory.Chain.StepVac.hasInfExp_mul h0 (GlobalTheory.Chain.StepVac.hasInfExp_of_order hθ (hL.xi s') hn' ho' τ)⟩
  exact GlobalTheory.RealEqWeil.weilDatum_realEq D _ _ _ _ _ _ _ _ _ (hf.kom s j hj) (hf.kom s' j hj) hexp hexp a ha b hb φ hφ

end GlobalTheory.Fam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RelIndexHomLatticeInertMoveSourceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_homLattice_inert_move_source : ∀ (D : D7) (S T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsInertAt D.host.F D.host.E v w → ∀ c ϖ e, IsUnramInv ϖ c (qV D.host.F v) → IsInertChart D.sp.cm.sig S.gram (frameLat S) h c e → ∀ (d : Fin S.rank → ℤ) (t : GU c S.rank), t.1.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KU c S.rank, ∀ k₂ ∈ KU c S.rank, GlobalTheory.FinWeil.idx (GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)) ((GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).map (GlobalTheory.FinWeilO.rhoF S T (embV S v (e.symm (k₁ * t * k₂)), 1))) = qV D.host.E w ^ (T.rank * (∑ i, max (d i) 0).toNat) := by
  first | exact @GlobalTheory.InertHomIdx.idx_latF_map_rhoF_eq_qV_pow | exact GlobalTheory.InertHomIdx.idx_latF_map_rhoF_eq_qV_pow | (intros; apply GlobalTheory.InertHomIdx.idx_latF_map_rhoF_eq_qV_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleLiftCombinationOfLawsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSawDoubleLiftCombination_of_laws : ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), BiAct D → CenFock D → LiftSum D → c.Is → (∀ s, (t s).Is) → RealEq t → KerX t → RdX t → TwoX t := by
  first | exact @GlobalTheory.SeeSaw.twoX_of_laws | exact GlobalTheory.SeeSaw.twoX_of_laws | (intros; apply GlobalTheory.SeeSaw.twoX_of_laws <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawPeriodsLinearRelationsDoubleStepStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSaw_periods_linearRelations_doubleStep : ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), DoubleStep D → c.Is → (∀ s, (t s).Is) → (∀ s, (t s).LocFin) → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) P₁ P₂ (I : Type) [Fintype I] (s : I → 𝒯) (α : I → ℂ) (φ : ∀ i, (t (s i)).Ch j → GA D (c.X j) → ℂ) (f : I → GA D (c.V (j + 1 + 1)) → ℂ), (∀ i a, IsContAut (c.X j) (φ i a)) → (∀ i, RapidDec _ (f i)) → (∀ i, RapidDec _ (liftS ((t (s i)).om (j + 1)) (c.vol (j + 1 + 1)).μ (c.vol (j + 1 + 1)).𝓕 (f i) ((t (s i)).pt (j + 1) P₂))) → (∀ a ∈ GinfC (c.V (j + 1)), ∀ a' ∈ GinfC (c.V (j + 1 + 1)), ∃ v : I → ℂ, (∀ i, Iter2 (c.ρJ j (σ + 1) h) (c.μf (j + 1)) (c.ρB (j + 1 + 1) σ (idx_step h)) (c.μf (j + 1 + 1)) (fun q₁ q₂ => (t (s i)).integrand j σ h P₁ P₂ (φ i) (f i) (a * q₁.1) (a' * q₂.1)) (v i)) ∧ ∑ i, α i * v i = 0) → ∑ i, α i * (t (s i)).perF j (σ + 1) h (φ i) (liftS ((t (s i)).om j) (c.vol (j + 1)).μ (c.vol (j + 1)).𝓕 (liftS ((t (s i)).om (j + 1)) (c.vol (j + 1 + 1)).μ (c.vol (j + 1 + 1)).𝓕 (f i) ((t (s i)).pt (j + 1) P₂)) ((t (s i)).pt j P₁)) = 0 := by
  first | exact @GlobalTheory.SeeSaw.VanMany.vanMany | exact GlobalTheory.SeeSaw.VanMany.vanMany | (intros; apply GlobalTheory.SeeSaw.VanMany.vanMany <;> assumption)
end

