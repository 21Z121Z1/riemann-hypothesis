import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0423
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0241
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0407
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeakTopologyWittTiltTensor
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlTowerGen
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0408
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Formalism.SharpRestriction.LevelLetterCocycles.RamificationTwoAndConjugationAtQAndD
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0421
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0013
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIterateDerivative
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0415
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0409

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousLoc
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

noncomputable section

namespace GlobalTheory.PotDual

def bundle {G : Type} [Group G] [TopologicalSpace G] (Qp : Type) {LL : Type} (O : Type) [Field Qp]
    [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    [IsTopologicalRing LL] {k : ℕ} (M : G →* Matrix (Fin k) (Fin k) LL) (hM : Continuous M) :
    GRep G Qp LL O where
  V := Fin k → LL
  ρ := matRep M
  cont x := by
    change Continuous fun g => (M g).mulVec x
    exact hM.matrix_mulVec continuous_const

section

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]

theorem isDual1_of_eq {k : ℕ} (M U : G →* Matrix (Fin k) (Fin k) LL)
    (hU : ∀ g, U g = ((cycLL PD LL g : LLˣ) : LL) • (M g⁻¹).transpose) :
    IsDual1 PD (matRep M) (matRep U) (dotProductBilin LL LL) := by
  refine ⟨fun g x y => ?_, fun x hx => ?_, fun y hy => ?_, rfl⟩
  · change (M g).mulVec x ⬝ᵥ ((U g).mulVec y) = ((cycLL PD LL g : LLˣ) : LL) * (x ⬝ᵥ y)
    rw [hU, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Matrix.mulVec_transpose,
      dotProduct_comm, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← map_mul,
      inv_mul_cancel, map_one, Matrix.one_mulVec, dotProduct_comm]
  · funext i
    have := hx (Pi.single i 1)
    simpa using this
  · funext i
    have := hy (Pi.single i 1)
    simpa using this

end

section

variable (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
  (hw : w ∈ placesOver D.host.E (D.nd.l i))

theorem continuous_loc {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (hM : Continuous fun g => M g) : Continuous (Br.loc D.nbr i w hw M) := by
  have hfc : Continuous (D.nbr i w hw).toLL :=
    continuous_subtype_val.comp (D.nbr i w hw).eO_cont
  have hι : Continuous fun g : Br.G D.nbr i w hw => ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd) :=
    continuous_subtype_val.comp (Br.iota_cont D.nbr i w hw)
  exact (hM.comp hι).matrix_map hfc

theorem isDual1_loc (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (x : D.nd.X i) :
    IsDual1 ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw) (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r x)))
      (matRep (Br.loc D.nbr i w hw (rDuO D.nd i r x))) (dotProductBilin _ _) := by
  refine isDual1_of_eq _ _ _ fun g => ?_
  let ι : Br.G D.nbr i w hw →* GE D.nd := (decS D.nd w).comp (Br.iota D.nbr i w hw)
  let f := (D.nbr i w hw).toLL
  have e : f (epsU D.nd i (ι g) : (D.nd.O i)ˣ) =
      ((cycLL ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw) ↥(D.nbr i w hw).LL.1 g :
        (↥(D.nbr i w hw).LL.1)ˣ) : ↥(D.nbr i w hw).LL.1) :=
    congrArg Units.val (GlobalTheory.CycBridge.locChi_epsU D i w hw g)
  rw [← e]
  ext a b
  congr 1
  change f ((((D.nd.chi i 1 (ι g)) * epsU D.nd i (ι g) : (D.nd.O i)ˣ) : D.nd.O i) *
      rO D.nd i r x ((ι g)⁻¹ : GE D.nd) b a) = f (epsU D.nd i (ι g) : (D.nd.O i)ˣ) *
    f ((((D.nd.chi i 1 (ι g⁻¹))⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) * rO D.nd i r x (ι g⁻¹) b a)
  rw [← map_mul, map_inv ι g, map_inv (D.nd.chi i 1), inv_inv, Units.val_mul]
  congr 1
  ring

end

set_option maxHeartbeats 1600000 in

theorem stepPotDual : StepPotDual := by
  classical
  intro D hT i r hr Xs w hw n ⟨K', h, hN, hF, hS, Sig, Fr, hFr, hst, h1, hc, hx⟩
  refine ⟨K', h, hN, hF, hS, Sig.image (fun a => a⁻¹), Fr, hFr, ?_, ?_,
    le_trans Finset.card_image_le hc, fun x => ?_⟩
  · intro a ha
    obtain ⟨a, ha', rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨b, hb, hab⟩ := hst a ha'
    refine ⟨b⁻¹, Finset.mem_image.2 ⟨b, hb, rfl⟩, fun g g' hg => ?_⟩
    rw [MonoidHom.inv_apply, MonoidHom.inv_apply, hab g g' hg]
  · exact Finset.mem_image.2 ⟨1, h1, inv_one⟩
  · have hcont := GlobalTheory.Pass.FamCont.stepCont D i r hr x
    exact (hT (D.nd.l i) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL h hN hF hS
      (bundle _ _ (Br.loc D.nbr i w hw (rTwO D.nd i r x)) (continuous_loc D i w hw _ hcont.1))
      (bundle _ _ (Br.loc D.nbr i w hw (rDuO D.nd i r x)) (continuous_loc D i w hw _ hcont.2))
      Sig (Sig.image (fun a => a⁻¹)) (hx x).1 (hx x).2).2 (dotProductBilin _ _)
      (isDual1_loc D i w hw r x)
      (fun b => by
        rw [Finset.mem_image]
        exact ⟨fun ⟨a, ha, e⟩ => ⟨a, ha, e.symm⟩, fun ⟨a, ha, e⟩ => ⟨a, ha, e.symm⟩⟩)

end GlobalTheory.PotDual

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousWittCbInclusionSmulWeakTopologyStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_wittCbInclusion_smul_weakTopology : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l} {s : ℕ} {LL : FinExt l} {h : Good K s LL} {W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))} (E : EtSit P AI K s LL h W) (T : Lt K LL) {d e : ℕ} (b : LatB T d) (bO : Module.Basis (Fin e) ℤ_[l] ↥(OL LL)) (y : TW (RW LL) T), letI := twTop T b; letI := aTop (K := K) bO; Continuous fun a : AA K LL => inclR LL (E.tie.io a) • y := by
  first | exact @GlobalTheory.WeakClosed.continuous_inclR_io_smul | exact GlobalTheory.WeakClosed.continuous_inclR_io_smul | (intros; apply GlobalTheory.WeakClosed.continuous_inclR_io_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CupCoboundaryStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.Published.PoitouTate GlobalTheory.ResSel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cup_coboundary_alt : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → ∀ ρ, IsDual i s ρ → ∀ (v : PlE D.host) (hv : v ∈ placesOver D.host.E (X.l i)) (c c' : ↥(Loc.GK (bkP.br i v hv).Kw) → Fin D.R.r → ↥(bkP.br i v hv).LL.1) (y y' : ↥(DecV N v) → Fin D.R.r → X.O0 i), c ∈ Formalism.WeaklyAdmissibleFiltrations.finiteCocycles (PDv bkP i v hv) (repV bkP i v hv (Tgl i s)) → c' ∈ Formalism.WeaklyAdmissibleFiltrations.finiteCocycles (PDv bkP i v hv) (repV bkP i v hv ρ) → (∀ g a, c ((bkP.br i v hv).e g) a = (bkP.br i v hv).toLL (y g a)) → (∀ g a, c' ((bkP.br i v hv).e g) a = (bkP.br i v hv).toLL (y' g a)) → ∃ f : ↥(DecV N v) → ↥(bkP.br i v hv).LL.1, Continuous f ∧ ∀ g h : ↥(DecV N v), (bkP.br i v hv).toLL (y g ⬝ᵥ ((ρ g : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).mulVec (y' h)) = (bkP.br i v hv).toLL (algebraMap ℤ_[X.l i] (X.O0 i) ((cycZ D.host.E N.Om (X.l i) g : ℤ_[X.l i]ˣ) : ℤ_[X.l i])) * f h - f (g * h) + f g := by
  first | exact @GlobalTheory.BKCup.cup_coboundary | exact GlobalTheory.BKCup.cup_coboundary | (intros; apply GlobalTheory.BKCup.cup_coboundary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CupDivisibleImageCoboundaryIffFiniteLevel
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.BKFinLevel.NatCup

section Lifts

variable {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  {ρ : Representation LL G V}

theorem liftQ_mem_lat (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (x : ↥L.T ⧸ I) :
    Formalism.MainNotions.LocalSituation.liftQ L I x ∈ L.T :=
  (Submodule.Quotient.mk_surjective I x).choose.2

theorem mk_liftQ_lat (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (x : ↥L.T ⧸ I) :
    (Submodule.Quotient.mk ⟨Formalism.MainNotions.LocalSituation.liftQ L I x, liftQ_mem_lat L I x⟩ : ↥L.T ⧸ I) = x :=
  (Submodule.Quotient.mk_surjective I x).choose_spec

theorem mk_liftD_lat (L : Lattice (O := O) ρ) (c : V ⧸ L.T) :
    (Submodule.Quotient.mk (liftD L c) : V ⧸ L.T) = c :=
  (Submodule.Quotient.mk_surjective L.T c).choose_spec

theorem mem_span_pow_smul_top (L : Lattice (O := O) ρ) (a : O) (x : ↥L.T) :
    x ∈ (Ideal.span {a} • ⊤ : Submodule O ↥L.T) ↔ ∃ y : ↥L.T, x = a • y := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, -, rfl⟩; exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩; exact ⟨y, Submodule.mem_top, rfl⟩

theorem inv_pow_mul_pow_mem (ϖ : O) (r : ℕ) :
    ∃ e : O, (algebraMap O LL ϖ)⁻¹ ^ r * (algebraMap O LL ϖ) ^ r = algebraMap O LL e := by
  rcases eq_or_ne (algebraMap O LL ϖ) 0 with h0 | h0
  · rcases Nat.eq_zero_or_pos r with hr | hr
    · exact ⟨1, by simp [hr]⟩
    · exact ⟨0, by simp [h0, zero_pow hr.ne']⟩
  · exact ⟨1, by rw [← mul_pow, inv_mul_cancel₀ h0, one_pow, map_one]⟩

theorem pair_shift {V' : Type} [AddCommGroup V'] [Module LL V'] (m : V →ₗ[LL] V' →ₗ[LL] LL)
    (f : V' →ₗ[LL] V') (a t â : V) (w y : V') (c π k u v : LL) (hâ : â = a + π • t)
    (hk : c * π = k) (hu : m a (f (w - c • y)) = u) (hv : m t (f y) = v) :
    u - k * v = m a (f w) - c * m â (f y) := by
  subst hâ hk hu hv
  simp only [map_sub, map_add, map_smul, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul]
  ring

end Lifts

end GlobalTheory.BKFinLevel.NatCup

namespace GlobalTheory.BKFinLevel

open GlobalTheory.BKFinLevel.NatCup in

theorem cobO_cupLD_ioL_iff : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∀ (ϖ : O) (r : ℕ) (d : ↥(latticeCocycles LA)) (c' : ↥(GK K) → ↥LA'.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA'.T)), CobO (P.PD K) L1 (cupLD LA' m (d : ↥(GK K) → A.V) (fun g => GlobalTheory.BKFinLevel.ioL LA' ϖ r (c' g))) ↔ CobO (P.PD K) L1 (GlobalTheory.BKFinLevel.cupQ LA LA' m ϖ r (redT LA _ d) c') := by
  intro l _ P K LL _ _ _ O _ _ _ L1 hL1 A A' LA LA' m hd ϖ r d c'
  have key : ∀ x, (Submodule.Quotient.mk (cupLD LA' m (d : ↥(GK K) → A.V)
      (fun g => ioL LA' ϖ r (c' g)) x) : LL ⧸ L1.T) =
      Submodule.Quotient.mk (cupQ LA LA' m ϖ r (redT LA _ d) c' x) := by
    rintro ⟨g, h⟩
    rw [Submodule.Quotient.eq, hL1]
    obtain ⟨e, he⟩ := inv_pow_mul_pow_mem (LL := LL) ϖ r

    have hyT := liftQ_mem_lat LA' _ (c' h)
    have hw : liftD LA' (ioL LA' ϖ r (c' h)) -
        (algebraMap O LL ϖ)⁻¹ ^ r • Formalism.MainNotions.LocalSituation.liftQ LA' _ (c' h) ∈ LA'.T := by
      have h2 : ioL LA' ϖ r (c' h) = Submodule.Quotient.mk
          ((algebraMap O LL ϖ)⁻¹ ^ r • Formalism.MainNotions.LocalSituation.liftQ LA' _ (c' h)) := by
        conv_lhs => rw [← mk_liftQ_lat LA' _ (c' h)]
        rfl
      exact (Submodule.Quotient.eq _).1 ((mk_liftD_lat LA' _).trans h2)

    have haT : (d : ↥(GK K) → A.V) g ∈ LA.T := d.2.2 g (Set.mem_univ g)
    have hred : (Submodule.Quotient.mk ⟨Formalism.MainNotions.LocalSituation.liftQ LA _ (redT LA _ d g),
        liftQ_mem_lat LA _ _⟩ : ↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) =
        Submodule.Quotient.mk ⟨(d : ↥(GK K) → A.V) g, haT⟩ := mk_liftQ_lat LA _ _
    obtain ⟨t, ht⟩ := (mem_span_pow_smul_top LA _ _).1 ((Submodule.Quotient.eq _).1 hred)
    have ht' : Formalism.MainNotions.LocalSituation.liftQ LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T) (redT LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T) d g) =
        (d : ↥(GK K) → A.V) g + (algebraMap O LL ϖ) ^ r • (t : A.V) := by
      have := congrArg (fun z : ↥LA.T => (z : A.V)) ht
      simp only [Submodule.coe_sub, Submodule.coe_smul] at this
      have hs : (algebraMap O LL ϖ) ^ r • (t : A.V) = ϖ ^ r • (t : A.V) := by
        rw [← map_pow, algebraMap_smul]
      rw [hs]
      exact (sub_eq_iff_eq_add').1 this
    have hw2 : A'.ρ g (liftD LA' (ioL LA' ϖ r (c' h)) - (algebraMap O LL ϖ)⁻¹ ^ r • Formalism.MainNotions.LocalSituation.liftQ LA' (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA'.T) (c' h)) ∈ LA'.T := LA'.stable g _ hw
    have hy2 : A'.ρ g (Formalism.MainNotions.LocalSituation.liftQ LA' (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA'.T) (c' h)) ∈ LA'.T := LA'.stable g _ hyT
    have hb1' : ∃ b : O, m ((d : ↥(GK K) → A.V) g) (A'.ρ g (liftD LA' (ioL LA' ϖ r (c' h)) - (algebraMap O LL ϖ)⁻¹ ^ r • Formalism.MainNotions.LocalSituation.liftQ LA' (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA'.T) (c' h))) = algebraMap O LL b := (hd.2 _).1 hw2 _ haT
    have hb2' : ∃ b : O, m (t : A.V) (A'.ρ g (Formalism.MainNotions.LocalSituation.liftQ LA' (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA'.T) (c' h))) = algebraMap O LL b := (hd.2 _).1 hy2 _ t.2
    obtain ⟨b1, hb1⟩ := hb1'
    obtain ⟨b2, hb2⟩ := hb2'
    refine ⟨b1 - e * b2, ?_⟩
    show algebraMap O LL (b1 - e * b2) =
      m ((d : ↥(GK K) → A.V) g) (A'.ρ g (liftD LA' (ioL LA' ϖ r (c' h)))) -
        (algebraMap O LL ϖ)⁻¹ ^ r * m (Formalism.MainNotions.LocalSituation.liftQ LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T) (redT LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T) d g))
          (A'.ρ g (Formalism.MainNotions.LocalSituation.liftQ LA' _ (c' h)))
    have hsplit : algebraMap O LL (b1 - e * b2) =
        algebraMap O LL b1 - algebraMap O LL e * algebraMap O LL b2 := by
      rw [map_sub, map_mul]
    exact hsplit.trans (pair_shift m (A'.ρ g) _ _ _ _ _ _ _ _ _ _ ht' he hb1 hb2)
  unfold CobO
  exact Iff.of_eq (congrArg (fun z => z ∈ ReciprocityTheory.Def.B2 (repD L1) ⊤) (funext key))

end GlobalTheory.BKFinLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamIffFramedGaloisRepresentationStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRham_iff_framed_galois_representation : FrameEx := by
  first | exact @GlobalTheory.PMon.FrameEquiv.frameEx | exact GlobalTheory.PMon.FrameEquiv.frameEx | (intros; apply GlobalTheory.PMon.FrameEquiv.frameEx <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompositionGroupEquivLocalGaloisGroupStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.decomposition_group_equiv_local_galois_group : ReciprocityTheory.ChartRestriction.T2.DecEquiv := by
  first | exact @GlobalTheory.DecLocal.decEquiv | exact GlobalTheory.DecLocal.decEquiv | (intros; apply GlobalTheory.DecLocal.decEquiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeltaAddSubMemPow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem delta_add_sub_mem_pow : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A)
    (J : Ideal A), (l : A) ∈ J → ∀ (n : ℕ) (x : A), ∀ y ∈ J ^ (n + 1), D.δ (x + y) - D.δ x ∈ J ^ n := by
  intro l _ A _ D J hl n x y hy
  have hy' : y ∈ J ^ n := Ideal.pow_le_pow_right (Nat.le_succ n) hy
  have hδ : D.δ y ∈ J ^ n := GlobalTheory.T.delta_mem_ideal_pow_of_mem_pow_succ l A D J hl n y hy
  rw [D.δ_add x y]
  have e : D.δ x + D.δ y - ∑ k ∈ Finset.Ioo 0 l, ((l.choose k / l : ℕ) : A) * x ^ k * y ^ (l - k) - D.δ x
      = D.δ y - ∑ k ∈ Finset.Ioo 0 l, ((l.choose k / l : ℕ) : A) * x ^ k * y ^ (l - k) := by ring
  rw [e]
  refine Ideal.sub_mem _ hδ (Ideal.sum_mem _ fun k hk => ?_)
  have hk' : 0 < l - k := Nat.sub_pos_of_lt (Finset.mem_Ioo.1 hk).2
  have : y ^ (l - k) ∈ J ^ n := by
    obtain ⟨m, hm⟩ : ∃ m, l - k = m + 1 := ⟨l - k - 1, by omega⟩
    rw [hm, pow_succ]
    exact Ideal.mul_mem_left _ _ hy'
  exact Ideal.mul_mem_left _ _ this

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DepthZeroAdmissibleAllPendingDataStatement
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depthZeroAdmissible_all_pending_data : ∀ (D : D7) (P : PairedCharacterCondition.Pend D), PairedCharacterCondition.RT.AdmDepthZeroTypes (D := D) → PairedCharacterCondition.admDZ P := by
  first | exact @GlobalTheory.AdmDepthZero.main | exact GlobalTheory.AdmDepthZero.main | (intros; apply GlobalTheory.AdmDepthZero.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DescEqXPowSmulNablaPow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal Matrix

namespace GlobalTheory.DescFalling

theorem desc_eq_X_pow_smul_nabla_pow {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    {P : PhiMod O K l e a ι} (C : Conn P) (k : ℕ) (v : Vec K a ι) :
    C.desc k v = (X : K⟦X⟧) ^ k • (C.nabla ^ k) v := by
  have hX : ∀ w, C.nabla ((X : K⟦X⟧) • w) = w + (X : K⟦X⟧) • C.nabla w := fun w => by
    have h := C.leibniz (fun _ => X) w
    have e1 : ∀ u : Vec K a ι, ((fun _ => (X : K⟦X⟧)) : ZMod a → K⟦X⟧) • u = (X : K⟦X⟧) • u :=
      fun u => rfl
    have e2 : ((fun _ => PowerSeries.derivative K (X : K⟦X⟧)) : ZMod a → K⟦X⟧) • w = w := by
      simp only [PowerSeries.derivative_X]
      exact one_smul _ w
    rw [e1, e1, e2] at h
    exact h
  have hcomm : ∀ (j : ℕ) (w : Vec K a ι),
      (C.nabla ^ j) ((X : K⟦X⟧) • C.nabla w) = (X : K⟦X⟧) • (C.nabla ^ (j + 1)) w + j • (C.nabla ^ j) w := by
    intro j
    induction j with
    | zero => intro w; simp
    | succ j ih =>
      intro w
      rw [pow_succ', Module.End.mul_apply, ih, map_add, hX, map_nsmul, pow_succ' C.nabla (j + 1),
        Module.End.mul_apply, pow_succ' C.nabla j, Module.End.mul_apply, succ_nsmul]
      abel
  induction k generalizing v with
  | zero => simp [Conn.desc_zero]
  | succ k ih =>
    rw [Conn.desc_succ, ih, Conn.N_apply, map_sub, hcomm, map_nsmul, add_sub_cancel_right, smul_smul,
      ← pow_succ]

end GlobalTheory.DescFalling
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DescNEqXPowMulIterateDerivative
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal Matrix

namespace GlobalTheory.BKReal

theorem coeff_iterate_derivative_descFactorial (K : Type) [NormedField K] (p : ℕ) (f : K⟦X⟧) (m : ℕ) :
    coeff m ((⇑(derivative K))^[p] f) = ((m + p).descFactorial p : K) * coeff (m + p) f := by
  induction p generalizing m with
  | zero => simp
  | succ p ih =>
    rw [Function.iterate_succ_apply', coeff_derivative, ih, Nat.descFactorial_succ,
      show m + 1 + p = m + (p + 1) by omega, show m + (p + 1) - p = m + 1 by omega]
    push_cast
    ring

theorem descN_eq_X_pow_mul_iterate_derivative :
    ∀ (K : Type) [NormedField K] (p : ℕ) (f : K⟦X⟧), descN K p f = X ^ p * (⇑(derivative K))^[p] f := by
  intro K _ p f
  ext n
  rw [coeff_descN, coeff_X_pow_mul']
  split_ifs with h
  · rw [coeff_iterate_derivative_descFactorial, Nat.sub_add_cancel h]
  · rw [Nat.descFactorial_of_lt (by omega), Nat.cast_zero, zero_mul]

end GlobalTheory.BKReal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DescentFreeModuleCocycle
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open CategoryTheory

namespace GlobalTheory

theorem descent_free_cocycle : ∀ (A B D T : Type) [CommRing A] [CommRing B] [CommRing D] [CommRing T] [Algebra A B] (p q : B →+* D) (q₁₂ q₂₃ q₁₃ : D →+* T) (q₃ : B →+* T), (algebraMap A B).FaithfullyFlat → CategoryTheory.IsPushout (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom p) (CommRingCat.ofHom q) → CategoryTheory.IsPushout (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom (p.comp (algebraMap A B))) (CommRingCat.ofHom q₃) (CommRingCat.ofHom q₁₂) → q₂₃.comp p = q₁₂.comp q → q₂₃.comp q = q₃ → q₁₃.comp p = q₁₂.comp p → q₁₃.comp q = q₃ → ∀ (d : ℕ) (ε : Matrix (Fin d) (Fin d) D), IsUnit ε → ε.map q₁₂ * ε.map q₂₃ = ε.map q₁₃ → ∀ N : Submodule A (Fin d → B), (∀ z, z ∈ N ↔ (fun i => p (z i)) = ε.mulVec fun i => q (z i)) → Module.Finite A ↥N ∧ Module.Projective A ↥N ∧ IsBaseChange B N.subtype := by
  intro A B D T _ _ _ _ _ p q q₁₂ q₂₃ q₁₃ q₃ hff hD hT h1 h2 h3 h4 d ε hε hcoc N hN
  haveI : Module.FaithfullyFlat A B := RingHom.faithfullyFlat_algebraMap_iff.1 hff
  have hTP := CommRingCat.isPushout_tensorProduct A B B
  let iso := hD.isoIsPushout _ _ hTP
  let e : D ≃+* B ⊗[A] B := iso.commRingCatIsoToRingEquiv
  let ψ : D →+* B ⊗[A] B := e.toRingHom
  have hψp : ∀ b, ψ (p b) = b ⊗ₜ[A] (1 : B) := fun b =>
    congr($(hD.inl_isoIsPushout_hom _ _ hTP).hom b)
  have hψq : ∀ b, ψ (q b) = (1 : B) ⊗ₜ[A] b := fun b =>
    congr($(hD.inr_isoIsPushout_hom _ _ hTP).hom b)
  let L : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B) :=
    Algebra.TensorProduct.map (AlgHom.id A B) (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B)
  let R : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B) :=
    (Algebra.TensorProduct.includeRight : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B))
  let M : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B) :=
    Algebra.TensorProduct.map (AlgHom.id A B) (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B)
  let c3 : B →+* B ⊗[A] (B ⊗[A] B) :=
    (R.comp (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B)).toRingHom
  have w : CommRingCat.ofHom (algebraMap A B) ≫ CommRingCat.ofHom c3 =
      CommRingCat.ofHom (p.comp (algebraMap A B)) ≫
        CommRingCat.ofHom (S := B ⊗[A] (B ⊗[A] B)) (L.toRingHom.comp ψ) := by
    ext a
    change c3 (algebraMap A B a) = L (ψ (p (algebraMap A B a)))
    rw [hψp]
    exact ((R.comp Algebra.TensorProduct.includeRight).commutes a).trans
      ((L.comp (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B)).commutes a).symm
  let Φ := hT.desc _ _ w
  let φ : T →+* B ⊗[A] (B ⊗[A] B) := Φ.hom
  have hφ3 : ∀ b, φ (q₃ b) = c3 b := fun b => congr($(hT.inl_desc _ _ w).hom b)
  have hφ12 : ∀ x, φ (q₁₂ x) = L (ψ x) := fun x => congr($(hT.inr_desc _ _ w).hom x)
  have hext : ∀ {W : CommRingCat} (f g : CommRingCat.of D ⟶ W), (∀ b, f (p b) = g (p b)) →
      (∀ b, f (q b) = g (q b)) → f = g := fun f g hp hq =>
    hD.hom_ext (by ext b; exact hp b) (by ext b; exact hq b)
  have hφ23 : ∀ x, φ (q₂₃ x) = R (ψ x) := by
    have key := hext (CommRingCat.ofHom q₂₃ ≫ Φ)
      (CommRingCat.ofHom (S := B ⊗[A] (B ⊗[A] B)) (R.toRingHom.comp ψ)) ?_ ?_
    · intro x; exact congr($(key).hom x)
    · intro b
      change φ (q₂₃ (p b)) = R (ψ (p b))
      rw [show q₂₃ (p b) = q₁₂ (q b) from congr($h1 b), hφ12, hψq, hψp]
      simp [L, R]
    · intro b
      change φ (q₂₃ (q b)) = R (ψ (q b))
      rw [show q₂₃ (q b) = q₃ b from congr($h2 b), hφ3, hψq]
      simp [c3, R]
  have hφ13 : ∀ x, φ (q₁₃ x) = M (ψ x) := by
    have key := hext (CommRingCat.ofHom q₁₃ ≫ Φ)
      (CommRingCat.ofHom (S := B ⊗[A] (B ⊗[A] B)) (M.toRingHom.comp ψ)) ?_ ?_
    · intro x; exact congr($(key).hom x)
    · intro b
      change φ (q₁₃ (p b)) = M (ψ (p b))
      rw [show q₁₃ (p b) = q₁₂ (p b) from congr($h3 b), hφ12, hψp]
      simp [L, M]
    · intro b
      change φ (q₁₃ (q b)) = M (ψ (q b))
      rw [show q₁₃ (q b) = q₃ b from congr($h4 b), hφ3, hψq]
      simp [c3, R, M]
  let ε' : Matrix (Fin d) (Fin d) (B ⊗[A] B) := ε.map ψ
  have hε' : IsUnit ε' := hε.map ψ.mapMatrix
  have hcoc' : ε'.map L * ε'.map R = ε'.map M := by
    have key := congrArg φ.mapMatrix hcoc
    rw [map_mul] at key
    have e12 : φ.mapMatrix (ε.map q₁₂) = ε'.map L := by
      ext i j; simp [ε', hφ12]
    have e23 : φ.mapMatrix (ε.map q₂₃) = ε'.map R := by
      ext i j; simp [ε', hφ23]
    have e13 : φ.mapMatrix (ε.map q₁₃) = ε'.map M := by
      ext i j; simp [ε', hφ13]
    rw [e12, e23, e13] at key
    exact key
  have hN' : ∀ z, z ∈ N ↔ (fun i => z i ⊗ₜ[A] (1 : B)) = ε'.mulVec fun i => (1 : B) ⊗ₜ[A] z i := by
    intro z
    rw [hN z]
    have hv : (ψ ∘ fun i => q (z i)) = fun i => (1 : B) ⊗ₜ[A] z i := funext fun k => hψq _
    have hmv : ∀ i, ψ ((ε.mulVec fun i => q (z i)) i) = (ε'.mulVec fun i => (1 : B) ⊗ₜ[A] z i) i := by
      intro i; rw [RingHom.map_mulVec, hv]
    constructor
    · intro h; funext i
      rw [← hmv i, ← h, hψp]
    · intro h; funext i
      apply e.injective
      change ψ (p (z i)) = ψ _
      rw [hmv i, hψp]
      exact congrFun h i
  exact GlobalTheory.T.faithfullyFlat_descent_free_module_cocycle A B d ε' hε' hcoc' N hN'

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DirectSumDeRhamCrystallineJumpsAddStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.directSum_deRham_crystalline_jumps_add : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (V₁ : Type) [AddCommGroup V₁] [Module ↥LL.1 V₁] [Module ℚ_[l] V₁] [IsScalarTower ℚ_[l] ↥LL.1 V₁] [FiniteDimensional ↥LL.1 V₁] (ρ₁ : Representation ↥LL.1 ↥(GK K) V₁) (V₂ : Type) [AddCommGroup V₂] [Module ↥LL.1 V₂] [Module ℚ_[l] V₂] [IsScalarTower ℚ_[l] ↥LL.1 V₂] [FiniteDimensional ↥LL.1 V₂] (ρ₂ : Representation ↥LL.1 ↥(GK K) V₂) (e : V ≃ₗ[↥LL.1] (V₁ × V₂)), (∀ g v, e (ρ g v) = (ρ₁ g (e v).1, ρ₂ g (e v).2)) → (IsDR (P.PD K) ρ ↔ IsDR (P.PD K) ρ₁ ∧ IsDR (P.PD K) ρ₂) ∧ (IsCrys (P.PD K) ρ ↔ IsCrys (P.PD K) ρ₁ ∧ IsCrys (P.PD K) ρ₂) ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), multV (P.PD K) ρ τ a = multV (P.PD K) ρ₁ τ a + multV (P.PD K) ρ₂ τ a := by
  first | exact @GlobalTheory.Per.DirectSumHT.directSum_hodgeTate | exact GlobalTheory.Per.DirectSumHT.directSum_hodgeTate | (intros; apply GlobalTheory.Per.DirectSumHT.directSum_hodgeTate <;> assumption)
end

