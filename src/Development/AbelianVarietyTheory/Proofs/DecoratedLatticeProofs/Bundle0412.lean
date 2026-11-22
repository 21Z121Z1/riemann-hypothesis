import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0033
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0359
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0466
import Formalism.LocalToGlobal.Columns.CoefModB
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0391
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0003
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0349
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentSubMulComplementEqComplement
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0275
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0270
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0437
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteAdeleIdempotentOfFMulSelf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0347
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0342
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0390
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0267
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0052
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProjectionMovesTypeVectorsModLevel
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0363
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0055
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0386
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0383
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0396
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0382
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0392
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0358

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReadingVectorFixedByClassStabiliserCharacter
section
noncomputable section

namespace GlobalTheory.AdForm.StabInv

section Pair
open Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.ColAd Matrix

variable {ι : Type} [Fintype ι] {n : ℕ}

theorem lT_fnOf (G : ι → Matrix (Fin n) (Fin n) ℂ) (lam : ι → DomWeight n) (u : ι → GL (Fin n) ℂ) (P : Pol ℂ ι n) :
    lT G u (fnOf G (shiftOf lam) 1 P) = fnOf G (shiftOf lam) 1 (rhoP lam (invTrK u⁻¹) P) := by
  funext y
  have e1 : ∀ τ, ((invTrK u⁻¹ τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ = (u τ : Matrix (Fin n) (Fin n) ℂ) := fun τ => by
    rw [invTrK_coe, Matrix.transpose_transpose, Pi.inv_apply, inv_inv]
  simp only [lT_apply, fnOf, LinearMap.coe_mk, AddHom.coe_mk, Pi.one_apply, Matrix.one_mul, frL, rhoP, MonoidHom.coe_mk,
    OneHom.coe_mk, actP, trAct, detTwK, LinearMap.smul_apply, AlgHom.toLinearMap_apply, smul_eq_mul, MvPolynomial.smul_eval,
    Formalism.GradedWeylDivisibility.blockAct, eval_aeval_poly, e1, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  have e2 : ∀ τ, detPow ℂ n (invTrK u⁻¹ τ) (lam τ).detShift = (u τ : Matrix (Fin n) (Fin n) ℂ).det ^ (lam τ).detShift :=
    fun τ => by rw [detPow, Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply, ← Matrix.det_transpose, e1]
  simp only [e2, Matrix.det_mul, mul_zpow, Finset.prod_mul_distrib, shiftOf, Matrix.mul_apply]
  ring

theorem eq_smul_of_pair (G G' : ι → Matrix (Fin n) (Fin n) ℂ) (lam lam' : ι → DomWeight n) (hl : lam = lam') (o : Frames G')
    (ho : ∀ τ, o.1 τ = 1) (k k' : ι → GL (Fin n) ℂ) (hk : k = k') {w : Pol ℂ ι n} (hw : w ∈ VV ℂ lam) (c : ℂ)
    (h : ∀ φ ∈ ValC G lam', ∃ φ' : Frames G → ℂ, lT G k φ' = φ ∧
      pairB lam (polOf G' (shiftOf lam) o φ') w = c * pairB lam (polOf G' (shiftOf lam) o φ) w) :
    w = c • rhoP lam k' w := by
  subst hl hk
  have hp : ∀ P, polOf G' (shiftOf lam) o (fnOf G (shiftOf lam) 1 P) = P := fun P => by
    have e : (fun τ => (o.1 τ)⁻¹) = 1 := funext fun τ => by rw [ho τ]; exact inv_one
    have := polOf_fnOf G' (shiftOf lam) o P
    rw [e] at this
    exact this
  have hm : w - c • rhoP lam k w ∈ VV ℂ lam := sub_mem hw (Submodule.smul_mem _ _ (polyAction_mem_VV lam k hw))
  have h0 := (pairingBNondegenerate_holds ℂ ι n lam).2 ⟨_, hm⟩ fun P => by
    obtain ⟨φ', e1, e2⟩ := h (lT G k (fnOf G (shiftOf lam) 1 P.1))
      (lT_mem G lam k ⟨P.1, by simpa [MvPolynomial.map_id] using map_mem_CSpan (RingHom.id ℂ) lam _ P.2, rfl⟩)
    have e3 : φ' = fnOf G (shiftOf lam) 1 P.1 := by
      have := congrArg (lT G k⁻¹) e1
      rwa [← lT_mul, ← lT_mul, mul_inv_cancel, lT_one, lT_one] at this
    rw [e3, lT_fnOf, hp, hp] at e2
    have e4 := pairingBInvariantK_holds ℂ ι n lam k⁻¹ P.1 (rhoP lam k w)
    have e5 : actP lam k⁻¹ (rhoP lam k w) = w := by
      show (rhoP lam k⁻¹ * rhoP lam k) w = w
      rw [← map_mul, inv_mul_cancel, map_one]; rfl
    rw [e5] at e4
    rw [pairBK_apply]
    show pairB lam P.1 (w - c • rhoP lam k w) = 0
    rw [map_sub, map_smul, e2, ← e4, smul_eq_mul]
    exact sub_self _
  exact sub_eq_zero.1 (congrArg Subtype.val h0)

end Pair

section Law
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
  Formalism.L2.Forms GlobalTheory.Core.Rk GlobalTheory.Core.Rk.Top GlobalTheory.Core.Rk.TopOnto
open GlobalTheory.Mem.ColAd GlobalTheory.Core.Rk.TopLift GlobalTheory.Core.Rk.Top.Model GlobalTheory.PointAtPlaceHom Formalism.MainNotions.StandardLattice Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {u : D.what₂.Word} {θ : InfFam D} {S : D.what₂.Tau → SPar} {M : DSModel D.sp.X' S}
  {j : SmT M →ₗ[ℂ] (FrP D → ℂ)} {J : Set (GA D D.sp.X')} {χ : GA D D.sp.X' → ℂ}

set_option maxHeartbeats 1000000 in

theorem coset_law_moved (hθ : IsInfFam θ) (hj : IsJ u M j) {b : GA D D.sp.X'} (hb : b ∈ GfC D.sp.X') {γ : GA D D.sp.X'}
    (hγ : γ ∈ GQ D.sp.X') {k h h' : GA D D.sp.X'} {κ x x'} (hk : HasMat k κ) (hJ : b⁻¹ * k * b ∈ J) (hh : HasMat h x)
    (hh' : HasMat h' x') (e : x' = (finPt γ).1 * x * κ) (v : SmT M) :
    ∃ v' : SmT M, lT _ (infPt θ γ) (j v') = j v ∧
      ∀ T ∈ MultT θ M J χ, T v' (h' * b) = χ (b⁻¹ * k * b) * T v (h * b) := by
  have R := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ D.sp.X'
  obtain ⟨f, hf, a, ha, rfl⟩ := R.2.2.2.2.2.2.1 γ
  obtain ⟨v', e1, e2⟩ := real_translate (J := J) (χ := χ) hθ hj a ha v
  have e3 : h' = f * h * k := by
    refine hasMat_pt hh' ?_
    have := hasMat_finPt (mul_mem (mul_mem hf hh.1) hk.1)
    rwa [finPt_mul, finPt_mul, finPt_of_hasMat hh, finPt_of_hasMat hk, ← finPt_mul_inf f ha, ← e] at this
  refine ⟨v', by rw [map_mul (infPt θ), infPt_of_fin θ hf, one_mul, e1], fun T hT => ?_⟩
  have e4 : h' * b * a = f * a * (h * b * (b⁻¹ * k * b)) := by
    have e5 : h * b * (b⁻¹ * k * b) = h * k * b := by group
    rw [e5, e3, mul_assoc f a, comm_of_mem _ ha (mul_mem (mul_mem hh.1 hk.1) hb)]
    simp only [mul_assoc]
  rw [e2 T hT, e4, multT_rel' (h * b * (b⁻¹ * k * b)) (f * a * (h * b * (b⁻¹ * k * b))) 1 (fun m hm w => by
    rw [one_mul]; exact (hm.aut w).left _ hγ _) hT, one_mul,
    multT_rel' (h * b) (h * b * (b⁻¹ * k * b)) (χ (b⁻¹ * k * b)) (fun m hm w => hm.lev w _ hJ (h * b)) hT]

end Law

section Chi
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2
  GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem chi_eq_chr {B : Base} {X : PreX B.toPre} (I : TC B X) (a : I.ι) {Lb U chi y lat st} (hR : I.ReadsP a Lb U chi y lat st)
    (c : (I.stX a).Cl) (s : (I.stX a).Stab c) (κ : U)
    (e' : y c = bc (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F)) ((I.stX a).gam c.1 s.1) * y c * κ.1) :
    ((chi κ : ℂˣ) : ℂ) = B.embLL (((I.stX a).chr c.1 s.1 : B.LLˣ) : B.LL) := by
  let κ0 : (I.stX a).G c.1 := (1, s.1.2.1, s.1.2.2)
  have hgam : (I.stX a).gam c.1 κ0 = 1 := map_one (ufGL B.fields.E (B.R.N B.R.m - 1))
  have hp := GlobalTheory.Mem.Col2.TilX.isPtOf_rat (hR.pt c) (s.1.1)⁻¹
  have hact : ((I.stX a).act c.1 κ0 ((I.stX a).rep c)).1.1 = (((s.1.1)⁻¹, 1, 1) : UF B.fields.E (B.R.N B.R.m - 1) ×
      GLG B.fields.E (B.R.N B.R.m - 1) (B.primes X).vGs × GLQ B.fields.E (B.R.N B.R.m - 1) (QE I.sel (I.tup a : Chr B.fields.F B.fields.E B.fields.K))) •
      ((I.stX a).rep c).1.1 := by
    have e1 : FrmG.incl _ _ s.1 • ((I.stX a).rep c).1.1 = ((I.stX a).rep c).1.1 :=
      congrArg (fun d : (I.stX a).D c.1 => d.1.1) s.2
    conv_rhs => rw [← e1]
    refine Eq.trans ?_ (smul_smul _ _ _).symm
    have e2 : FrmG.incl _ _ κ0 = (((s.1.1)⁻¹, 1, 1) : UF B.fields.E (B.R.N B.R.m - 1) ×
        GLG B.fields.E (B.R.N B.R.m - 1) (B.primes X).vGs × GLQ B.fields.E (B.R.N B.R.m - 1) (QE I.sel (I.tup a : Chr B.fields.F B.fields.E B.fields.K))) *
        FrmG.incl _ _ s.1 := by
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · exact (inv_mul_cancel _).symm
      · exact (one_mul _).symm
      · exact (one_mul _).symm
    exact congrArg (fun t => t • ((I.stX a).rep c).1.1) e2
  have hyk : y c * κ.1 = ratAd B.host.F (s.1.1)⁻¹ * y c := by
    have e3 : ratAd B.host.F (s.1.1)⁻¹ =
        (bc (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F)) ((I.stX a).gam c.1 s.1))⁻¹ := by
      unfold ratAd
      rw [map_inv, map_inv]
      rfl
    rw [e3]
    conv_rhs => rw [e']
    group
  have hq : PtOf (y c * κ.1) ((I.stX a).act c.1 κ0 ((I.stX a).rep c)).1.1 := by
    rw [hyk, hact]
    exact hp
  exact hR.chr c κ κ0 hgam hq

theorem sgT_eq {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) :
    (I.perIn u a).sgT = (Formalism.L2.Forms.sgT (D := I.rec7 l Z) u : B.fields.Tau → DomWeight (B.R.N B.R.m - 1)) := by
  funext τ
  obtain ⟨a, ha⟩ := B.R.t_odd
  have e1 : B.R.m * (B.R.t + 1) / 2 = B.R.m * (a + 1) := by
    rw [ha, show B.R.m * (2 * a + 1 + 1) = 2 * (B.R.m * (a + 1)) by ring]; omega
  have e2 : (B.R.t + 1) / 2 = a + 1 := by omega
  show GlobalTheory.Mem.Col2.shW (B.wts.sgW τ) (-((B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ))) =
    Formalism.L2.Forms.shW (B.wts.sgW τ) ((B.R.m * (B.R.t + 1) / 2 : ℕ) : ℤ)
  rw [e1, e2]
  unfold GlobalTheory.Mem.Col2.shW Formalism.L2.Forms.shW
  congr 1

theorem star_eq_inv {H K : Type} [Group H] [Finite H] [Field K] (φ : H →* Kˣ) (σ : K →+* ℂ) (s : H) :
    star (σ (φ s : K)) = (σ (φ s : K))⁻¹ := by
  have e : σ (φ s : K) ^ Nat.card H = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one, map_one]
  exact (Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one e Nat.card_pos.ne')).symm

end Chi

section Main
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.TopLift GlobalTheory.Core.Rk.TopOnto GlobalTheory.Core.Rk.Top.Model

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem reading_stab_inv : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ : ℕ → ℂ), PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (a : I.ι), ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → g.bT ∈ GfC _ → LevG K g.bT (levS _ R.βX (datXP R P t)) (levChi _ R.βX (datXP R P t)) → ∀ f : CXP R P t, ∀ (c : (I.stX a).Cl) (w : Formalism.L2.DIV.Pol ℂ (I.rec7 l Z).what₂.Tau (B.R.N B.R.m - 1)), w ∈ Formalism.L2.DIV.VV ℂ (I.perIn u a).sgT → (∀ v h, GlobalTheory.Core.Rk.Top.HasMat h (K.y c).1 → f.1 v (h * g.bT) = Formalism.L2.DIV.pairB (I.perIn u a).sgT (Formalism.L2.Col.polOf (GlobalTheory.Mem.Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m - 1)) (Formalism.L2.Forms.shiftOf (I.perIn u a).sgT) (GlobalTheory.Mem.Col2.fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1)) (j v)) w) → ∀ s : (I.stX a).Stab c, w = (B.embLL ((I.stX a).chr c.1 s.1 : B.LL))⁻¹ • Formalism.L2.DIV.rhoP (I.perIn u a).sgT (Formalism.L2.DIV.embGL (Formalism.L2.Col.embAt B.embLL B.fields.emb) ((I.stX a).gam c.1 s.1)) w := by
  intro B X I hI hP l Z u G _ _ Pl0 T F Ks _ _ _ R g c₀ hX j hj P t a bad K hR hb hL f c w hw hf s
  have hθ : IsInfFam R.θ := hX.inf
  have hst : (K.stabI c s).1 = (I.stX a).gam c.1 s.1 := hR.stab c s
  obtain ⟨κ₀, hκ₀, e0⟩ := (K.stabI_range c (K.stabI c s)).1 ⟨s, rfl⟩
  let κ : K.lev.U := ⟨κ₀, hκ₀⟩⁻¹
  have e1 : (K.y c).1 = Formalism.UG.bc (Formalism.UG.inclE (F := (I.rec7 l Z).host.F)
      (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) (K.stabI c s).1 * (K.y c).1 * κ.1 := by
    rw [← e0]
    show _ = (K.y c).1 * κ₀ * (K.y c).1⁻¹ * (K.y c).1 * κ₀⁻¹
    group
  have e2 := chi_eq_chr I a hR c s κ (by
    have h0 := e1
    rw [hst] at h0
    exact h0)
  haveI : Finite ((I.stX a).Stab c) := ((I.fm l u a).stabPFin c : Finite _)
  have e3 := star_eq_inv (((I.stX a).chr c.1).comp (Subgroup.subtype _ : (I.stX a).Stab c →* _)) B.embLL s
  obtain ⟨γ, hγ, e4, e5⟩ := exists_ratPt hθ (rankP (I.rec7 l Z)) (K.stabI c s).1 (K.stabI c s).2
  obtain ⟨k, hk⟩ := hasMat_exists (D := I.rec7 l Z) ⟨κ.1, ((K.lev.U_eq _).1 κ.2).1⟩
  obtain ⟨h, hh⟩ := hasMat_exists (D := I.rec7 l Z) (K.y c)
  have e6 : levChi _ R.βX (datXP R P t) (g.bT⁻¹ * k * g.bT) = (B.embLL ((I.stX a).chr c.1 s.1 : B.LL))⁻¹ :=
    (hL.2 k κ hk).trans ((congrArg star e2).trans e3)
  refine eq_smul_of_pair (gramC (gramP (I.rec7 l Z)) (embT (I.rec7 l Z))) _ _ _ (sgT_eq I l Z u a)
    (GlobalTheory.Mem.Col2.fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1)) (fun _ => rfl) (infPt R.θ γ) _ ?_ hw _ fun φ hφ => ?_
  · funext τ
    refine Units.ext ((e5 τ).trans ?_)
    rw [hst]
    ext p q
    show B.host.φ₀ _ = _
    rw [← B.embE_φ₀]
    rfl
  · obtain ⟨v, rfl⟩ := (hj.range ▸ hφ : φ ∈ LinearMap.range j)
    obtain ⟨v', e7, e8⟩ := coset_law_moved (χ := levChi _ R.βX (datXP R P t)) hθ hj hb hγ hk ((hL.1 k).2 ⟨κ, hk⟩) hh hh
      (e1.trans (congrArg (· * (K.y c).1 * κ.1) e4.symm)) v
    refine ⟨j v', e7, ?_⟩
    have e9 := e8 f.1 f.2
    rw [hf v' h hh, hf v h hh, e6] at e9
    exact e9

end Main

end GlobalTheory.AdForm.StabInv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReductionUniqueOfMaximalStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduction_unique_of_maximal : ∀ (D : D7) (u : D.what₂.Word) (d : GlobalTheory.SeeSaw.Dat D u) (τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E) (PP : Formalism.L2.DIV.Pl D.host.E) (G : GlobalTheory.LocMod.GAt d τ PP) (x x' : G.S.P.J) (g g' : GL (Fin D.R.r) (Formalism.L2.DIV.kP PP)), G.Red x g → G.Red x' g' → GlobalTheory.StepData.MaxM ((x' : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val - (x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val) → g' = g := by
  first | exact @GlobalTheory.LevelComb.red_uniq | exact GlobalTheory.LevelComb.red_uniq | (intros; apply GlobalTheory.LevelComb.red_uniq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResidueEqZeroIffValLt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.SplitPt

theorem residue_eq_zero_iff_val_lt {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (t : 𝒪[k]) : residue 𝒪[k] t = 0 ↔ valuation k (t : k) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact Valuation.Integer.not_isUnit_iff_valuation_lt_one

theorem resField_equiv : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k) (PP : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt q.e PP → (∀ x : 𝓞 D.host.E, q.pr (incA D (x : D.host.E)) ∈ 𝒪[k]) ∧ ∃ ρ : 𝓀[k] ≃+* (𝓞 D.host.E ⧸ PP.asIdeal), ∀ (x : 𝓞 D.host.E) (t : 𝒪[k]), (t : k) = q.pr (incA D (x : D.host.E)) → ρ (residue 𝒪[k] t) = Ideal.Quotient.mk PP.asIdeal x := by
  intro D k _ _ _ _ q PP he
  obtain ⟨hint, -⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D q.e PP he
  have hmem : ∀ x : 𝓞 D.host.E, q.pr (incA D (x : D.host.E)) ∈ 𝒪[k] := fun x => by
    rw [q.pr_mem_iff]
    exact mul_mem hint (Formalism.L2.DIV.oToS D.host.F D.host.E x).2
  refine ⟨hmem, ?_⟩
  let ψ : 𝓞 D.host.E →+* 𝒪[k] :=
    ((q.pr.comp (incA D)).comp (algebraMap (𝓞 D.host.E) D.host.E)).codRestrict 𝒪[k] hmem
  have hψ : ∀ x, (ψ x : k) = q.pr (incA D (x : D.host.E)) := fun x => rfl
  let φ : 𝓞 D.host.E →+* 𝓀[k] := (residue 𝒪[k]).comp ψ
  have hker : RingHom.ker φ = PP.asIdeal := by
    ext x
    have e1 : ((Formalism.L2.DIV.oToS D.host.F D.host.E x : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) =
        toEAf D (incA D (x : D.host.E)) := rfl
    rw [RingHom.mem_ker, RingHom.comp_apply, residue_eq_zero_iff_val_lt, hψ, q.mem_iff_val_lt he, e1, prF_toEAf]
  have hsurj : Function.Surjective φ := by
    intro c
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
    set z : EAf D := toEAf D (q.sec a) with hz
    have hprz : q.prF he z = a := by rw [hz, prF_toEAf, q.pr_sec]
    have hoff : (1 - toEAf D q.e) * z = 0 := by
      have he1 : toEAf D q.e * z = z := by
        rw [hz, ← RingHom.map_mul, ← q.sec_pr, q.pr_sec]
      rw [sub_mul, one_mul, he1, sub_self]
    have hzint : z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
      (q.mem_intAf_iff he z).2 ⟨by rw [hoff]; exact zero_mem _, by rw [hprz]; exact a.2⟩
    obtain ⟨x, hx0⟩ := GlobalTheory.FunObj.Comparison₂.exists_approx PP.ne_bot ⟨z, hzint⟩
    have hx : (⟨z, hzint⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) - Formalism.L2.DIV.oToS D.host.F D.host.E x ∈
        Formalism.L2.DIV.idS D.host.F PP.asIdeal := hx0
    have hv := q.val_lt_of_mem_idS he hx
    refine ⟨x, ?_⟩
    show residue 𝒪[k] (ψ x) = residue 𝒪[k] a
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff_val_lt]
    have e1 : (((⟨z, hzint⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) - Formalism.L2.DIV.oToS D.host.F D.host.E x :
        Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) = z - toEAf D (incA D (x : D.host.E)) := rfl
    rw [e1, map_sub, hprz, prF_toEAf] at hv
    have e2 : ((ψ x - a : 𝒪[k]) : k) = -((a : k) - q.pr (incA D (x : D.host.E))) := by
      rw [AddSubgroupClass.coe_sub, hψ]; ring
    rw [e2, Valuation.map_neg]; exact hv
  refine ⟨((Ideal.quotEquivOfEq hker).symm.trans (RingHom.quotientKerEquivOfSurjective hsurj)).symm, ?_⟩
  intro x t ht
  have htx : t = ψ x := Subtype.ext (by rw [ht, hψ])
  rw [RingEquiv.symm_apply_eq, htx]
  rfl

end GlobalTheory.FinPl.SplitPt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowLineIdealEqInverseDifferentPow
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

namespace GlobalTheory.Core.Mi.LatMatch.DiffInv

theorem aaD_eq_dI_pow : ∀ (D : D7) (i : Fin D.R.rS), aaD D i = dI D ^ (D.R.rS - i.1) := by
  intro D i
  have hP := Formalism.IndefR.Fin.factPrincipalDatum D.R D.host
  have hinv : dI D = (ddS D)⁻¹ := by
    rw [GlobalTheory.IntTerm.Conv.ddS_eq]
    exact eq_inv_of_mul_eq_one_left hP
  rw [hinv, inv_pow, aaD, ← Nat.cast_sub i.2.le, _root_.zpow_neg, _root_.zpow_natCast]

end GlobalTheory.Core.Mi.LatMatch.DiffInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalarComplementFrameDiagModConductor
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ScalW

set_option maxHeartbeats 800000 in
theorem scalar_diag_mod_g : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (β : GL (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)), IsLiftFrame X.B.I X.B.g (flagVec X.e0 X.f0 X.z0 X.bw X.bwd) β → ∀ c : Formalism.L2.Herm.intAf X.B.I.F X.B.I.E, c * sigInt X.B.I c = 1 → (∀ N : ℕ, Nat.Coprime N X.B.g → ZMod' X.B.I N (1 - c.1)) → ∃ h ∈ Hfin X u, (∀ h' ∈ Hfin X u, h * h' = h' * h) ∧ ∃ x : GL (Fin X.B.I.n) (Formalism.L2.Herm.intAf X.B.I.F X.B.I.E), frGL β x = (((X.xu u)⁻¹ * h * X.xu u : X.B.I.Gf) : GL (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)) ∧ ∀ i j, ZMod' X.B.I X.B.g (((x : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Formalism.L2.Herm.intAf X.B.I.F X.B.I.E)) - midDiag X.B.I.n D.R.rS D.R.k 1 c) i j).1 := by
  intro D X u β hβ c hc hN
  have hg1 : 1 ≤ X.B.g := Formalism.L2.SG.PoincareInHH.Cut.one_le_g X
  obtain ⟨M6, hM6, hz6⟩ := GlobalTheory.T.exists_coprime_multiplier_one_sub_norm_congr_zero D X u
  have hTg : Nat.Coprime (D.mem u).A.T X.B.g := GlobalTheory.T.nat_coprime_of_congr_mul_one_sub_mod_level X.B.I X.B.g _ M6 hg1 hM6 hz6
  have hT0 : (D.mem u).A.T ≠ 0 := (D.mem u).A.T_prime.ne_zero
  obtain ⟨Mb, hMb, hb7⟩ := GlobalTheory.T.exists_coprime_multiplier_hyperbolic_terms_near_reference D X
  obtain ⟨Mc, hMc, hc7⟩ := GlobalTheory.T.exists_coprime_multiplier_negativeVector_term_near D X u
  have hc' : c.1 * sigA X.B.I c.1 = 1 := by
    have := congrArg Subtype.val hc
    simpa [sigInt_coe] using this
  obtain ⟨hfix, hfz, hidem⟩ := GlobalTheory.T.orthProjHyperbolicNegativeSpan_fixes_basis_and_idempotent D X u
  obtain ⟨h, hh, hhi⟩ := GlobalTheory.T.exists_unitary_scalarBlend_selfAdjoint_idempotent X.B.I (GlobalTheory.ScalW.prjM X u) c.1
    (fun y => by rw [GlobalTheory.ScalW.prjM_mulVec, GlobalTheory.ScalW.prjM_mulVec, hidem])
    (fun x y => by rw [GlobalTheory.ScalW.prjM_mulVec, GlobalTheory.ScalW.prjM_mulVec, GlobalTheory.T.orthProjHyperbolicNegativeSpan_selfAdjoint]) hc'
  have hh' : X.B.I.fmat h = GlobalTheory.ScalW.hMat X u c.1 := hh
  have hhi' : X.B.I.fmat h⁻¹ = GlobalTheory.ScalW.hMat X u (sigA X.B.I c.1) := hhi
  obtain ⟨hH, hcomm⟩ := GlobalTheory.T.scalarBlend_projection_mem_stabilizer_and_commutes D X u c.1 h hfix hfz hh'
  obtain ⟨hP0, hfl⟩ := GlobalTheory.T.orthProjReferenceFrame_on_flagBasis_mod_level D X

  set P' : VA X.B.I → VA X.B.I := fun y => X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.prj X u (X.B.I.fmat (X.xu u) *ᵥ y)
    with hP'
  set M := Mb * Mc * M6 * (D.mem u).A.T with hMdef
  have hMg : Nat.Coprime M X.B.g := ((hMb.mul hMc).mul hM6).mul hTg
  have smulL : ∀ {s : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F}, s ∈ IntAf X.B.I.F X.B.I.E → ∀ {y : VA X.B.I},
      y ∈ X.B.I.Lf → s • y ∈ X.B.I.Lf := fun hs _ hy => X.B.I.Lf.smul_mem (⟨_, hs⟩ : IntAf X.B.I.F X.B.I.E) hy
  have smulM : ∀ {s : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F}, s ∈ IntAf X.B.I.F X.B.I.E → ∀ {y : VA X.B.I},
      y ∈ mL X.B.I X.B.g → s • y ∈ mL X.B.I X.B.g := fun hs _ hy => (mL X.B.I X.B.g).smul_mem (⟨_, hs⟩ : IntAf X.B.I.F X.B.I.E) hy
  have hnear : ∀ y ∈ X.B.I.Lf, (M : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (P' y - GlobalTheory.ScalW.prj0 X y) ∈ mL X.B.I X.B.g := by
    intro y hy
    rw [hP']
    beta_reduce
    rw [GlobalTheory.T.wordElement_conj_orthProjHyperbolicNegativeSpan_eq]
    simp only [GlobalTheory.ScalW.prj0]
    have hA1 : (Mb : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • ((∑ a, hA X.B.I (GlobalTheory.ScalW.fV X a) y • GlobalTheory.ScalW.eV X a) -
        ∑ a, hA X.B.I (X.f0 a) y • X.e0 a) ∈ mL X.B.I X.B.g := by
      rw [← Finset.sum_sub_distrib, Finset.smul_sum]
      exact Submodule.sum_mem _ fun a _ => (hb7 y hy a).1
    have hA2 : (Mb : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • ((∑ a, hA X.B.I (GlobalTheory.ScalW.eV X a) y • GlobalTheory.ScalW.fV X a) -
        ∑ a, hA X.B.I (X.e0 a) y • X.f0 a) ∈ mL X.B.I X.B.g := by
      rw [← Finset.sum_sub_distrib, Finset.smul_sum]
      exact Submodule.sum_mem _ fun a _ => (hb7 y hy a).2
    have hZ := hc7 y hy
    have hw0 : hA X.B.I X.z0 y • X.z0 ∈ X.B.I.Lf :=
      X.B.I.Lf.smul_mem (⟨_, GlobalTheory.St.G.FrameClose.hA_int X.vectorsInLattice.2.1 hy⟩ : IntAf X.B.I.F X.B.I.E) X.vectorsInLattice.2.1
    have hW : ((M6 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (1 - (((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F))) •
        (hA X.B.I X.z0 y • X.z0) ∈ mL X.B.I X.B.g := Formalism.L2.SG.PoincareInHH.Cut.GU.smul_mL X hz6 hw0
    have hTd : (((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) *
        divN X.B.I (D.mem u).A.T (hA X.B.I (X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.zV X u) y) =
        hA X.B.I (X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.zV X u) y := Formalism.L2.SG.Pf.unitaryCongruence.gmul_divN X.B.I _ hT0 _
    generalize (∑ a, hA X.B.I (GlobalTheory.ScalW.fV X a) y • GlobalTheory.ScalW.eV X a) = S1 at hA1 ⊢
    generalize (∑ a, hA X.B.I (GlobalTheory.ScalW.eV X a) y • GlobalTheory.ScalW.fV X a) = S2 at hA2 ⊢
    generalize (∑ a, hA X.B.I (X.f0 a) y • X.e0 a) = S3 at hA1 ⊢
    generalize (∑ a, hA X.B.I (X.e0 a) y • X.f0 a) = S4 at hA2 ⊢
    generalize X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.zV X u = z' at hZ hTd ⊢
    generalize divN X.B.I (D.mem u).A.T (hA X.B.I z' y) = dd at hTd ⊢
    generalize hA X.B.I X.z0 y • X.z0 = w0 at hZ hW ⊢
    rw [← hTd] at hZ
    rw [hMdef, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, GlobalTheory.ScalW.scalW_ident]
    have hN' : ∀ m : ℕ, (m : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ∈ IntAf X.B.I.F X.B.I.E := fun m => natCast_mem _ m
    exact sub_mem (sub_mem (add_mem (smulM (mul_mem (mul_mem (hN' _) (hN' _)) (hN' _)) hA1)
      (smulM (mul_mem (mul_mem (hN' _) (hN' _)) (hN' _)) hA2)) (smulM (mul_mem (hN' _) (hN' _)) hZ))
      (smulM (mul_mem (hN' _) (hN' _)) hW)
  have key : ∀ s : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F, ZMod' X.B.I M (1 - s) → ∀ y ∈ X.B.I.Lf,
      (1 - s) • (P' y - GlobalTheory.ScalW.prj0 X y) ∈ mL X.B.I X.B.g := by
    intro s hzs y hy
    obtain ⟨t, ht, e⟩ := hzs
    rw [e, mul_comm, mul_smul]
    exact smulM ht (hnear y hy)
  have hint : ∀ s : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F, s ∈ IntAf X.B.I.F X.B.I.E → ZMod' X.B.I M (1 - s) →
      ∀ y ∈ X.B.I.Lf, s • y + (1 - s) • P' y ∈ X.B.I.Lf := by
    intro s hs hzs y hy
    have e : s • y + (1 - s) • P' y = s • y + (1 - s) • (P' y - GlobalTheory.ScalW.prj0 X y) + (1 - s) • GlobalTheory.ScalW.prj0 X y := by
      rw [smul_sub]; abel
    rw [e]
    exact add_mem (add_mem (smulL hs hy) (GlobalTheory.St.G.FrameClose.mL_le _ (key s hzs y hy)))
      (smulL (sub_mem (one_mem _) hs) (hP0 y hy))
  have hact : ∀ (s : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (k : X.B.I.Gf), X.B.I.fmat k = GlobalTheory.ScalW.hMat X u s →
      ∀ y, X.B.I.fmat ((X.xu u)⁻¹ * k * X.xu u) *ᵥ y = s • y + (1 - s) • P' y := by
    intro s k hk y
    rw [Formalism.L2.SG.PoincareInHH.Cut.fmat_mul, Formalism.L2.SG.PoincareInHH.Cut.fmat_mul, ← mulVec_mulVec, ← mulVec_mulVec, hk,
      GlobalTheory.ScalW.hMat_mulVec, mulVec_add, mulVec_smul, mulVec_smul, mulVec_mulVec,
      Formalism.L2.SG.PoincareInHH.Cut.fmat_inv_mul, one_mulVec]
  have hcM : ZMod' X.B.I M (1 - c.1) := hN M hMg
  have hsM : ZMod' X.B.I M (1 - sigA X.B.I c.1) := by
    have := Formalism.L2.SG.Pf.unitaryCongruence.Z_sig X.B.I M hcM
    rwa [map_sub, map_one] at this
  have hinvY : ((X.xu u)⁻¹ * h * X.xu u)⁻¹ = (X.xu u)⁻¹ * h⁻¹ * X.xu u := by group
  set d : Fin X.B.I.n → Formalism.L2.Herm.intAf X.B.I.F X.B.I.E :=
    fun i => if D.R.rS ≤ i.val ∧ i.val < D.R.rS + D.R.k then c else 1 with hd
  obtain ⟨x, hx1, hx2⟩ := GlobalTheory.T.frame_matrix_diagonal_mod_level_of_diagonal_action X.B.I X.B.g _ β ((X.xu u)⁻¹ * h * X.xu u) d hβ
    (fun y hy => by rw [hact _ h hh']; exact hint _ c.2 hcM y hy)
    (fun y hy => by
      rw [hinvY, hact _ _ hhi']
      exact hint _ (Formalism.L2.SG.Pf.unitaryCongruence.sigA_mem X.B.I c.2) hsM y hy)
    (fun j => by
      obtain ⟨hbL, hW, hnW⟩ := hfl j.val
      rw [hact _ h hh']
      have hk := key c.1 hcM _ hbL
      by_cases hj : D.R.rS ≤ j.val ∧ j.val < D.R.rS + D.R.k
      · have e1 : (d j).1 = c.1 := by simp [hd, hj]
        rw [e1]
        have e : c.1 • flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val + (1 - c.1) • P' (flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val)
            - c.1 • flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val =
            (1 - c.1) • (P' (flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val) - GlobalTheory.ScalW.prj0 X (flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val))
            + (1 - c.1) • GlobalTheory.ScalW.prj0 X (flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val) := by
          rw [smul_sub]; abel
        rw [e]
        exact add_mem hk (smulM (sub_mem (one_mem _) c.2) (hW hj))
      · have e1 : (d j).1 = 1 := by simp [hd, hj]
        rw [e1]
        have e : c.1 • flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val + (1 - c.1) • P' (flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val)
            - (1 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val =
            (1 - c.1) • (P' (flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val) - GlobalTheory.ScalW.prj0 X (flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val))
            + (1 - c.1) • (GlobalTheory.ScalW.prj0 X (flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val) - flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val) := by
          simp only [smul_sub, sub_smul, one_smul]; abel
        rw [e]
        exact add_mem hk (smulM (sub_mem (one_mem _) c.2) (hnW hj)))
  refine ⟨h, hH, hcomm, x, hx1, fun i j => ?_⟩
  have e : midDiag X.B.I.n D.R.rS D.R.k 1 c = Matrix.diagonal d := by
    simp only [midDiag, hd]
  rw [e]
  exact hx2 i j

end GlobalTheory.ScalW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatHalfTensorSplitPlaceSelfDualStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhatHalf_tensor_split_place_selfDual : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (M : Lat S) (M' : Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ (P : LocPl ψ S T M M') (e : AE D), e * P.q.e = 0 → ∀ Φ : WO S T → ℂ, IsSBHalf e (latO S T (M : Set _) (M' : Set _) fun _ => True) Φ → ∀ Ψ ∈ SB (Matrix P.Y P.Y' P.k), IsSBHalf (e + P.q.e) (latO S T (M : Set _) (M' : Set _) fun _ => True) ((ofSplit P.q).tensorAt P.FS P.FT Φ Ψ) := by
  first | exact @GlobalTheory.TensorLatO.isSBHalf_tensorAt_latO | exact GlobalTheory.TensorLatO.isSBHalf_tensorAt_latO | (intros; apply GlobalTheory.TensorLatO.isSBHalf_tensorAt_latO <;> assumption)
end

