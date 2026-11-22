import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0293
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulCompSmul
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0278
import Formalism.LocalToGlobal.Columns.XtPhiTopGCongr
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.TopLawQ
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointRightTranslateByLevelCoupledStep
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypePrimeFramesRightTranslateDifferIntegralGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiAtCongInvariant
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartsReadingStepMoveBasePointsOneOffLevelPrime
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FirstCoupledKernelEquivariantCosets
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0294
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0114
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0296
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousToZModComp
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0104
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0139
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0266
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0269
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0295

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicDatumInvarianceSupportKernelChainStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicDatum_invariance_support_kernelChain : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => PtEx A a → SizeLaw A a) := by
  first | exact @GlobalTheory.TwV.sizeLaw_of_tie | exact GlobalTheory.TwV.sizeLaw_of_tie | (intros; apply GlobalTheory.TwV.sizeLaw_of_tie <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartBasePointAdelicRightMulLevelStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_base_point_adelic_right_mul_level : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (κ : ((St i hi).K β).lev.U) (x x₁ : UA D i hi)
    (p q : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i) (k : SB t μ → (Sp t.X.E (D.R.N i) ≃ₗ[t.X.E] Sp t.X.E (D.R.N i))),
    x₁.1 = x.1 * κ.1 → IsPtAd A a i hi β x p → q.deco.1.N = p.deco.1.N → q.deco.1.f = p.deco.1.f →
    (∀ P, frsF t.sel (t.tup μ) q P = frsF t.sel (t.tup μ) p P * k P) → (∀ P, k P ∈ GLint t.X.E (D.R.N i) P.1) →
    (∀ P, InFrame t.seam (A.fb i hi β) (t.cst μ).D P κ.1 (k P)) → IsPtAd A a i hi β x₁ q) := by
  first | exact @GlobalTheory.PtMove.isPtAd_mul_lev | exact GlobalTheory.PtMove.isPtAd_mul_lev | (intros; apply GlobalTheory.PtMove.isPtAd_mul_lev <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartFramesMulAdeleAtBadPrime
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrameMove

section Cong

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}

theorem congAt_mono {P : HeightOneSpectrum (𝓞 E)} {m n : ℕ} (hmn : m ≤ n) {k : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)}
    (h : CongAt (F := F) P n k) : CongAt (F := F) P m k := by
  intro a b
  have hq : ((qOf P : ℕ) : E) ≠ 0 := by
    have : qOf P ≠ 0 := fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact_mod_cast this
  have e0 : (((qOf P : ℕ) : E) ^ m)⁻¹ = algebraMap (𝓞 E) E (((qOf P : ℕ) : 𝓞 E) ^ (n - m)) * (((qOf P : ℕ) : E) ^ n)⁻¹ := by
    rw [map_pow, map_natCast]
    have hn : ((qOf P : ℕ) : E) ^ n = ((qOf P : ℕ) : E) ^ m * ((qOf P : ℕ) : E) ^ (n - m) := by
      rw [← pow_add, Nat.add_sub_cancel' hmn]
    rw [hn]
    field_simp
  have e : iA F E (((qOf P : ℕ) : E) ^ m)⁻¹ * ((k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1) a b =
      iA F E (algebraMap (𝓞 E) E (((qOf P : ℕ) : 𝓞 E) ^ (n - m))) *
        (iA F E (((qOf P : ℕ) : E) ^ n)⁻¹ * ((k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1) a b) := by
    rw [← mul_assoc, ← map_mul, e0]
  rw [e]
  exact GlobalTheory.CplPt.intAtA_mul (GlobalTheory.CplPt.intAtA_int _) (h a b)

end Cong

theorem mem_of_local {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (d : ℕ)
    (k : Sp E n ≃ₗ[E] Sp E n) (hk : ∀ x ∈ stdAt E n P, ((qOf P ^ d : ℕ) : E)⁻¹ • (k x - x) ∈ stdAt E n P)
    (x : Sp E n) (hx : x ∈ stdAt E n P) : k x ∈ stdAt E n P := by
  have hq : qOf P ≠ 0 := fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  have hc : ((qOf P ^ d : ℕ) : E) ≠ 0 := by exact_mod_cast pow_ne_zero d hq
  have e : k x = x + (qOf P ^ d) • (((qOf P ^ d : ℕ) : E)⁻¹ • (k x - x)) := by
    rw [← Nat.cast_smul_eq_nsmul E, smul_smul, mul_inv_cancel₀ hc, one_smul, add_sub_cancel]
  rw [e]
  exact add_mem hx (nsmul_mem (hk x hx) _)

end GlobalTheory.FrameMove

namespace GlobalTheory.FrameMove

theorem frames_mul : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (j : ℕ) (hj : j ≤ D.R.m) (β : (St j hj).Ch) (x x₁ : UA D j hj)
    (κ : GL (Fin (D.R.N j)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) j), x₁.1 = x.1 * κ →
    IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
    ∀ (P : SB t μ) (dep : SB t μ → ℕ) (g : Sp t.X.E (D.R.N j) ≃ₗ[t.X.E] Sp t.X.E (D.R.N j)),
      1 ≤ dep P → dep P ≤ (t.cst μ).D P → g ∈ GLint t.X.E (D.R.N j) P.1 →
      InFrame t.seam (A.fb j hj β) dep P κ g →
      (frsF t.sel (t.tup μ) p₁ P).trans ((frsF t.sel (t.tup μ) p P).symm.trans g.symm) ∈ GLint t.X.E (D.R.N j) P.1 ∧
      ∀ w ∈ stdAt t.X.E (D.R.N j) P.1, ((qOf P.1 : t.X.E) ^ dep P)⁻¹ •
        ((frsF t.sel (t.tup μ) p₁ P).trans ((frsF t.sel (t.tup μ) p P).symm.trans g.symm) w - w) ∈ stdAt t.X.E (D.R.N j) P.1) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _ _ j hj β x x₁ κ p p₁ hxκ hp hp₁ P dep g hd1 hdD hg hIn
  have hD1 : 1 ≤ (t.cst μ).D P := hd1.trans hdD
  have hu := hp.frame P
  have hu₁ := hp₁.frame P
  unfold NearAt at hu hu₁
  unfold InFrame NearAt at hIn
  rw [hxκ] at hu₁
  set h := (frsF t.sel (t.tup μ) p₁ P).trans ((frsF t.sel (t.tup μ) p P).symm.trans g.symm) with hh
  have hs : h = g⁻¹ * ((frsF t.sel (t.tup μ) p P)⁻¹ * frsF t.sel (t.tup μ) p₁ P) := by
    ext w; rfl
  have key : ratA D.host.F (seamGL t.seam h) =
      ((ratA D.host.F (seamGL t.seam g))⁻¹ *
        ((ratA D.host.F (A.crd j hj) * x.1 * ratA D.host.F (A.fb j hj β P))⁻¹ * ratA D.host.F (seamGL t.seam (frsF t.sel (t.tup μ) p P)))⁻¹ *
        ratA D.host.F (seamGL t.seam g)) *
      (((ratA D.host.F (A.fb j hj β P))⁻¹ * κ * ratA D.host.F (A.fb j hj β P))⁻¹ * ratA D.host.F (seamGL t.seam g))⁻¹ *
      ((ratA D.host.F (A.crd j hj) * (x.1 * κ) * ratA D.host.F (A.fb j hj β P))⁻¹ *
        ratA D.host.F (seamGL t.seam (frsF t.sel (t.tup μ) p₁ P))) := by
    rw [hs]
    simp only [map_mul, map_inv]
    group
  have c1 := GlobalTheory.CplPt.congAt_conj (dep P)
    (congAt_mono hdD (GlobalTheory.LevFrame.congAt_inv _ _ _ _ _ _ hD1 hu))
    (fun a b => GlobalTheory.CplPt.seamGL_int t.seam ⟨g, hg⟩ a b)
  have c2 := GlobalTheory.LevFrame.congAt_inv _ _ _ _ _ _ hd1 hIn
  have c3 := congAt_mono hdD hu₁
  have hC : CongAt (F := D.host.F) (seamP t.seam P.1) (dep P) (ratA D.host.F (seamGL t.seam h)) := by
    rw [key]
    exact GlobalTheory.CplPt.congAt_mul _ (GlobalTheory.CplPt.congAt_mul _ c1 c2) c3
  have hCi : CongAt (F := D.host.F) (seamP t.seam P.1) (dep P) (ratA D.host.F (seamGL t.seam h⁻¹)) := by
    rw [map_inv, map_inv]
    exact GlobalTheory.LevFrame.congAt_inv _ _ _ _ _ _ hd1 hC
  have l1 := GlobalTheory.TwU.MidIndep.congAt_local t.seam P.1 (dep P) (D.R.N j) h hC
  have l2 := GlobalTheory.TwU.MidIndep.congAt_local t.seam P.1 (dep P) (D.R.N j) h⁻¹ hCi
  refine ⟨fun w => ⟨fun hw => ?_, fun hw => mem_of_local P.1 (dep P) h l1 w hw⟩, fun w hw => ?_⟩
  · have := mem_of_local P.1 (dep P) h⁻¹ l2 _ hw
    rwa [show (h⁻¹ : Sp t.X.E (D.R.N j) ≃ₗ[t.X.E] Sp t.X.E (D.R.N j)) (h w) = w from h.symm_apply_apply w] at this
  · have := l1 w hw
    rwa [Nat.cast_pow] at this

end GlobalTheory.FrameMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartsReadingStepMoveBasePointsOneOffLevelPrimeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartsReadingStep_moveBasePoints_one_offLevelPrime : GlobalTheory.TwU.AtTrue.ReadsMove := by
  first | exact @GlobalTheory.TwU.AtTrue.readsMove_holds | exact GlobalTheory.TwU.AtTrue.readsMove_holds | (intros; apply GlobalTheory.TwU.AtTrue.readsMove_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColumnFieldKernelPushforwardEqHostKernelFunctionStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnFieldKernel_pushforward_eq_hostKernelFunction : ∀ {D : D7} {X : Fields} (s : Seam D X), s.Ok → ∀ {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) {a b : ℕ} (SS : Finset (HeightOneSpectrum (𝓞 X.E))) (cl : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (Ξ : HomE X.E a b → ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → δ ≠ 0 → B.VecP χ → 0 < cl → (∀ Q ∈ (SS.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding), conjPrime₂ Q ∉ (SS.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding)) → TaylorLogMetric.admitted D a b (s.lat N) (s.lat N') → DatLoc D cc (SS.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding) cl (s.lat N) (s.lat N') (fun x => Ξ (seamHom s x)) → s.push (thC (X.embC s.σ₀) δ D.host.d (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹ (ambOf s B χ cD).AA SS N N' cl Ξ ((ambOf s B χ cD).e a b N N')) = kerTh B χ (SS.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding) cl (s.lat N) (s.lat N') (fun x => Ξ (seamHom s x)) := by
  first | exact @GlobalTheory.TwU.SeamKer.seam_kerTh | exact GlobalTheory.TwU.SeamKer.seam_kerTh | (intros; apply GlobalTheory.TwU.SeamKer.seam_kerTh <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CongruentOneMemStepLevelsCharacterOneStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.congruent_one_mem_step_levels_character_one : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ),
    X.Ok → Pr.Ok → ChIdx.Ok Ch sel mu cst L G m2 → ∀ j (b : L.β j) (P : rowSG Pr sel mu) (k : GLint X.E (R.N j) P.1), j ≤ m2 + 1 →
    (∀ s l, IntAt P.1 ((((qOf P.1 : ℕ) : X.E) ^ (cst.D P))⁻¹ * (k.1 (Pi.single s 1) l - (Pi.single s 1 : Sp X.E (R.N j)) l))) →
    GlobalTheory.TopLaw.LevAt (L.levG j b) (L.levQ j b) P k 1 := by
  first | exact @GlobalTheory.LevOneAt.levAt_one | exact GlobalTheory.LevOneAt.levAt_one | (intros; apply GlobalTheory.LevOneAt.levAt_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CouplingCosetsRightTranslateInFramesTypePrimeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop GlobalTheory.TopStep
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coupling_cosets_right_translate_in_frames_type_prime : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (hi : t.m2 + 1 ≤ D.R.m) (β : (St (t.m2 + 1) hi).Ch) (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (t.m2 + 1))
    (P : SB t μ), P.1 ∈ t.Pr.vGs → ∀ (Gg k : GLint t.X.E (D.R.N (t.m2 + 1)) P.1) z, A.cplRel β P Gg.1 z →
    redGL _ P.1 k = redGL _ P.1 Gg → frsF t.sel (t.tup μ) p₁ P = frsF t.sel (t.tup μ) p P * k.1 →
    (∀ l, IntAt P.1 ((qOf P.1 : t.X.E) * (frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) hi β p)) l)) ∧
    (∀ l, IntAt P.1 ((qOf P.1 : t.X.E) * (frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁)) l)) ∧
    k.1 ((frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁))) -
      (frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) hi β p)) ∈ stdAt t.X.E _ P.1) := by
  first | exact @GlobalTheory.CplCosetPt.cosetOf_frames_vG | exact GlobalTheory.CplCosetPt.cosetOf_frames_vG | (intros; apply GlobalTheory.CplCosetPt.cosetOf_frames_vG <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspRepCharacterSupportLiftTransTowerStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspRep_characterSupportLift_trans_tower : ∀ (K M N : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field M] [NumberField M] [IsTotallyComplex M] [Field N] [NumberField N] [IsTotallyComplex N] [Algebra K M] [Algebra M N] [Algebra K N] [IsScalarTower K M N] (a : ℕ) (π : CuspSub K a) (P : CuspSub M a) (Q : CuspSub N a), CharLift π P → CharLift P Q → CharLift π Q := by
  first | (exact @GlobalTheory.RoadU.charLift_trans) | (exact GlobalTheory.RoadU.charLift_trans) | (intros; apply GlobalTheory.RoadU.charLift_trans  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumJetsTranslate
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.MomT
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recSeam HostTie AnTie badS)
open GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation (StdOver)

noncomputable section

namespace GlobalTheory.DatumJets.Transl

open GlobalTheory.LiftTypePrime GlobalTheory.MomT.PtMoments

theorem exists_denom {E W : Type} [Field E] [NumberField E] [AddCommGroup W] [Module (𝓞 E) W] {p : ℕ} (hp : p.Prime)
    {M M' : Submodule (𝓞 E) W} (hM : M.FG)
    (h : ∀ P : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ P.asIdeal → M ≤ localization₂ P.asIdeal M') :
    ∃ s : ℕ, Nat.Coprime s p ∧ ∀ x ∈ M, (s : 𝓞 E) • x ∈ M' := by
  have key : ∀ x : W, ∃ s : ℕ, Nat.Coprime s p ∧ (x ∈ M → (s : 𝓞 E) • x ∈ M') := fun x => by
    by_cases hx : x ∈ M
    swap
    · exact ⟨1, by simp, fun h => absurd h hx⟩
    by_contra hn
    let I : Ideal (𝓞 E) := M'.comap (LinearMap.toSpanSingleton (𝓞 E) W x)
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
    have : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).2 hpZ
    have hI : I.comap (algebraMap ℤ (𝓞 E)) ≤ Ideal.span {(p : ℤ)} := fun z hz => by
      rw [Ideal.mem_span_singleton, Int.natCast_dvd]
      by_contra hz'
      refine hn ⟨z.natAbs, ((Nat.Prime.coprime_iff_not_dvd hp).2 hz').symm, fun _ => ?_⟩
      have hz1 : (z : 𝓞 E) • x ∈ M' := hz
      rcases Int.natAbs_eq z with h1 | h1
      · rw [h1, Int.cast_natCast] at hz1; exact hz1
      · rw [h1, Int.cast_neg, Int.cast_natCast, neg_smul, neg_mem_iff] at hz1; exact hz1
    obtain ⟨Q, hQ, hQp, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (Ideal.span {(p : ℤ)}) I hI
    have hpQ : (p : 𝓞 E) ∈ Q := by
      have : (p : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 E)) := hQc ▸ Ideal.mem_span_singleton_self _
      simpa using this
    have hQ0 : Q ≠ ⊥ := by
      rintro rfl
      exact hp.ne_zero (by simpa using hpQ)
    obtain ⟨c, hc, hcx⟩ : ∃ c : 𝓞 E, c ∉ Q ∧ c • x ∈ M' := h ⟨Q, hQp, hQ0⟩ hpQ hx
    exact hc (hQ hcx)
  choose f hf hfx using key
  obtain ⟨S, rfl⟩ := hM
  refine ⟨∏ x ∈ S, f x, Nat.Coprime.prod_left fun x _ => hf x, fun x hx => ?_⟩
  refine (Submodule.span_le (p := M'.comap (((∏ x ∈ S, f x : ℕ) : 𝓞 E) • LinearMap.id))).2 (fun y hy => ?_) hx
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem f (Finset.mem_coe.1 hy)
  change ((∏ x ∈ S, f x : ℕ) : 𝓞 E) • y ∈ M'
  rw [hc, mul_comm, Nat.cast_mul, mul_smul]
  exact M'.smul_mem _ (hfx y (Submodule.subset_span hy))

theorem stdLat_fg (E : Type) [Field E] (n : ℕ) : (Formalism.L2.Col.stdLat E n).FG :=
  Submodule.fg_pi fun _ => by rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _

theorem stdAt_of_stdOver (D : D7) {p : ℕ} (hp : p.Prime) {n : ℕ} {N : Submodule (𝓞 D.host.E) (Sp D.host.E n)} (hN : N.FG)
    (h : StdOver p N) : StdAt D p ((recSeam D).lat N) := by
  obtain ⟨s, hs, h1⟩ := exists_denom hp hN (M' := Formalism.L2.Col.stdLat D.host.E n) fun P hP => (le_locP _ _).trans (h P hP).le
  obtain ⟨t, ht, h2⟩ := exists_denom hp (stdLat_fg D.host.E n) (M' := N) fun P hP => (le_locP _ _).trans (h P hP).ge
  have hl : ∀ x, x ∈ (recSeam D).lat N ↔ x ∈ N := fun x => GlobalTheory.SeamTransport.mem_lat (recSeam D) N x
  refine ⟨Formalism.L2.Col.stdLat D.host.E n, fun x => ?_, s * t, hs.mul_left ht, fun x hx => ?_, fun x hx => ?_⟩
  · simp only [Formalism.L2.Col.stdLat, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]
    exact forall_congr' fun k => ⟨fun ⟨y, hy⟩ => hy ▸ y.isIntegral_coe, fun hy => ⟨⟨_, hy⟩, rfl⟩⟩
  · have := h1 x ((hl x).1 hx)
    rw [Nat.cast_smul_eq_nsmul] at this ⊢
    rw [mul_comm, mul_smul]
    exact nsmul_mem this _
  · have := h2 x hx
    rw [Nat.cast_smul_eq_nsmul] at this ⊢
    rw [hl, mul_smul]
    exact nsmul_mem this _

variable {D : D7} {a b : ℕ}

theorem applyAt0_monomial (cD : D.what₂.Tau → ℂ) (G : TaylorLogMetric.VC D a b → ℂ) (m : TaylorLogMetric.Mono D a b) :
    GL3Theta.applyAt0 D (inLetters D cD (MvPolynomial.monomial m 1)) G =
      (m.prod fun k n => cD k.1 ^ n) * ((m.prod fun _ n => (n.factorial : ℂ)) * TaylorLogMetric.taylor D G m) := by
  classical
  have h : inLetters D cD (MvPolynomial.monomial m (1 : ℂ)) = MvPolynomial.monomial m (m.prod fun k n => cD k.1 ^ n) := by
    rw [inLetters, MvPolynomial.aeval_monomial, MvPolynomial.monomial_eq]
    simp only [mul_pow, Finsupp.prod_mul, map_one, one_mul, map_finsuppProd, map_pow]
  rw [h, GL3Theta.applyAt0, Finset.sum_subset MvPolynomial.support_monomial_subset, Finset.sum_singleton,
    MvPolynomial.coeff_monomial, if_pos rfl, mul_assoc]
  intro x _ hx
  rw [MvPolynomial.notMem_support_iff.1 hx, zero_mul, zero_mul]

end GlobalTheory.DatumJets.Transl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetInvMulFrameReadingCongruentOneModNormStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
open GlobalTheory.TopStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_inv_mul_frame_reading_congruent_one_mod_norm : ∀ {D : D7} {X : Fields} (s : Seam D X) {i : ℕ} {SB : Finset (HeightOneSpectrum (𝓞 X.E))}
    (fb : SB → GL (Fin (D.R.N i)) D.host.E) (dep : SB → ℕ) (P : SB), 1 ≤ dep P →
    ∀ (κ : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))
      (g C : Sp X.E (D.R.N i) ≃ₗ[X.E] Sp X.E (D.R.N i)), InFrame s fb dep P κ g →
    CongAt (F := D.host.F) (seamP s P.1) (dep P) (ratA D.host.F (seamGL s C)) →
    IntAtA (F := D.host.F) (seamP s P.1) (iA D.host.F D.host.E ((qOf (seamP s P.1) : D.host.E))⁻¹ *
      ((((Matrix.GeneralLinearGroup.det κ)⁻¹ : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E) *
        iA D.host.F D.host.E (s.iE ((LinearEquiv.det (g * C) : X.Eˣ) : X.E)) - 1)) := by
  first | exact @GlobalTheory.FramesDet.det_frame_mul_congAt | exact GlobalTheory.FramesDet.det_frame_mul_congAt | (intros; apply GlobalTheory.FramesDet.det_frame_mul_congAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsChartPointFramesMovedByLevelStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_chart_point_frames_moved_by_level : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (hi : t.m2 < D.R.m) (β : (St t.m2 hi.le).Ch) (κ : ((St t.m2 hi.le).K β).lev.U)
    (p : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) t.m2) (g : SB t μ → (Sp t.X.E (D.R.N t.m2) ≃ₗ[t.X.E] Sp t.X.E (D.R.N t.m2)))
    (z : SB t μ → t.X.K),
    (∀ P, A.midRel t.m2 hi β P (g P) (z P) ∧ InFrame t.seam (A.fb t.m2 hi.le β) (t.cst μ).D P κ.1 (g P)) →
    ∃ (q : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) t.m2) (κP : GLQ t.X.E (D.R.N t.m2) (rowSG t.Pr t.sel (t.tup μ)))
      (c : rowSG t.Pr t.sel (t.tup μ) → t.X.Kˣ),
      (∀ P, frsF t.sel (t.tup μ) q P = frsF t.sel (t.tup μ) p P * ((κP P)⁻¹).1) ∧
      (∀ P, GlobalTheory.TopLaw.LevAt ((t.idx μ).levG t.m2 (A.ib t.m2 hi β)) ((t.idx μ).levQ t.m2 (A.ib t.m2 hi β)) P (κP P) (c P)) ∧
      q.deco.1.N = p.deco.1.N ∧ q.deco.1.f = p.deco.1.f ∧
      (∀ P, ((c P : t.X.Kˣ) : t.X.K) * z P = 1) ∧
      (∀ P, rhoS t.Ch t.sel (t.tup μ) t.m2 P ((LinearEquiv.det ((κP P)⁻¹).1 : t.X.Eˣ) : t.X.E) =
        rhoS t.Ch t.sel (t.tup μ) t.m2 P ((LinearEquiv.det (g P) : t.X.Eˣ) : t.X.E)) ∧
      ∀ P, InFrame t.seam (A.fb t.m2 hi.le β) (t.cst μ).D P κ.1 ((κP P)⁻¹).1) := by
  first | exact @GlobalTheory.LevSrcPt.exists_pt_lev | exact GlobalTheory.LevSrcPt.exists_pt_lev | (intros; apply GlobalTheory.LevSrcPt.exists_pt_lev <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FramesOfRightTranslatePointPrincipalCongruenceStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
open GlobalTheory.TopStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frames_of_right_translate_point_principal_congruence : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D}
    {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
    (A : AdData t u μ St) (a : 𝓞 D.host.E) (j : ℕ) (hj : j ≤ D.R.m) (β : (St j hj).Ch) (x x₁ : UA D j hj)
    (κ : GL (Fin (D.R.N j)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)), x₁.1 = x.1 * κ →
    ∀ (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) j), IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
    ∀ (P : SB t μ) (g : GLint t.X.E (D.R.N j) P.1), InFrame t.seam (A.fb j hj β) (t.cst μ).D P κ g.1 →
    ∃ C : GLint t.X.E (D.R.N j) P.1, C ∈ GlobalTheory.TopStep.prinCong (D.R.N j) P.1 ((t.cst μ).D P) ∧
      CongAt (F := D.host.F) (seamP t.seam P.1) ((t.cst μ).D P) (ratA D.host.F (seamGL t.seam C.1)) ∧
      frsF t.sel (t.tup μ) p₁ P = frsF t.sel (t.tup μ) p P * (g * C).1 := by
  first | exact @GlobalTheory.LevFrames.frames_lev | exact GlobalTheory.LevFrames.frames_lev | (intros; apply GlobalTheory.LevFrames.frames_lev <;> assumption)
end

