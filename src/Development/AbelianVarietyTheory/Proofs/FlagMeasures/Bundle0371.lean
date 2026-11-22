import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.TopfBasis
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CuspidalSubspaceClosedRightTranslationStable
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommutantScalar
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0342
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0365
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0003
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0366
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0355
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0026
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.StepAnalyticConstantsP
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0014
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.CuspFrame
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0236
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0180
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0177
import Formalism.LocalToGlobal.Divisibility.DivisionCompatibleToSub2Indef2
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
import Formalism.LocalToGlobal.GroupLattices.JointServices.LevelOperatorFixesImage
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelHeightBoundSection
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0367
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0368
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsCompactKH
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsBesPosOfBesselTied

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsCuspHomOfCuspLowest
section
open MeasureTheory Formalism.MainNotions.S Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.RowLev NumberField Matrix
open scoped InnerProductSpace TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowLev

theorem isCuspHom_of_cusp_lowest : ∀ (B : RowsAut), (∀ v, IsDS (B.I.ε v) (B.lam v) (B.σ v)) → (∀ v, ‖B.w v‖ = 1) → ∀ A ∈ B.I.eHom B.σs B.μf B.fund B.R B.Re, B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext (A (B.tens B.w))) → IsCuspHom B.I A := by
  intro B hDS hw A hA hcusp
  obtain ⟨S, hS, hSc, hSR, -⟩ := GlobalTheory.CuspSubspace.cuspidal_closed_stable B
  obtain ⟨-, -, -, -, hirr⟩ :=
    GlobalTheory.HilbTensorRep.tensor_rep_rows B fun v => ⟨(hDS v).2.2.1, (hDS v).2.2.2.1⟩
  obtain ⟨T₀, hT₀, rfl⟩ := Submodule.mem_map.mp hA
  have hT₀' : ∀ g : B.I.Ginf, T₀.comp (B.σs g) = (B.R (g, 1)).comp T₀ := hT₀
  have hRe := (GlobalTheory.IdemProj.re_orth_proj B).2.1

  have hint : ∀ (g : B.I.Ginf) (u : B.Hs),
      B.Re (T₀ (B.σs g u)) = B.R (g, 1) (B.Re (T₀ u)) := by
    intro g u
    have h1 := congrArg (fun L => L u) (hT₀' g)
    have h2 := congrArg (fun L => L (T₀ u)) (hRe g)
    simp only [ContinuousLinearMap.comp_apply] at h1 h2
    rw [h1, h2]

  let P : Submodule ℂ B.Hs := S.comap (B.Re.comp T₀ : B.Hs →L[ℂ] B.I.L2 B.μf B.fund).toLinearMap
  have hPc : IsClosed (P : Set B.Hs) :=
    hSc.preimage (B.Re.comp T₀).continuous
  have hPs : ∀ g, ∀ u ∈ P, B.σs g u ∈ P := by
    intro g u hu
    change B.Re (T₀ (B.σs g u)) ∈ S
    rw [hint]
    exact hSR _ _ hu
  have hw0 : B.tens B.w ∈ P := by
    change B.Re (T₀ (B.tens B.w)) ∈ S
    rw [hS]
    simpa [ContinuousLinearMap.compL_apply] using hcusp
  have hne : B.tens B.w ≠ 0 := by
    intro h0
    have hn := GlobalTheory.HilbTensorRep.norm_tens B.tens_spec.1 B.w
    rw [h0, norm_zero] at hn
    simp [hw] at hn
  rcases hirr P hPc hPs with hbot | htop
  · exact absurd ((Submodule.mem_bot ℂ).mp (hbot ▸ hw0)) hne
  · intro u
    have hu : u ∈ P := htop ▸ Submodule.mem_top
    have : B.Re (T₀ u) ∈ S := hu
    simpa [ContinuousLinearMap.compL_apply] using (hS _).mp this

end GlobalTheory.RowLev
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeMultiplicityOneCountingHypothesesStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isKTypeOf_lowK_of_countHyp : ∀ (B : RowsAut) (Cg : ℝ) (n₀ : ℕ) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ), 8 ≤ n₀ → CountHyp B Cg n₀ d p q b → (∀ v, Formalism.MainNotions.S.IsKTypeOf (B.I.ε v) (B.σ v) (Formalism.QuantumDeterminants.lowK (B.I.ε v) (B.lam v)) (Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v))) := by
  first | exact @GlobalTheory.Dec.countHyp_isKTypeOf_lowKSub | exact GlobalTheory.Dec.countHyp_isKTypeOf_lowKSub | (intros; apply GlobalTheory.Dec.countHyp_isKTypeOf_lowKSub <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MovedTypeVectorsSpanFixedLatticeVectorModLevelStatement
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moved_type_vectors_span_fixed_lattice_vector_mod_level : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (c : ℕ) (p : VA X.B.I →ₗ[X.B.I.E ⊗[X.B.I.F] Af X.B.I.F] VA X.B.I), c ≡ 1 [MOD X.B.g] → (∀ y ∈ X.B.I.Lf, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p y ∈ X.B.I.Lf) → (∀ a, p (incl X.B.I (X.eR a)) = 0 ∧ p (incl X.B.I (X.fR a)) = 0) → p (incl X.B.I (X.zR u)) = 0 → ∀ v ∈ X.B.I.Lf, p v = v → InMod X.B.I X.B.g (Set.range (fun i => (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bw i)) ∪ Set.range (fun i => (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bwd i))) v := by
  first | exact @GlobalTheory.St.G.SpanMoved.span_moved | exact GlobalTheory.St.G.SpanMoved.span_moved | (intros; apply GlobalTheory.St.G.SpanMoved.span_moved <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NonGenericCorankOnePairsBoundOfSplitFiniteRealRoStatement
section
open Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic GlobalTheory.NGRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonGenericCorankOnePairsBound_of_splitFiniteRealRow : NGCut2P → RowNGP := by
  first | exact @GlobalTheory.NGRow.rowNG_of_cut2P | exact GlobalTheory.NGRow.rowNG_of_cut2P | (intros; apply GlobalTheory.NGRow.rowNG_of_cut2P <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PostOnMemGoodPart
section
noncomputable section

open Formalism.MainNotions.ArithmeticCylinders IsDedekindDomain MeasureTheory Formalism.MainNotions.S Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.RowLev NumberField Matrix
open scoped InnerProductSpace TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MultTranslate

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}
  {θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}

theorem isCuspFun_rTr {φ : GA D V → ℂ} (h : IsCuspFun V φ) (x : GA D V) : IsCuspFun V (rTr V x φ) := by
  intro r C hC μ 𝓕 hμ h𝓕 g
  simpa only [rTr, mul_assoc] using h r C hC μ 𝓕 hμ h𝓕 (g * x)

theorem isMultMap_rTr {J J' : Set (GA D V)} {χ χ' : GA D V → ℂ} {x : GA D V} (hx : x ∈ GfC V)
    (hJ : ∀ k ∈ J', x⁻¹ * k * x ∈ J ∧ χ' k = χ (x⁻¹ * k * x)) {T : MMap M} (h : IsMultMap θ M J χ T) :
    IsMultMap θ M J' χ' (postOn M (GlobalTheory.FinTranslate.rTrL V x) T) where
  aut v := GlobalTheory.FinTranslate.isAutFunSm_rTr θ V x hx _ (h.aut v)
  cusp v := isCuspFun_rTr (h.cusp v) x
  lev v k hk g := by
    change T v (g * k * x) = χ' k * T v (g * x)
    rw [(hJ k hk).2, ← h.lev v _ (hJ k hk).1]
    congr 1
    group
  equiv τ g hg v w hw := by
    funext y
    change T (Function.update v τ w) (y * x) = T v (y * atTau θ V τ g * x)
    rw [h.equiv τ g hg v w hw, mul_assoc,
      ← GlobalTheory.FinTranslate.comm_fin_real V hx (GlobalTheory.FinTranslate.atTau_mem θ V τ g), ← mul_assoc]
    rfl
  cont τ v y := h.cont τ v (y * x)

theorem postOn_mem_goodPart {J J' : Set (GA D V)} {χ χ' : GA D V → ℂ} {x : GA D V} (hx : x ∈ GfC V)
    (hJ : ∀ k ∈ J', x⁻¹ * k * x ∈ J ∧ χ' k = χ (x⁻¹ * k * x)) {L L' : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)}
    (hL : ∀ f, L' (rTr V x f) = rTr V x (L f)) {T : MMap M} (h : T ∈ goodPart θ M J χ L) :
    postOn M (GlobalTheory.FinTranslate.rTrL V x) T ∈ goodPart θ M J' χ' L' := by
  rw [mem_goodPart, GlobalTheory.MultMem.mem_mult_iff] at h ⊢
  refine ⟨isMultMap_rTr hx hJ h.1, fun v => ?_⟩
  change L' (rTr V x (T v)) = rTr V x (T v)
  rw [hL, h.2]

end GlobalTheory.MultTranslate

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PtBoundAndFarBoundAndDecGap
section
namespace GlobalTheory.Deep

theorem ptBound_and_farBound_and_decGap :
    GlobalTheory.Deep.PtBound ∧ GlobalTheory.Deep.FarBound ∧ GlobalTheory.DSId.DecGap :=
  have hd : GlobalTheory.DSId.DecGap :=
    GlobalTheory.DecGapBound.decGap_of_formulaGap GlobalTheory.Jet.FormGapFree.formulaGap
  have hp : GlobalTheory.Deep.PtBound := GlobalTheory.Deep.ptBound_of_decGap hd
  ⟨hp, GlobalTheory.FarTerms.farBound_of_ptBound hp, hd⟩

end GlobalTheory.Deep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowMapSurjectiveOfPrimitiveRows
section
open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Cx NumberField

namespace GlobalTheory

theorem rowMap_surjective_of_primitiveRows_alt : ∀ (D : D7) [IsTotallyComplex D.what₂.LL] (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (Ps : Subgroup G) (ψs : Ps →* D.what₂.LLˣ) (Zs : DefSub A3.fam3.amb3) (S0 : IndefData (A3.side3 P0 ψ0 Zs)) (S1 : IndefData (A3.side3 Ps ψs Zs)) (X0 : BaseLevelRowSide D) (Dc : DefCols (A3.side3 Ps ψs Zs)) (Sp : SPer Dc) (C : ColData Dc Sp S1) (NuC : ∀ u, Submodule (𝓞 D.what₂.LL) (Fin (Dc.a u) → D.what₂.LL)) (I : DivisionCompatibilityDataThreeSided D A3 P0 ψ0 Ps ψs Zs S0 S1 X0 Dc) (Dcf : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 Ps ψs Zs)) (Spf : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (s : ℕ), DivDef3 D A3 P0 ψ0 Ps ψs Zs S0 S1 X0 C NuC I → A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation (⟨P0, ψ0, Ps, ψs, Dcf, Spf, Zscf⟩ : Face3 D A3) → PrimRows3 R (⟨P0, ψ0, Ps, ψs, Dcf, Spf, Zscf⟩ : Face3 D A3) → (R.toCx3 (⟨P0, ψ0, Ps, ψs, Dcf, Spf, Zscf⟩ : Face3 D A3)).zs = Zs → HEq ((R.toCx3 (⟨P0, ψ0, Ps, ψs, Dcf, Spf, Zscf⟩ : Face3 D A3)).data (⟨P0, ψ0, Ps, ψs, Dcf, Spf, Zscf⟩ : Face3 D A3).cr true) S1 → (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤ := by
  intro D _ G _ _ Pl0 I0 T A3 Ks _ _ _ R P0 ψ0 Ps ψs Zs S0 S1 X0 Dc Sp C NuC I Dcf Spf Zscf s hD hOk hSep hW hP hzs hS1
  obtain ⟨h1, h2⟩ := GlobalTheory.T.primitiveRows_map_bijective_columnLevel D G Pl0 I0 T A3 Ks R ⟨P0, ψ0, Ps, ψs, Dcf, Spf, Zscf⟩ s hOk hSep hW hP Zs S1 hzs hS1
  exact GlobalTheory.T.V0_map_iota_eq_top_definite D G Pl0 I0 (List ℕ) T D.R.m A3 P0 ψ0 Ps ψs Zs S0 S1 X0 Dc Sp C NuC I hD ⟨s, hOk.ok2⟩ h1 h2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelHeightBoundSectionStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_height_bound_section : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ (g₀ : Mat k r) (β : Fin r → ℕ) (c : ℂ), inWb k r z → inWb k r z' → 0 < Tz k r z → IsNormal0 k r hj β c z z' g₀ → ∀ De R₀ : ℝ, DeOK k r z z' g₀ De → 1 ≤ R₀ → ∀ m ∈ UH (Hb k), ∀ (q : PSec k r j × (UToff β → ℂ)) (a : Fin r → ℝ), (∀ b, 0 < a b) → Sg2 k r z' (sEl k r j β q * (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)) ≤ R₀ → Sg k r z (g₀ * (sEl k r j β q * (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m))) ≤ R₀ → (∀ p, ‖q.2 p‖ ≤ R₀ ^ (2 * r) * De) ∧ (∀ b, eucl (m⁻¹ *ᵥ q.1.1 b) ≤ R₀ ^ (2 * r) * De) ∧ (∀ p, ‖q.1.2.1 p‖ ≤ 2 * r * (R₀ ^ (2 * r) * De) ^ 2) ∧ ∀ b, |q.1.2.2 b| ≤ 2 * r * (R₀ ^ (2 * r) * De) ^ 2 := by
  first | exact @GlobalTheory.Amp.SecBound.section_coord_le | exact GlobalTheory.Amp.SecBound.section_coord_le | (intros; apply GlobalTheory.Amp.SecBound.section_coord_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelOneVectorMeasurableOfCompactSupportStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_one_vector_measurable_of_compactSupport : GlobalTheory.GaussMean.OneVectorCc → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → SW1b2 F E σ M J := by
  first | exact @GlobalTheory.OneVecMeas.sw1b2_of_cc | exact GlobalTheory.OneVecMeas.sw1b2_of_cc | (intros; apply GlobalTheory.OneVecMeas.sw1b2_of_cc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SobolevInequalityAtIdentityBesselModelUnitaryGroStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sobolev_inequality_at_identity_besselModelUnitaryGroup : ∀ (k r : ℕ) (μG : Measure (Mt k r)), IsHaarOn (GG k r) μG → ∃ (C : ℝ) (Ws : List (List (Mat k r))) (K₀ : Set (Mt k r)), IsCompact K₀ ∧ (∀ ws ∈ Ws, ∀ X ∈ ws, InLieHpk k r X) ∧ ∀ (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (f : Mat k r → B), SmoothOnH (Hpk k r) f → ‖f 1‖ ^ 2 ≤ C * (Ws.map fun ws => ∫ x in K₀, ‖rdWord ws f (Matrix.of x)‖ ^ 2 ∂μG).sum := by
  first | exact @GlobalTheory.SobAtOne.sobolev_at_one_G | exact GlobalTheory.SobAtOne.sobolev_at_one_G | (intros; apply GlobalTheory.SobAtOne.sobolev_at_one_G <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoIntegralNormalisedPowPeakStatement
section
open MeasureTheory Matrix Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_integral_normalised_pow_smul_of_unique_peak : ∀ (X : Type) [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X), IsProbabilityMeasure μ → ∀ (K : Set X) (x₀ : X) (f : X → ℝ), IsCompact K → μ Kᶜ = 0 → x₀ ∈ K → (∀ U : Set X, IsOpen U → x₀ ∈ U → 0 < μ U) → Continuous f → f x₀ = 1 → (∀ x ∈ K, 0 ≤ f x ∧ f x ≤ 1) → (∀ U ∈ 𝓝 x₀, ∃ δ < 1, ∀ x ∈ K, x ∉ U → f x ≤ δ) → ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (F : X → E), ContinuousOn F K → Tendsto (fun m : ℕ => ∫ x, ((f x ^ m / ∫ y, f y ^ m ∂μ : ℝ) : ℂ) • F x ∂μ) atTop (𝓝 (F x₀)) := by
  first | exact @GlobalTheory.tendsto_integral_normalised_pow_peak | exact GlobalTheory.tendsto_integral_normalised_pow_peak | (intros; apply GlobalTheory.tendsto_integral_normalised_pow_peak <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ThetaKernelInvarianceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Per MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.IndefiniteRowSideFullHecke.BesselData (hA vecA actV)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_kernel_invariance : ∀ (D : D7) (X : ThetaX D) (T : ThetaTied D X) (Wl : WeilTied D X T) (L A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : FJDat L A B ι), 1 < A.rank → ∀ (Φ : X.Sch L A) (g : GA D A), ∀ n ∈ d.N, (∀ γ ∈ d.N, γ ∈ GQ B → d.theta Wl.ψ (omZ Wl L A Φ) (γ * n) g = d.theta Wl.ψ (omZ Wl L A Φ) n g) ∧ ∀ γ ∈ GQ A, ∀ δ, EmbRel B A ι δ γ → d.theta Wl.ψ (omZ Wl L A Φ) (δ * n * δ⁻¹) (γ * g) = d.theta Wl.ψ (omZ Wl L A Φ) n g := by
  first | exact @GlobalTheory.Per.ThetaAut.theta_aut | exact GlobalTheory.Per.ThetaAut.theta_aut | (intros; apply GlobalTheory.Per.ThetaAut.theta_aut <;> assumption)
end

