import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0496
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0502
import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.ImportsAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2262
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2310

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.WeilRepresentationLevelEqConductor
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.WeilLevel
theorem weil_representation_level_eq_conductor : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (f : WO S T → ℂ), _root_.GlobalTheory.FunPr.ThetaLocalInputs → IsWeilDatumO ψ S T χS χT om → IsThetaFunO ψ S T f → ∃ U : Subgroup (GA D T), IsOpen (U : Set (GA D T)) ∧ ∀ k ∈ U, k ∈ GfC T → om (1, k) f = f := by
  intro D ψ S T χS χT om f _ hW hf
  have hψ := hW.std
  obtain ⟨U, hUo, hU⟩ := hf.level
  obtain ⟨N, K, hNU, hKo, hAR, hKN, hKA⟩ := stab ψ S T hψ U hUo
  have hfN : ∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f := fun u hu h0 => hU u (hNU hu) h0
  obtain ⟨-, hcomp, -⟩ := GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T
  have hMV : ∀ k ∈ K, k ∈ GfC T → ∀ g, IsThetaFunO ψ S T g → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u g = g) →
      IsThetaFunO ψ S T (om (1, k) g) ∧ ∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u (om (1, k) g) = om (1, k) g := by
    intro k hk hkf g hg hgN
    refine ⟨hW.om_pres _ g hg, fun u hu hu0 => ?_⟩
    obtain ⟨h1, h2⟩ := hKN k⁻¹ (K.inv_mem hk) ((GfC T).inv_mem hkf) u hu hu0
    have e := hW.om_heis 1 k (actO S T 1 k⁻¹ u) g hg
    have e2 := GlobalTheory.AdelicLatMove.actO_actO_inv S T 1 k u
    rw [inv_one] at e2
    rw [e2, hgN _ h1 h2] at e
    exact e.symm
  have hMC : ∀ k ∈ K, k ∈ GfC T → ∀ w g, IsThetaFunO ψ S T g → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u g = g) →
      (∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T w l) = 1) →
      om (1, k) (heisO ψ S T w g) = heisO ψ S T w (om (1, k) g) := by
    intro k hk hkf w g hg hgN hw
    obtain ⟨d1, d2, d3⟩ := hKA k hk hkf w hw
    have e := hcomp w (actO S T 1 k w - w) (om (1, k) g)
    rw [(hMV k hk hkf g hg hgN).2 _ d1 d2, d3, one_smul, add_sub_cancel] at e
    rw [hW.om_heis 1 k w g hg, e]
  have hsc : ∀ k ∈ K, k ∈ GfC T → ∃ c : ℂ, ∀ g, IsThetaFunO ψ S T g → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u g = g) → om (1, k) g = c • g := by
    intro k hk hkf
    exact scalar_of_prod hψ N (om (1, k)) hAR (fun g hg hgN => (hMV k hk hkf g hg hgN).1) (hMC k hk hkf)
      (prodId ψ S T hψ N (om (1, k)) (hMV k hk hkf) (hMC k hk hkf)
        (fun μ 𝓕 hμ h𝓕 g hg _ => hW.om_unit μ 𝓕 hμ h𝓕 (1, k) g hg))
  by_cases hf0 : ∃ x₀, f x₀ ≠ 0
  · obtain ⟨x₀, hx₀⟩ := hf0
    let F : GA D T → ℂ := fun k => om (1, k) f x₀ / f x₀
    have hFc : Continuous F :=
      ((hW.om_cont f hf x₀).comp (continuous_const.prodMk continuous_id)).div_const _
    have hF1 : F 1 = 1 := by
      show om (1, 1) f x₀ / f x₀ = 1
      rw [show ((1, 1) : GA D S × GA D T) = 1 from rfl, map_one, Module.End.one_apply, div_self hx₀]
    have hFc' : ∀ k ∈ K, k ∈ GfC T → ∀ c : ℂ, (∀ g, IsThetaFunO ψ S T g → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u g = g) → om (1, k) g = c • g) →
        F k = c := by
      intro k hk hkf c hc
      show om (1, k) f x₀ / f x₀ = c
      rw [hc f hf hfN, Pi.smul_apply, smul_eq_mul, mul_div_assoc, div_self hx₀, mul_one]
    have hFm : ∀ a ∈ K, a ∈ GfC T → ∀ b ∈ K, b ∈ GfC T → F (a * b) = F a * F b := by
      intro a ha haf b hb hbf
      obtain ⟨ca, hca⟩ := hsc a ha haf
      obtain ⟨cb, hcb⟩ := hsc b hb hbf
      rw [hFc' a ha haf ca hca, hFc' b hb hbf cb hcb]
      show om (1, a * b) f x₀ / f x₀ = ca * cb
      rw [show ((1, a * b) : GA D S × GA D T) = (1, a) * (1, b) by simp, map_mul, Module.End.mul_apply,
        hcb f hf hfN, map_smul, hca f hf hfN, smul_smul, Pi.smul_apply, smul_eq_mul, mul_div_assoc, div_self hx₀,
        mul_one, mul_comm]
    obtain ⟨V, hVo, hV⟩ := openKer T K hKo F hFc hF1 hFm
    refine ⟨V ⊓ K, hVo.inter hKo, fun k hk hkf => ?_⟩
    obtain ⟨c, hc⟩ := hsc k hk.2 hkf
    have h1 : c = 1 := by rw [← hFc' k hk.2 hkf c hc]; exact hV k hk.1 hkf
    rw [hc f hf hfN, h1, one_smul]
  · push_neg at hf0
    have : f = 0 := funext hf0
    refine ⟨⊤, isOpen_univ, fun k _ _ => ?_⟩
    rw [this, map_zero]
end GlobalTheory.WeilLevel
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_weil_level_eq_conductor : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (f : WO S T → ℂ), _root_.GlobalTheory.FunPr.ThetaLocalInputs → IsWeilDatumO ψ S T χS χT om → IsThetaFunO ψ S T f → ∃ U : Subgroup (GA D T), IsOpen (U : Set (GA D T)) ∧ ∀ k ∈ U, k ∈ GfC T → om (1, k) f = f := by
  first | exact @_root_.GlobalTheory.WeilLevel.weil_representation_level_eq_conductor | exact _root_.GlobalTheory.WeilLevel.weil_representation_level_eq_conductor | (intros; apply _root_.GlobalTheory.WeilLevel.weil_representation_level_eq_conductor <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.WildAKer
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem UpperTheory.WildA.ker_wild_ramification_map :
    ∃ C1 : ℝ, 0 < C1 ∧ ∀ (D : D7) (large₂ : SizeData₂ D) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m)
          (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F →
          ∀ (ch : Choice R) (CF : ℝ), ch.Is → ch.AtScale CF large₂.sc.b → ch.FieldOK → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.NormSum.Inp D →
          DictAt ch → ∀ (S : Finset ℕ) (δ : ℕ → ℝ), GlobalTheory.NormSum.Letters D S δ →
          ∀ (t : T) (p : Pair T), DefPair D.R.m p → ∀ (k : ℕ) (d : FinDatum ch.G t p), 0 < k → IsCosetDatum k d → d.z = 1 →
          d.P = locPl ch.G t → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big), ch.S.Z.IsRatAt d x y →
          ∀ (w : PlL D) (l : ℕ), l.Prime → (l : 𝓞 D.what₂.LL) ∈ w.asIdeal → Away ch.G t w →
          ∀ (a : ℝ) (v : VV ℂ (wt ch.G p.small)), InLat _ w a (latAt ch.S.toGridChoice p.small x) v →
            InLat _ w (a + (vw w ((l : ℕ) : D.what₂.LL) : ℝ) * C1 *
                GlobalTheory.SumSize.TopInt.kerLoss ch.G δ C1 large₂.sc.b p.small p.big l (padicValNat l k))
              (latAt ch.S.toGridChoice p.big y) (ch.S.Z.kkMap 1 d x y v) := by
  refine ⟨1, one_pos, ?_⟩
  intro D large₂ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch CF _ _ _ _ hI hDict S δ hL t p hp k d hk hd hz hP x y hR w l hl hw hA a v hv
  have hn := DefPair.nodes hp
  obtain ⟨k', hk', hd', hle, hsp⟩ := UpperTheory.WildA.depth large₂ hS.size d hP w l hl hw hA k hk hd
  obtain ⟨r, U, hU, e, hx⟩ := UpperTheory.WildA.toStd ch.S.toGridChoice p.small hn.1 l hl x
  obtain ⟨r', U', hU', e', hy⟩ := UpperTheory.WildA.toStd ch.S.toGridChoice p.big hn.2 l hl y
  have hmv := UpperTheory.WildA.move ch.S.Z hS.core.lev t p hp d x r y r' U U' hU hU'
  have hR' : ch.S.Z.IsRatAt d (r * x) (r' * y) := by
    intro i j
    have := UpperTheory.WildA.ratMove D _ _ _ _ _ _ hmv (fun i j => by
      have := hR i j
      rwa [Normal.kkIn, LinearMap.toMatrix_apply] at this) i j
    rwa [Normal.kkIn, LinearMap.toMatrix_apply]
  have h1 := UpperTheory.WildA.kerStd D large₂ Γ Pl0 T A Ks R F hS ch hI hDict S δ hL t p hp k' d hk' hd' hz hP _ _ hR' w l hl hw hsp hx hy
    large₂.sc.b
  have h2 := (UpperTheory.WildA.latMove D _ w a _ U v).2 hv
  rw [← e] at h2
  have h3 := UpperTheory.WildA.matLat D _ _ w l hl hw _ _ hx hy _ _ h1 a _ h2
  have h4 := LinearMap.congr_fun hmv v
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at h4
  rw [h4, e'] at h3
  refine GlobalTheory.SumSize.TopInt.inLat_mono ((UpperTheory.WildA.latMove D _ w _ _ U' _).1 h3) ?_
  rw [mul_one]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (GlobalTheory.SumSize.TopInt.kerLoss_mono _ _ _ _ _ _ _ hle)
    (by exact_mod_cast GlobalTheory.SumSize.TopInt.vw_natCast_nonneg w l))
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.WittTowerConstantRatioEqBottom
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.SqTower
theorem theta_tower_bottom_constant_ratio : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW) (B B' WW₁ : HSp D) (Y : Tri T B B' WW₁) (c : T → ℂ),
      IsBottomTri W i j X → GlobalTheory.SqTower.IsStageC W i j 0 0 Y → Y.IsConst W.ψ W.θ c → ∃ v : T → ℂ,
        X.IsConst W.ψ W.θ (fun t => v t * c t) ∧
        ∀ t, v t ≠ 0 ∧ ∃ ζ : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (Qn G t) ζ ∧ v t = D.what₂.embLL ζ * v μ₀ := by
  intro _ _ _
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ hμ G => ?_⟩⟩
  intro W S _ hN i j A A' WW X B B' WW₁ Y c hX hY hc
  obtain ⟨Y₁, hY₁, hc₁⟩ := GlobalTheory.T.definiteBottom_stage_transport_same_constants W i j X Y hX hY
  obtain ⟨Z₁, v₁, hZ₁, e1, e2, e3, hv₁, hc₂⟩ := GlobalTheory.T.definiteBottom_lattice_change_constants_awayUnit μ₀ hμ W S hN i j X Y₁ hX hY₁
  obtain ⟨Z₂, v₂, hZ₂, f1, f2, f3, f4, f5, f6, hv₂, hc₃⟩ := GlobalTheory.T.definiteBottom_framesChange_stageZero μ₀ hμ W S hN i j X Z₁ hX hZ₁ e1 e2 e3
  obtain ⟨κ, hκ, hX'⟩ := GlobalTheory.T.definiteBottom_tower_constants_differ_by_factor W i j X Z₂ hX hZ₂ f1 f2 f3 f4 f5 f6 _ (hc₃ _ (hc₂ _ (hc₁ c hc)))
  refine ⟨fun t => κ * (v₂ t * v₁ t), ?_, fun t => ?_⟩
  · convert hX' using 2 with t
    ring
  · obtain ⟨h1, ζ₁, u₁, q₁⟩ := hv₁ t
    obtain ⟨h2, ζ₂, u₂, q₂⟩ := hv₂ t
    refine ⟨mul_ne_zero hκ (mul_ne_zero h2 h1), ζ₂ * ζ₁, u₂.mul u₁, ?_⟩
    show κ * (v₂ t * v₁ t) = _ * (κ * (v₂ μ₀ * v₁ μ₀))
    rw [q₁, q₂, map_mul]
    ring
end GlobalTheory.SqTower
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_tower_constant_ratio_eq_bottom : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW) (B B' WW₁ : HSp D) (Y : Tri T B B' WW₁) (c : T → ℂ),
      IsBottomTri W i j X → GlobalTheory.SqTower.IsStageC W i j 0 0 Y → Y.IsConst W.ψ W.θ c → ∃ v : T → ℂ,
        X.IsConst W.ψ W.θ (fun t => v t * c t) ∧
        ∀ t, v t ≠ 0 ∧ ∃ ζ : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (Qn G t) ζ ∧ v t = D.what₂.embLL ζ * v μ₀ := by
  first | exact @_root_.GlobalTheory.SqTower.theta_tower_bottom_constant_ratio | exact _root_.GlobalTheory.SqTower.theta_tower_bottom_constant_ratio | (intros; apply _root_.GlobalTheory.SqTower.theta_tower_bottom_constant_ratio <;> assumption)
end
end

