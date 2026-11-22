import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0056
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0180
import Development.AbelianVarietyTheory.Counterexamples.AnisotropicRankZero.WittSphericalSectionLeftInvariantRationalParabol
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1697
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1703
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordOperatorL2BoundPolynomial
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1465
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1466

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingSmulRightConj
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

noncomputable section

namespace GlobalTheory.CM.ActRight

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem bar_bar (H : Host E) (s : 𝓞 E) : H.bar (H.bar s) = s := by
  apply Subtype.ext
  show ((H.bar (H.bar s) : 𝓞 E) : E) = (s : E)
  rw [H.bar_eq, H.bar_eq]
  simp

theorem weilEq_act_adj (H : Host E) (K : Type) [Field K] [NumberField K] (σ₁ : K →+* ℂ)
    (A : PAT H (Sp (𝓞 K))) (a : 𝓞 E) :
    WeilEq A.t.PP.L (A.t.act.act (H.bar a)) (𝟙 _) A.t.PP.L (𝟙 _) (A.t.act.act a)
      (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  have hl : Out.Laws := GlobalTheory.abelianSchemeLaws_all.1
  have key := (GlobalTheory.PairingFibre.lamEq_weilEq_over_ring hl (𝓞 K) A.pol A.pol A.pol A.pol
    (A.t.act.act (H.bar a)) (𝟙 _) (𝟙 _) (A.t.act.act a) (A.t.act.hom _) inferInstance inferInstance
    (A.t.act.hom a) ℂ (σ₁.comp (algebraMap (𝓞 K) K))).1
  apply key
  unfold LamEq
  rw [Category.comp_id, Category.comp_id]
  have h := A.t.adj (H.bar a)
  rwa [bar_bar] at h

theorem weilEq_act_right : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K]
    [NumberField K] (σ₁ : K →+* ℂ) (A B : PAT H (Sp (𝓞 K))) (f g : A.t.G ⟶ B.t.G), IsMonHom f → IsMonHom g →
    ∀ r s : 𝓞 E,
    WeilEq B.t.PP.L f g A.t.PP.L (A.t.act.act r) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) →
    WeilEq B.t.PP.L f (A.t.act.act s ≫ g) A.t.PP.L (A.t.act.act (r * H.bar s)) (𝟙 _)
      (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  intro E _ _ _ H K _ _ σ₁ A B f g _ _ r s h n x y c hn hx hy
  haveI := A.t.act.hom s
  haveI := A.t.act.hom r
  have hy' : (y ≫ A.t.act.act s) ^ n = 1 := by rw [← MonObj.pow_comp, hy, MonObj.one_comp]
  have hx' : (x ≫ A.t.act.act r) ^ n = 1 := by rw [← MonObj.pow_comp, hx, MonObj.one_comp]
  have h1 := h n x (y ≫ A.t.act.act s) c hn hx hy'
  have h2 := weilEq_act_adj H K σ₁ A s n (x ≫ A.t.act.act r) y c hn hx' hy
  rw [← Category.assoc, h1, A.t.act.mul, ← Category.assoc, h2]
  simp only [Category.comp_id]

end GlobalTheory.CM.ActRight
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittDecompositionIsotropicFrameEisensteinDiction
section
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch GlobalTheory.ResidueEisenstein
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ResidueDictionary

theorem dict : ∀ (D : D7) (V V₀ : HSp D) (r : ℕ) (d : HypDec V V₀ (r + 1)), IsAniso V₀ → ∀ l : Lvl V, l.Good → HasIw d l.K → DataJ D.sp.cm.sig V.gram d.e d.e' l.L l.c (fun g => (iwAbs (absDet d) l.K g : ℝ)) ∧ (∃ T, IsRepsJ D.sp.cm.sig V.gram d.e T) ∧ ∀ T, IsRepsJ D.sp.cm.sig V.gram d.e T → ∀ (g : GA D V) (s : ℂ), sphericalEisensteinSeriesOnGroup d l.K g s = ∑' t : T, (((iwAbs (absDet d) l.K (t.1.1 * g) : ℝ≥0) : ℝ) : ℂ) ^ (s + ((V.rank : ℂ) - (r + 1)) / 2) := by
  intro D V V₀ r d hA l hl hIw
  have hsc : ∀ q : stab d, ScalesBy D.sp.cm.sig V.gram d.e (q : GA D V) (onX d q) := fun q => mul_jX d q
  have hstab := (GlobalTheory.EisCont.parFlag_stab_leftInv D V V₀ (r + 1) d).2.2.1
  have hiff : ∀ x : GA D V, (∃ β, ScalesBy D.sp.cm.sig V.gram d.e x β) ↔ x ∈ stab d := fun x =>
    ⟨fun ⟨β, e⟩ => (hstab x β e).1, fun hx => ⟨_, hsc ⟨x, hx⟩⟩⟩
  have htriv := GlobalTheory.Doubling.triv_of_isCompact (isClosed_stab d) (continuous_absDet d) hl.isCompact_K

  have hmk : ∀ t γ : GQ V, GlobalTheory.AutomorphicL2Unitary.mk ((stab d).subgroupOf (GQ V)) t = GlobalTheory.AutomorphicL2Unitary.mk ((stab d).subgroupOf (GQ V)) γ ↔
      ((γ * t⁻¹ : GQ V) : GA D V) ∈ stab d := fun t γ => by
    rw [GlobalTheory.AutomorphicL2Unitary.mk_eq_iff]
    constructor
    · rintro ⟨δ, hδ⟩
      have : (γ * t⁻¹ : GQ V) = δ := by rw [← hδ]; group
      rw [this]; exact δ.2
    · intro h
      exact ⟨⟨γ * t⁻¹, h⟩, by simp⟩
  refine ⟨⟨isCMExt_host D, GlobalTheory.Doubling.isHermND_gram V, GlobalTheory.WittFrameOfDec.isWittFrame_of_hypDec D V V₀ _ d hA, hl.1,
    fun g => ?_, fun p β e k hk => ?_⟩, ?_, fun T hT g s => ?_⟩
  · obtain ⟨q, k, hk, rfl⟩ := hIw g
    exact ⟨q, onX d q, hsc q, k, hk, rfl⟩
  · obtain ⟨hp, rfl⟩ := hstab p β e
    have := iwAbs_mul_of_triv htriv ⟨p, hp⟩ hk
    rw [this]
    rfl
  · refine ⟨Set.range fun q : GlobalTheory.AutomorphicL2Unitary.Quot ((stab d).subgroupOf (GQ V)) => (q.out : GQ V), fun γ => ?_⟩
    refine ⟨(GlobalTheory.AutomorphicL2Unitary.mk ((stab d).subgroupOf (GQ V)) γ).out, ⟨⟨_, rfl⟩, (hiff _).2 ((hmk _ _).1 (Quotient.out_eq _))⟩, ?_⟩
    rintro t' ⟨⟨q, rfl⟩, ht'⟩
    have e := (hmk q.out γ).2 ((hiff _).1 ht')
    have e2 : q = GlobalTheory.AutomorphicL2Unitary.mk ((stab d).subgroupOf (GQ V)) γ := (Quotient.out_eq q).symm.trans e
    subst e2
    rfl
  · have hbij : Function.Bijective fun t : T => GlobalTheory.AutomorphicL2Unitary.mk ((stab d).subgroupOf (GQ V)) (t.1 : GQ V) := by
      constructor
      · rintro ⟨t, ht⟩ ⟨t', ht'⟩ e
        have e' := (hmk _ _).1 e
        obtain ⟨u, -, hu⟩ := hT t'
        have h1 := hu t' ⟨ht', (hiff _).2 (by simp)⟩
        have h2 := hu t ⟨ht, (hiff _).2 e'⟩
        exact Subtype.ext (h2.trans h1.symm)
      · intro q
        induction q using Quotient.inductionOn with
        | h γ =>
          obtain ⟨t, ⟨ht, hs⟩, -⟩ := hT γ
          exact ⟨⟨t, ht⟩, (hmk _ _).2 ((hiff _).1 hs)⟩
    change cosetSum (stab d) (GQ V) (sphericalSectionIwasawa d l.K s) g = _
    rw [GlobalTheory.Eis.cosetSum_eq_tsum (GlobalTheory.AnisotropicResidueNonvanishing.witt_spherical_section_left_invariant_rational_parabolic d l hl hIw s) hbij g]
    refine tsum_congr fun t => ?_
    simp only [sphericalSectionIwasawa, npow, rhoH]
    congr 1
    push_cast
    ring

end GlobalTheory.ResidueDictionary
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameLeviNormalizesRadicalProperties
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT)
open Matrix

noncomputable section
namespace GlobalTheory.ResidueEisenstein.FrameLeviFacts

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem absE_det_of_scalesBy {k : ℕ} {X : Matrix (Fin n) (Fin k) E} {L : Matrix (Fin k) (Fin n) E} (hL : L * X = 1)
    {γ : GAd σ J} (hγ : γ ∈ ratPts σ J) {β : GL (Fin k) (AF F ⊗[F] E)} (e : ScalesBy σ J X γ β) :
    absE F E (Matrix.GeneralLinearGroup.det β) = 1 := by
  rw [← range_ratEmb] at hγ
  obtain ⟨γ0, rfl⟩ := hγ
  have hmat : (matHom _ σ J (ratEmb σ J γ0)).1 = (γ0.1.1 : Matrix (Fin n) (Fin n) E).map (inclR (F := F) (AF F)) := by
    ext s t; rfl
  have hL' : adMat F L * adMat F X = 1 := by
    rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]
  have hb : β.1 = (L * γ0.1.1 * X).map (inclR (F := F) (AF F)) := by
    have := congrArg (adMat F L * ·) e
    have h2 : adMat F L * (adMat F X * β.1) = β.1 := by rw [← Matrix.mul_assoc, hL', Matrix.one_mul]
    rw [h2, hmat] at this
    rw [← this]
    simp only [adMat, Matrix.map_mul, Matrix.mul_assoc]
  set c : E := (L * γ0.1.1 * X).det with hc
  have hd : (Matrix.GeneralLinearGroup.det β).1 = inclR (F := F) (AF F) c := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hb, hc, RingHom.map_det]
    rfl
  by_cases hc0 : c = 0
  · have : Subsingleton (AF F ⊗[F] E) := by
      have h01 := (Matrix.GeneralLinearGroup.det β).mul_inv
      rw [hd, hc0, map_zero, zero_mul] at h01
      exact subsingleton_of_zero_eq_one h01
    rw [Subsingleton.elim (Matrix.GeneralLinearGroup.det β) 1, map_one]
  · have := GlobalTheory.Doubling.absE_inclR (F := F) (E := E) (Units.mk0 c hc0)
    rwa [show (Units.map (inclR (F := F) (AF F)).toMonoidHom (Units.mk0 c hc0)) = Matrix.GeneralLinearGroup.det β from
      Units.ext (by simp [hd])] at this

end GlobalTheory.ResidueEisenstein.FrameLeviFacts

namespace GlobalTheory.ResidueEisenstein

open GlobalTheory.StdPar GlobalTheory.ResLine.LeviFacts in

theorem frame_levi_facts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → (∀ m ∈ GlobalTheory.StdPar.levi σ J X Y {Fin.last r}, ∀ u ∈ unipRad σ J X, m * u * m⁻¹ ∈ unipRad σ J X) ∧ (∀ g ∈ unipRad σ J X, g ∈ GlobalTheory.StdPar.levi σ J X Y {Fin.last r} → g = 1) ∧ (∀ u ∈ unipRad σ J X, ScalesBy σ J X u 1) ∧ (∀ m ∈ GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r}, ∃ β, ScalesBy σ J X m β ∧ absE F E (Matrix.GeneralLinearGroup.det β) = 1) ∧ (∀ γ ∈ ratPts σ J, ∀ β, ScalesBy σ J X γ β → absE F E (Matrix.GeneralLinearGroup.det β) = 1) ∧ GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r} ≤ GlobalTheory.StdPar.levi σ J X Y {Fin.last r} ∧ IsClosed ((GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r} : Subgroup (GAd σ J)) : Set (GAd σ J)) := by
  intro F E _ _ _ _ _ σ n J r X Y h hJ hW
  have hX : initCols X (Fin.last r) = X := rfl
  have hY : initCols Y (Fin.last r) = Y := rfl
  have hlev : ∀ m ∈ levi σ J X Y {Fin.last r}, m ∈ frameStab σ J X ⊤ ∧ m ∈ frameStab σ J Y ⊤ := fun m hm => by
    simp only [levi, Subgroup.mem_iInf] at hm
    exact hm _ (Finset.mem_singleton_self _)
  refine ⟨fun m hm u hu => conj_mem hW (Fin.last r) (hlev m hm).1 hu,
    fun g hg hm => eq_one h hJ hW (Fin.last r) hg (hlev g hm).2,
    fun u hu => (unipRad_fix hu).trans (by simp), fun m hm => ?_,
    fun γ hγ β e => FrameLeviFacts.absE_det_of_scalesBy (yx h hJ hW) hγ e, inf_le_left,
    (isClosed_levi {Fin.last r} h hJ hW).2⟩
  have h2 : m ∈ ⨅ k ∈ ({Fin.last r} : Finset (Fin (r + 1))),
      frameStab σ J (initCols X k) ((absE F E).comp Matrix.GeneralLinearGroup.det).ker := hm.2
  simp only [Subgroup.mem_iInf] at h2
  obtain ⟨B, hB, e⟩ := h2 _ (Finset.mem_singleton_self _)
  exact ⟨B, e, hB⟩

end GlobalTheory.ResidueEisenstein
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameRankLeAndExistsRationalSwap
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ResidueEisenstein.Swap

open GlobalTheory.ResLine.Swap

theorem two_mul_le_and_exists_ratPts_swap : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E),
    IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y →
    2 * (r + 1) ≤ n ∧ ∃ w ∈ ratPts σ J, (matHom _ σ J w).1 * adMat F Y = adMat F X ∧
      (matHom _ σ J w).1 * adMat F X = adMat F Y := by
  intro F E _ _ _ _ _ σ n J r X Y hσ hJ hW
  classical
  have hxx : Formalism.UG.cT (σ : E →+* E) X * J * X = 0 := hW.xx
  have hyy : Formalism.UG.cT (σ : E →+* E) Y * J * Y = 0 := hW.yy
  have hxy : Formalism.UG.cT (σ : E →+* E) X * J * Y = 1 := hW.xy
  have hJ' := cT_eq_of_isHermND hJ
  have hyx : Formalism.UG.cT (σ : E →+* E) Y * J * X = 1 := by
    have h := congrArg (Formalism.UG.cT (σ : E →+* E)) hxy
    rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul, cT_cT_of_isCMExt hσ, hJ', Formalism.UG.cT_one] at h
    simpa [Matrix.mul_assoc] using h
  refine ⟨?_, ?_⟩
  ·
    let f : ((Fin (r + 1) → E) × (Fin (r + 1) → E)) →ₗ[E] (Fin n → E) :=
      Y.mulVecLin.comp (LinearMap.fst E _ _) + X.mulVecLin.comp (LinearMap.snd E _ _)
    have hf : Function.Injective f := by
      intro p q hpq
      have hp : ∀ p : (Fin (r + 1) → E) × (Fin (r + 1) → E),
          (Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ f p = p.1 ∧ (Formalism.UG.cT (σ : E →+* E) Y * J) *ᵥ f p = p.2 := by
        intro p
        simp only [f, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply,
          Matrix.mulVecLin_apply, Matrix.mulVec_add, Matrix.mulVec_mulVec, hxx, hyy, hxy, hyx,
          Matrix.one_mulVec, Matrix.zero_mulVec, add_zero, zero_add]
        exact ⟨trivial, trivial⟩
      have h1 := hp p
      have h2 := hp q
      rw [hpq] at h1
      exact Prod.ext (h1.1.symm.trans h2.1) (h1.2.symm.trans h2.2)
    have h := LinearMap.finrank_le_finrank_of_injective hf
    simpa [Module.finrank_prod, two_mul] using h
  set u := X - Y with hu
  set v := Formalism.UG.cT (σ : E →+* E) u * J with hv
  have hvy : v * Y = 1 := by
    rw [hv, hu, cT_sub', Matrix.sub_mul, Matrix.sub_mul, hxy, hyy, sub_zero]
  have hvx : v * X = -1 := by
    rw [hv, hu, cT_sub', Matrix.sub_mul, Matrix.sub_mul, hxx, hyx, zero_sub]
  set w0 : Matrix (Fin n) (Fin n) E := 1 + u * v with hw0
  have hw0y : w0 * Y = X := by
    rw [hw0, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hvy, Matrix.mul_one, hu]; abel
  have hw0x : w0 * X = Y := by
    rw [hw0, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hvx, Matrix.mul_neg, Matrix.mul_one, hu]; abel
  have hw0u : w0 * u = -u := by
    rw [hu, Matrix.mul_sub, hw0y, hw0x]; abel
  have hsq : w0 * w0 = 1 := by
    conv_lhs => rw [show w0 * w0 = w0 * (1 + u * v) from rfl]
    rw [Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, hw0u, hw0, Matrix.neg_mul]; abel
  have hcw : Formalism.UG.cT (σ : E →+* E) w0 * J = J * w0 := by
    rw [hw0, cT_add', Formalism.UG.cT_one, Formalism.UG.cT_mul, hv, Formalism.UG.cT_mul, cT_cT_of_isCMExt hσ, hJ',
      Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one]
    simp only [Matrix.mul_assoc]
  have hunit : Formalism.UG.cT (σ : E →+* E) w0 * J * w0 = J := by
    rw [hcw, Matrix.mul_assoc, hsq, Matrix.mul_one]
  let U : GL (Fin n) E := ⟨w0, w0, hsq, hsq⟩
  have hU : U ∈ Formalism.UG.UJ (σ : E →+* E) J := hunit
  refine ⟨GlobalTheory.AdelicU.ratEmb σ J ⟨U, hU⟩, ?_, ?_, ?_⟩
  · rw [← GlobalTheory.AdelicU.range_ratEmb]; exact ⟨_, rfl⟩
  · change w0.map (inclR (F := F) (AF F)) * adMat F Y = adMat F X
    simp only [adMat]
    rw [← Matrix.map_mul, hw0y]
  · change w0.map (inclR (F := F) (AF F)) * adMat F X = adMat F Y
    simp only [adMat]
    rw [← Matrix.map_mul, hw0x]

end GlobalTheory.ResidueEisenstein.Swap

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameUnipotentRadicalClosedFundDomainMassOne
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ResidueEisenstein

theorem unipRad_frame_closed_mass_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → IsClosed (unipRad σ J X : Set (GAd σ J)) ∧ ∃ (ν : Measure (unipRad σ J X)) (DN : Set (unipRad σ J X)), ν.IsHaarMeasure ∧ IsFundamentalDomain ((ratPts σ J).subgroupOf (unipRad σ J X)) DN ν ∧ ν DN = 1 := by
  intro F E _ _ _ _ _ σ n J r X Y h hJ hW
  have e : X = X.submatrix id (Fin.castLE (le_refl (r + 1))) := by
    ext i j
    rfl
  have hC : GlobalTheory.UAut.IsIsoCols σ J X := e ▸ GlobalTheory.UAut.isIsoCols_of_isWittFrame hW (sigma_sigma h) hJ _
  haveI := GlobalTheory.UAut.locallyCompact_unipRad h hJ hC
  exact ⟨GlobalTheory.UAut.unipFlag_const (σ := σ) (J := J) X 0 ▸ GlobalTheory.UAut.isClosed_unipFlag hJ (sigma_sigma h) hC _,
    GlobalTheory.UAut.exists_mass_one (GlobalTheory.UAut.cocompact_unipRad h hJ hC)⟩

end GlobalTheory.ResidueEisenstein
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordOperatorL2BoundPolynomialStatement
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.word_operator_L2_bound_polynomial : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (T : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ((κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ)) (c : ℂ), ∀ Φ ∈ schA F κ, ∀ (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∀ P : ℕ, ∃ C : ℝ, ∀ ρ : ℝ, 1 ≤ ρ → ∀ zs : List ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)), zs.length ≤ P → (∀ ζ ∈ zs, ‖ζ‖ ≤ ρ) → ∫⁻ x, ‖wordR F T c zs Φ x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal (C * ρ ^ (2 * P)) := by
  first | exact @GlobalTheory.ArchDecay.wordR_L2_le | exact GlobalTheory.ArchDecay.wordR_L2_le | (intros; apply GlobalTheory.ArchDecay.wordR_L2_le <;> assumption)
end

