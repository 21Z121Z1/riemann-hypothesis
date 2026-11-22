import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0072
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0022
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishingStatement
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0071
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1444
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1876
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1714
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1916
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1936
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFinitePureTensors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedTensorSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0229
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1919
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0050
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1932
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1809
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1873
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1914
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1796
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1938
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1933
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1129
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1760

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceConjMemArithmeticGroup
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
open IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RepConv

theorem hat_cong {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} (L : Set (Fin n → E))
    (γ : Matrix (Fin n) (Fin n) E) (M : ℕ) (h : ∀ x ∈ L, ∃ y ∈ L, γ.mulVec x - x = M • y) :
    ∀ z ∈ GlobalTheory.AdLat.hat F L, ∃ y ∈ GlobalTheory.AdLat.hat F L,
      (γ.map (inclR (F := F) (FiniteAdeleRing (𝓞 F) F))).mulVec z - z = M • y := by
  intro z hz
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    obtain ⟨y, hy, e⟩ := h x hx
    refine ⟨fun i => a ⊗ₜ y i, AddSubgroup.subset_closure ⟨a, ha, y, hy, rfl⟩, ?_⟩
    funext i
    have e1 := congrFun e i
    simp only [Pi.sub_apply, Pi.smul_apply] at e1 ⊢
    rw [← TensorProduct.tmul_smul, ← e1, TensorProduct.tmul_sub]
    congr 1
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [inclR]
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨y, hy, e⟩ := ha
    obtain ⟨y', hy', e'⟩ := hb
    refine ⟨y + y', add_mem hy hy', ?_⟩
    rw [Matrix.mulVec_add, smul_add, ← e, ← e']
    abel
  | neg a _ ha =>
    obtain ⟨y, hy, e⟩ := ha
    refine ⟨-y, neg_mem hy, ?_⟩
    rw [Matrix.mulVec_neg, smul_neg, ← e]
    abel

theorem archM_mul' {D : D7} (V : HSp D) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (a b : GA D V) :
    archM V θ (a * b) = archM V θ a * archM V θ b := by
  unfold archM
  rw [map_mul, Units.val_mul, Matrix.map_mul]

theorem archM_one' {D : D7} (V : HSp D) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) :
    archM V θ 1 = 1 := by
  unfold archM
  rw [map_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem exists_rat {D : D7} (V : HSp D) (γ' : GL (Fin V.rank) D.host.E)
    (h : ∀ x y, herm (-(V.gram)ᵀ) (γ'.1.mulVec x) (γ'.1.mulVec y) =
      herm (-(V.gram)ᵀ) x y) :
    ∃ γ₀ ∈ GQ V, (finHom V γ₀).1 = γ'.1.map (inclR (Af D.host.F)) ∧
      ∀ (τ : D.host.E →+* ℂ) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ), Formalism.MainNotions.StandardLattice.IsInfEmb τ θ →
        archM V θ γ₀ = γ'.1.map τ := by
  have hU : γ' ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram := by
    show Formalism.UG.cT _ γ'.1 * V.gram * γ'.1 = V.gram
    refine Matrix.ext fun a b => ?_
    have := h (Pi.single b 1) (Pi.single a 1)
    have hc : ∀ x, cc x = (D.sp.cm.sig : D.host.E →+* D.host.E) x := fun _ => rfl
    simp only [herm, Matrix.mulVec_single_one, hc, Matrix.neg_apply, Matrix.transpose_apply, Matrix.col_apply] at this
    have h2 : ∑ x, ∑ y, (Pi.single b 1 : Fin V.rank → D.host.E) x * -V.gram y x *
        (D.sp.cm.sig : D.host.E →+* D.host.E) ((Pi.single a 1 : Fin V.rank → D.host.E) y) = -V.gram a b := by
      rw [Finset.sum_eq_single b, Finset.sum_eq_single a]
      · simp
      · intro j _ hj; simp [hj]
      · simp
      · intro j _ hj; simp [hj]
      · simp
    rw [h2] at this
    rw [← neg_inj, ← this]
    simp only [Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hR : Formalism.UG.bc (inclR (AF D.host.F)) γ' ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
    have hU' : Formalism.UG.cT _ γ'.1 * V.gram * γ'.1 = V.gram := hU
    have := congrArg (fun m => Matrix.map m (inclR (F := D.host.F) (AF D.host.F))) hU'
    simp only [Matrix.map_mul] at this
    rw [GlobalTheory.UnitaryGlue.cT_map (inclR (F := D.host.F) (AF D.host.F)) (D.sp.cm.sig : D.host.E →+* D.host.E)
      (sigR (AF D.host.F) D.sp.cm.sig) (fun _ => rfl)] at this
    exact this
  let γ₀ : GA D V := ⟨_, hR⟩
  have h1 : (matHom V γ₀).1 = γ'.1.map (inclR (AF D.host.F)) := rfl
  refine ⟨γ₀, Subgroup.mem_subgroupOf.2 ⟨γ', hU, rfl⟩, ?_, fun τ θ hθ => ?_⟩
  · rw [← GlobalTheory.UnitaryGlue.map_map_inclR (sndA D.host.F), ← h1]; rfl
  · have hinc : (γ'.1.map (inclR (Ainf D.host.F))).map θ = γ'.1.map τ := by
      ext i j
      exact hθ.1 _
    rw [← hinc, ← GlobalTheory.UnitaryGlue.map_map_inclR (fstA D.host.F), ← h1]; rfl

theorem map_eq_of_frames {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} (γ1 γ2 γ3 : GL (Fin r) E)
    (x b : Frame Ψ r) (τ : Ψ) (u : Matrix (Fin r) (Fin r) ℂ) (hdet : (mat x τ).det ≠ 0)
    (hb : mat b τ = (mat x τ)⁻¹ * u * mat x τ) (e : lact γ1 x = lact γ2 (rmul (lact γ3 x) b)) :
    ((γ2 * γ3)⁻¹ * γ1).1.map τ.1 = u := by
  have hu : IsUnit (mat x τ).det := Ne.isUnit hdet
  have e5 : γ1.1.map τ.1 * mat x τ = γ2.1.map τ.1 * ((γ3.1.map τ.1 * mat x τ) * mat b τ) := congrFun e τ
  rw [hb] at e5
  have e6 : γ1.1.map τ.1 = (γ2 * γ3).1.map τ.1 * u := by
    have := congrArg (· * (mat x τ)⁻¹) e5
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one,
      Matrix.mul_nonsing_inv_cancel_left _ _ hu] at this
    rw [this, Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]
  rw [Units.val_mul, Matrix.map_mul, e6, ← Matrix.mul_assoc, ← Matrix.map_mul, Units.inv_mul,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

theorem hat_cong_conj {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} (L L' : Set (Fin n → E))
    (g : GL (Fin n) (GlobalTheory.AdLat.RA F E))
    (hhat : (GlobalTheory.AdLat.hat F L' : Set (Fin n → GlobalTheory.AdLat.RA F E)) = g.1.mulVec '' (GlobalTheory.AdLat.hat F L))
    (γ : Matrix (Fin n) (Fin n) E) (M : ℕ) (h : ∀ x ∈ L', ∃ y ∈ L', γ.mulVec x - x = M • y) :
    ∀ z ∈ GlobalTheory.AdLat.hat F L, ∃ y ∈ GlobalTheory.AdLat.hat F L,
      ((g⁻¹).1 * γ.map (inclR (F := F) (FiniteAdeleRing (𝓞 F) F)) * g.1).mulVec z - z = M • y := by
  intro z hz
  have hz1 : g.1.mulVec z ∈ (GlobalTheory.AdLat.hat F L' : Set (Fin n → GlobalTheory.AdLat.RA F E)) := by
    rw [hhat]; exact ⟨z, hz, rfl⟩
  obtain ⟨y, hy, e⟩ := hat_cong L' γ M h _ hz1
  have hy1 : y ∈ (GlobalTheory.AdLat.hat F L' : Set (Fin n → GlobalTheory.AdLat.RA F E)) := hy
  rw [hhat] at hy1
  obtain ⟨y', hy', rfl⟩ := hy1
  refine ⟨y', hy', ?_⟩
  have e2 := congrArg ((g⁻¹).1.mulVec) e
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at e2
  rw [← e2, Matrix.mul_assoc]

set_option maxHeartbeats 400000 in

theorem conj_mem_of_cong : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (Comp : Type) (X : Comp → Data D.host.E V.rank)
    (dict : GA D V → Σ k, Frame (X k).Ψ V.rank) (Kf : Subgroup (GA D V))
    (th : ∀ c, (X c).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : ℕ) (x0 : ∀ c, Frame (X c).Ψ V.rank),
    IsLevelK V M Kf → (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) → DictIsUnif V dict Kf th rfl →
    (∀ c, x0 c ∈ (X c).dom) →
    (∀ g, ∀ h ∈ GinfC V, ∃ γ' ∈ (X (dict g).1).Γ,
      dict (g * h) = ⟨(dict g).1, lact γ' (rmul (dict g).2 (archMat V th rfl x0 h (dict g).1))⟩) →
    (∀ c, (X c).Gm = -(V.gram)ᵀ) →
    ∀ (k : Comp) (g : GA D V), dict g = ⟨k, x0 k⟩ →
    ∀ Λk : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E),
      (Λk : Set (Fin V.rank → D.host.E)) = GlobalTheory.AdLat.latOf (maximalRealSubfield D.host.E) (finHom V g).1
        (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) →
      (GlobalTheory.AdLat.hat (maximalRealSubfield D.host.E) (Λk : Set (Fin V.rank → D.host.E)) :
                   Set (Fin V.rank → GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)) =
        ((finHom V g).1 : Matrix (Fin V.rank) (Fin V.rank) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)).mulVec ''
          (GlobalTheory.AdLat.hat (maximalRealSubfield D.host.E) (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E))) →
    ∀ γ' : GL (Fin V.rank) D.host.E,
      (IsUStab (-(V.gram)ᵀ) Λk γ' ∧ ∀ x ∈ Λk, ∃ y ∈ Λk, (γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E).mulVec x - x = M • y) →
      ∃ γ ∈ (X k).Γ, ∀ (τ : D.host.E →+* ℂ) (hτ : τ ∈ (X k).Ψ),
        archM V (th k ⟨τ, hτ⟩) g * (γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map τ =
          (γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map τ * archM V (th k ⟨τ, hτ⟩) g := by
  intro D V Comp X dict Kf th M x0 hK hth hd hx0 hact _ k g hg Λk _ hhat γ' hγ'
  haveI : IsTotallyReal D.host.F := D.sp.cm.totReal
  obtain ⟨γ₀, hQ, hfin, harch⟩ := exists_rat V γ' hγ'.1.1
  obtain ⟨hinj, -, -, hsur⟩ := (GlobalTheory.T.adelicUnitary_exists_with_prescribed_parts D V).2 (X k).Ψ (th k) (X k).cmType (hth k)
  obtain ⟨h, hh, hhw⟩ := hsur (fun τ => archM V (th k τ) (g⁻¹ * γ₀ * g)) (fun τ =>
    GlobalTheory.MarkUnit.infMat_unitary D.sp.cm.sig V.gram τ.1
      (fun x => IsCMField.complexEmbedding_complexConj D.host.E τ.1 x) (th k τ) (hth k τ) _)
  have hκ1 : ∀ τ, archM V (th k τ) (g⁻¹ * γ₀ * g * h⁻¹) = 1 := fun τ => by
    rw [archM_mul', ← hhw, ← archM_mul', mul_inv_cancel, archM_one']
  have hh1 : finHom V h = 1 := hh
  have hκ : g⁻¹ * γ₀ * g * h⁻¹ ∈ Kf := by
    refine (hK _).2 ⟨hinj _ hκ1, ?_⟩
    have hf : (finHom V (g⁻¹ * γ₀ * g * h⁻¹)).1 =
        ((finHom V g)⁻¹).1 * γ'.1.map (inclR (Af D.host.F)) * (finHom V g).1 := by
      rw [← hfin]
      simp only [map_mul, map_inv, hh1, inv_one, mul_one, Units.val_mul]
    rw [(GlobalTheory.Member.latHat_eq_hat_and_gram D V).1, hf]
    exact hat_cong_conj (F := D.host.F) (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E))
      (Λk : Set (Fin V.rank → D.host.E)) (finHom V g) hhat γ'.1 M hγ'.2
  obtain ⟨γ1, hγ1, e1⟩ := hd.1 γ₀ hQ g
  obtain ⟨γ3, hγ3, e3⟩ := hd.2.1 _ hκ g
  obtain ⟨γ2, hγ2, e2⟩ := hact (g * (g⁻¹ * γ₀ * g * h⁻¹)) h hh
  have hgrp : g * (g⁻¹ * γ₀ * g * h⁻¹) * h = γ₀ * g := by group
  rw [hgrp, e1] at e2
  rw [e3] at e2 hγ2
  rw [hg] at e2 hγ1 hγ2 hγ3
  have e4 : lact γ1 (x0 k) = lact γ2 (rmul (lact γ3 (x0 k)) (archMat V th rfl x0 h k)) :=
    eq_of_heq (Sigma.mk.inj e2).2
  refine ⟨(γ2 * γ3)⁻¹ * γ1, mul_mem (inv_mem (mul_mem hγ2 hγ3)) hγ1, fun τ hτ => ?_⟩
  have hb : mat (archMat V th rfl x0 h k) ⟨τ, hτ⟩ =
      (mat (x0 k) ⟨τ, hτ⟩)⁻¹ * archM V (th k ⟨τ, hτ⟩) h * mat (x0 k) ⟨τ, hτ⟩ := by
    have hre : ∀ u : Matrix (Fin V.rank) (Fin V.rank) ℂ,
        Matrix.reindex (finCongr (rfl : V.rank = V.rank)) (finCongr (rfl : V.rank = V.rank)) u = u := fun u => by
      simp
    rw [← hre (archM V (th k ⟨τ, hτ⟩) h)]
    rfl
  have e6 := map_eq_of_frames γ1 γ2 γ3 (x0 k) _ ⟨τ, hτ⟩ _ (hx0 k ⟨τ, hτ⟩).1 hb e4
  rw [e6, hhw, ← harch τ _ (hth k ⟨τ, hτ⟩), ← archM_mul', ← archM_mul']
  congr 1
  group

end GlobalTheory.RepConv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedTensorLocalOperators
section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval
namespace GlobalTheory.EvKer

theorem ker_trivial : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (e : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (ei : SInf F κ →L[ℂ] SInf F κ)
    (ev : ∀ v : Pl F, ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ),
    (∀ v, ∀ φ ∈ SB (κ → Fv F v), ev v φ ∈ SB (κ → Fv F v)) →
    (∀ᶠ v in cofinite, ev v (stdInd F κ v) = stdInd F κ v) →
    (∀ (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ), (∀ v, φ v ∈ SB (κ → Fv F v)) →
      (∀ᶠ v in cofinite, φ v = stdInd F κ v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    Set.InjOn e (schA F κ : Set ((κ → AF F) → ℂ)) →
    ∀ v, ∀ ψ ∈ SB (κ → Fv F v), ev v ψ = 0 → ψ = 0 := by
  intro F _ _ κ _ e ei ev hSB hstd hpure hinj v ψ hψ hev
  classical
  by_contra hne
  obtain ⟨f₀, hf₀⟩ := GlobalTheory.TensUniq.exists_sInf_ne_zero F κ
  set φ : ∀ w : Pl F, (κ → Fv F w) → ℂ := Function.update (fun w => stdInd F κ w) v ψ with hφdef
  have hφSB : ∀ w, φ w ∈ SB (κ → Fv F w) := by
    intro w
    by_cases h : w = v
    · subst h; simpa [φ] using hψ
    · simpa [φ, Function.update_of_ne h, stdInd] using GlobalTheory.StdVacuum.indicator_mem_SB (κ := κ) w
  have hφev : ∀ᶠ w in cofinite, φ w = stdInd F κ w := by
    exact (Filter.eventually_cofinite_ne v).mono fun w h => by simp [φ, Function.update_of_ne h]
  have hmem : pure f₀ φ ∈ schA F κ := GlobalTheory.TensUniq.pure_mem_schA f₀ φ hφSB (by simpa [stdInd] using hφev)
  have hcomp : (fun w => ev w (φ w)) = Function.update (fun w => ev w (stdInd F κ w)) v 0 := by
    funext w
    by_cases h : w = v
    · subst h; simp [φ, hev]
    · simp [φ, Function.update_of_ne h]
  have hevstd : ∀ᶠ w in cofinite, (fun w => ev w (stdInd F κ w)) w =
      {x : κ → Fv F w | ∀ i, x i ∈ HeightOneSpectrum.adicCompletionIntegers F w}.indicator 1 := by
    simpa [stdInd] using hstd
  obtain ⟨r, -, hr⟩ := GlobalTheory.PureFactor.exists_rest_factor v (ei f₀) _ hevstd
  have hzero : e (pure f₀ φ) = 0 := by
    rw [hpure f₀ φ hφSB hφev, hcomp, ← hr 0]
    funext x
    simp [tens]
  have h0 : pure f₀ φ = 0 := hinj hmem (Submodule.zero_mem _) (by rw [hzero, map_zero])
  have hall : ∀ w, φ w ≠ 0 := by
    intro w
    by_cases h : w = v
    · subst h; simpa [φ] using hne
    · simp only [φ, Function.update_of_ne h]
      intro h1
      have := congrFun h1 0
      simp [stdInd, Set.indicator, zero_mem] at this
  have := GlobalTheory.EvInj.eq_zero_of_pure_eq_zero f₀ φ hall (by simpa [stdInd] using hφev) h0
  exact hf₀ (by rw [this]; rfl)

end GlobalTheory.EvKer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedTensorSchwartzStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restricted_tensor_schwartz : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ → AF F) → ℂ) (vac vac₁ : ∀ v : Pl F, (κ → Fv F v) → ℂ)
    (ei : SInf F κ →L[ℂ] SInf F κ) (ev : ∀ v : Pl F, ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ),
    (∀ v, vac v ∈ SB (κ → Fv F v)) →
    (∀ᶠ v in Filter.cofinite, vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    (∀ᶠ v in Filter.cofinite, vac₁ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    (∀ v, ev v (vac v) = vac₁ v) → (∀ v, ∀ φ ∈ SB (κ → Fv F v), ev v φ ∈ SB (κ → Fv F v)) →
    (∀ f φ, (∀ v, φ v ∈ SB (κ → Fv F v)) → (∀ᶠ v in Filter.cofinite, φ v = vac v) →
      e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    (∃ c : ℝ, 0 ≤ c ∧ ∀ μ : @Measure (κ → mixedEmbedding.mixedSpace F) (borel _),
        @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∀ f f' : SInf F κ,
          @integral _ ℂ _ _ (borel _) μ (fun x => ei f x * starRingEnd ℂ (ei f' x)) =
            (c : ℂ) * @integral _ ℂ _ _ (borel _) μ (fun x => f x * starRingEnd ℂ (f' x))) →
    (∀ v : Pl F, ∃ c : ℝ, 0 ≤ c ∧ ∀ μ : @Measure (κ → Fv F v) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
        ∀ φ ∈ SB (κ → Fv F v), ∀ φ' ∈ SB (κ → Fv F v),
          @integral _ ℂ _ _ (borel _) μ (fun x => ev v φ x * starRingEnd ℂ (ev v φ' x)) =
            (c : ℂ) * @integral _ ℂ _ _ (borel _) μ (fun x => φ x * starRingEnd ℂ (φ' x))) →
    ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ c : ℝ≥0∞, ∀ Φ ∈ schA F κ, ∫⁻ x, ‖e Φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := by
  first | exact @GlobalTheory.TensorSquareIntegral.exists_const_tensor | exact GlobalTheory.TensorSquareIntegral.exists_const_tensor | (intros; apply GlobalTheory.TensorSquareIntegral.exists_const_tensor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatBlockScaledHasLatticeDepth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
open GlobalTheory.PureMatch GlobalTheory.SquareFlipReach ValuativeRel

namespace GlobalTheory.PurityDepth

theorem hasDepth_scaled : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A' C : Type) [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C] (ϖ : kˣ) (P : Finset C) (Ψ : Matrix A' C k → ℂ),
    Ψ ∈ GlobalTheory.WeilM.SB (Matrix A' C k) → IsUnif ϖ → ∃ M : ℕ, ∀ n, 2 * M ≤ n →
      HasDepth ϖ n (blockLat ϖ n P) (fun Y => Ψ (Y * diagonal (fun col => if col ∈ P then ((ϖ ^ M : kˣ) : k) else (((ϖ ^ M)⁻¹ : kˣ) : k)))) := by
  intro k _ _ _ _ A' C _ _ _ _ ϖ P Ψ hΨ hϖ
  have hΨ' : Ψ ∈ GlobalTheory.SplitWeil.SB (Matrix A' C k) := hΨ
  have hϖ' : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ := fun x => by rw [hϖ, le_uniformizer_iff]
  obtain ⟨Λ, hΛ, hinv⟩ := GlobalTheory.RootEx.sb_matrix_exists_isOpen_addSubgroup k A' C Ψ hΨ'
  let f : (A' × C → k) → Matrix A' C k := fun z => Matrix.of fun i j => z (i, j)
  have hf : Continuous f := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact continuous_apply (i, j)
  have hΛn : f ⁻¹' (Λ : Set (Matrix A' C k)) ∈ nhds (0 : A' × C → k) :=
    (hΛ.preimage hf).mem_nhds (by
      show f 0 ∈ Λ
      exact (show f 0 = 0 from rfl) ▸ Λ.zero_mem)
  have hc : IsCompact (tsupport Ψ) := hΨ.2
  have h1 : ∀ q : A' × C, ∀ᶠ e : ℕ in Filter.atTop,
      (fun x : Matrix A' C k => x q.1 q.2) '' tsupport Ψ ⊆ GlobalTheory.SplitWeil.cball (ϖ ^ e)⁻¹ := fun q =>
    GlobalTheory.AdaptedExp.eventually_subset_cball hϖ' (hc.image (by fun_prop))
  obtain ⟨M, hM1, hM2⟩ := ((Filter.eventually_all.2 h1).and (GlobalTheory.AdaptedExp.eventually_box_subset hϖ' hΛn)).exists
  refine ⟨M, fun n hn => ?_⟩

  set w := valuation k (ϖ : k) with hw
  have hw1 : w ≤ 1 := hϖ.mem
  set u := valuation k ((ϖ ^ M : kˣ) : k) with hu
  have hu0 : 0 < u := zero_lt_iff.2 (by simp [hu])
  have huw : u = w ^ M := by rw [hu, Units.val_pow_eq_pow_val, map_pow]
  have hinvu : valuation k (((ϖ ^ M)⁻¹ : kˣ) : k) = u⁻¹ := by
    rw [Units.val_inv_eq_inv_val, map_inv₀]
  have hn' : valuation k ((ϖ ^ n : kˣ) : k) ≤ u * u := by
    rw [Units.val_pow_eq_pow_val, map_pow, huw, ← pow_add, ← two_mul]
    exact pow_le_pow_right_of_le_one' hw1 hn
  have hd : ∀ (X : Matrix A' C k) i j, (X * diagonal (fun col => if col ∈ P then ((ϖ ^ M : kˣ) : k)
      else (((ϖ ^ M)⁻¹ : kˣ) : k))) i j = X i j * (if j ∈ P then ((ϖ ^ M : kˣ) : k) else (((ϖ ^ M)⁻¹ : kˣ) : k)) :=
    fun X i j => mul_diagonal _ _ _ _
  refine ⟨fun Y hY => ?_, fun Y Z hZ => ?_⟩
  · by_contra hne
    apply hY
    have hs := subset_tsupport _ hne
    have he : ∀ i j, valuation k (Y i j * (if j ∈ P then ((ϖ ^ M : kˣ) : k) else (((ϖ ^ M)⁻¹ : kˣ) : k))) ≤ u⁻¹ :=
      fun i j => by
        have := hM1 (i, j) ⟨_, hs, rfl⟩
        simpa only [GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq, hd, hinvu] using this
    refine GlobalTheory.SplitFlip.FourierDepth.mem_matLat_blockLat.2 ⟨fun i j hj => ?_, fun i j hj => ?_⟩
    · have h := he i j
      rw [if_pos hj, map_mul, ← hu] at h
      rw [Valuation.mem_integer_iff, map_mul]
      calc valuation k ((ϖ ^ n : kˣ) : k) * valuation k (Y i j) ≤ u * u * valuation k (Y i j) :=
            mul_le_mul_left hn' _
        _ = u * (valuation k (Y i j) * u) := by rw [mul_assoc, mul_comm u (valuation k (Y i j))]
        _ ≤ u * u⁻¹ := mul_le_mul_right h _
        _ = 1 := mul_inv_cancel₀ hu0.ne'
    · have h := he i j
      rw [if_neg hj, map_mul, hinvu] at h
      rw [Valuation.mem_integer_iff]
      have := mul_le_mul_left h u
      rwa [mul_assoc, inv_mul_cancel₀ hu0.ne', mul_one] at this
  · obtain ⟨h1, h2⟩ := GlobalTheory.SplitFlip.FourierDepth.mem_matLat_smul_blockLat.1 hZ
    show Ψ ((Y + Z) * _) = Ψ (Y * _)
    rw [Matrix.add_mul]
    refine hinv _ _ ?_
    refine hM2 (fun q => (Z * diagonal (fun col => if col ∈ P then ((ϖ ^ M : kˣ) : k)
      else (((ϖ ^ M)⁻¹ : kˣ) : k))) q.1 q.2) ?_
    unfold GlobalTheory.StepData.box
    intro q
    beta_reduce
    rw [hd, map_mul, ← hu]
    by_cases hj : q.2 ∈ P
    · rw [if_pos hj, ← hu]
      calc valuation k (Z q.1 q.2) * u ≤ 1 * u := mul_le_mul_left (h1 q.1 q.2 hj) _
        _ = u := one_mul u
    · rw [if_neg hj, hinvu]
      calc valuation k (Z q.1 q.2) * u⁻¹ ≤ u * u * u⁻¹ := mul_le_mul_left ((h2 q.1 q.2 hj).trans hn') _
        _ = u := by rw [mul_assoc, mul_inv_cancel₀ hu0.ne', mul_one]

end GlobalTheory.PurityDepth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatPartialEvaluationStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LatVac
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_bruhat_partial_evaluation : ∀ (k : Type) [TopologicalSpace k] [T2Space k] (κ κ' : Type) [Fintype κ] [Fintype κ'], ∀ f ∈ SB (κ ⊕ κ' → k),
    (∀ x₁ : κ → k, (fun x₂ : κ' → k => f (Sum.elim x₁ x₂)) ∈ SB (κ' → k)) ∧
      ∀ l : ((κ' → k) → ℂ) →ₗ[ℂ] ℂ, (fun x₁ : κ → k => l fun x₂ => f (Sum.elim x₁ x₂)) ∈ SB (κ → k) := by
  first | exact @GlobalTheory.SliceSB.slice_mem | exact GlobalTheory.SliceSB.slice_mem | (intros; apply GlobalTheory.SliceSB.slice_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatRestrictedProductChar
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.WeylTwist

open GlobalTheory.SympChange GlobalTheory.HeisSchA

theorem pure_mul_psi : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → (∀ᶠ v in cofinite, PsiUnr ψ v) →
    ∀ (κ : Type) [Fintype κ] (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) (y : κ → AF F),
    (∀ v, φ v ∈ SB (κ → Fv F v)) → (∀ᶠ v in cofinite, φ v = GlobalTheory.SympChange.indO v) →
    (∀ v, (fun z => φ v z * GlobalTheory.LatVac.psiAt ψ v (z ⬝ᵥ fun i => evFin F v (y i))) ∈ SB (κ → Fv F v)) ∧
    (∀ᶠ v in cofinite, (fun z => φ v z * GlobalTheory.LatVac.psiAt ψ v (z ⬝ᵥ fun i => evFin F v (y i))) = GlobalTheory.SympChange.indO v) ∧
    ∀ x, pure f φ x * ψ (x ⬝ᵥ y) = (f (fun i => evI F (x i)) * eInf (fun i => evI F (x i)) (fun i => evI F (y i))) *
      ∏ᶠ v, (φ v (fun i => evFin F v (x i)) *
        GlobalTheory.LatVac.psiAt ψ v ((fun i => evFin F v (x i)) ⬝ᵥ fun i => evFin F v (y i))) := by
  intro F _ _ ψ hψ hunr κ _ f φ y hφ hφO
  have hlc := GlobalTheory.SympUnip.psiAt_isLocallyConstant ψ hψ.1
  have hyint : ∀ᶠ v : Pl F in cofinite, ∀ i, evFin F v (y i) ∈ v.adicCompletionIntegers F :=
    eventually_all.2 fun i => GlobalTheory.SympUnip.eventually_evFin (y i)
  refine ⟨fun v => ⟨(hφ v).1.mul ((hlc v).comp_continuous (continuous_id.dotProduct continuous_const)),
    (hφ v).2.mul_right⟩, ?_, fun x => ?_⟩
  · filter_upwards [hunr, hφO, hyint] with v hv hφv hy
    funext z
    rw [hφv]
    by_cases hz : z ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F}
    · have hm : (z ⬝ᵥ fun i => evFin F v (y i)) ∈ v.adicCompletionIntegers F :=
        sum_mem fun i _ => mul_mem (hz i) (hy i)
      have h4 := (hv 1).2 (one_mem _) _ hm
      rw [one_mul] at h4
      rw [GlobalTheory.LatVac.psiAt_apply, h4, mul_one]
    · rw [indO, Set.indicator_of_notMem hz, zero_mul]
  · have hfin : (Function.mulSupport fun v : Pl F => φ v fun i => evFin F v (x i)).Finite := by
      have h3 : ∀ᶠ v : Pl F in cofinite, ∀ i, evFin F v (x i) ∈ v.adicCompletionIntegers F :=
        eventually_all.2 fun i => GlobalTheory.SympUnip.eventually_evFin (x i)
      have h4 : ∀ᶠ v : Pl F in cofinite, (φ v fun i => evFin F v (x i)) = 1 := by
        filter_upwards [hφO, h3] with v hv h3
        rw [hv, indO, Set.indicator_of_mem (show _ ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from h3)]
        rfl
      exact h4
    have hq : ∀ v : Pl F, evalV F v (p2 (x ⬝ᵥ y)) =
        (fun i => evFin F v (x i)) ⬝ᵥ fun i => evFin F v (y i) := fun v =>
      RingHom.map_dotProduct (evFin F v : AF F →+* Fv F v) x y
    obtain ⟨hs, hp⟩ := GlobalTheory.SympUnip.finChar_eq_finprod ψ hψ.1 (p2 (x ⬝ᵥ y))
    simp only [hq] at hs hp
    let q : AF F →+* mixedEmbedding.mixedSpace F := (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp p1
    have h3 : ψ (mk (p1 (x ⬝ᵥ y)) 0) = eInf (fun i => evI F (x i)) (fun i => evI F (y i)) := by
      have e1 : evI F (mk (p1 (x ⬝ᵥ y)) 0) = (fun i => evI F (x i)) ⬝ᵥ fun i => evI F (y i) :=
        RingHom.map_dotProduct q x y
      rw [hψ.2.2 _ (at_mk _), e1, eInf]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
    rw [finprod_mul_distrib hfin hs, ← hp, map_eq_mul ψ (x ⬝ᵥ y), h3]
    ring

end GlobalTheory.WeylTwist

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeCentraliserClassNumberFiniteBorelStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.TorCls
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.similitudeCentraliser_classNumber_finite_borel : ∀ (D : Type) [Ring D] [Algebra ℚ D] [FiniteDimensional ℚ D] (σ : D →+* Dᵐᵒᵖ) (β y : D) (p : ℕ) [Fact p.Prime], letI : TopologicalSpace (AfP p ⊗[ℚ] D) := moduleTopology (AfP p) (AfP p ⊗[ℚ] D); letI : TopologicalSpace (ℚ_[p] ⊗[ℚ] D) := moduleTopology ℚ_[p] (ℚ_[p] ⊗[ℚ] D); ∀ U : Subgroup (((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ)), (∃ O : Set (((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ)), IsOpen O ∧ 1 ∈ O ∧ ∀ z ∈ O, GlobalTheory.CentCls.TC D σ β y (AfP p) z.1 → GlobalTheory.CentCls.TC D σ β y ℚ_[p] z.2 → z ∈ U) → ∃ S : Finset (((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ)), ∀ z : ((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ), GlobalTheory.CentCls.TC D σ β y (AfP p) z.1 → GlobalTheory.CentCls.TC D σ β y ℚ_[p] z.2 → ∃ γ : Dˣ × ℚˣ, (γ.1 : D) * β * (σ (γ.1 : D)).unop = algebraMap ℚ D (γ.2 : ℚ) * β ∧ Commute (γ.1 : D) y ∧ ∃ s ∈ S, ∃ u ∈ U, z = GlobalTheory.TorCls.dg D p γ * s * u := by
  first | (exact @GlobalTheory.CentCls.Fin.classes_finite) | (exact GlobalTheory.CentCls.Fin.classes_finite) | (intros; apply GlobalTheory.CentCls.Fin.classes_finite  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardCharacterAlmostUnramifiedStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_character_almost_unramified : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    (∀ᶠ v in cofinite, PsiUnr ψ v) ∧ ∀ v : Pl F, ∃ x, psiLoc ψ v x ≠ 1 := by
  first | exact @GlobalTheory.PsiStdCond.psi_std_conductor | exact GlobalTheory.PsiStdCond.psi_std_conductor | (intros; apply GlobalTheory.PsiStdCond.psi_std_conductor <;> assumption)
end

