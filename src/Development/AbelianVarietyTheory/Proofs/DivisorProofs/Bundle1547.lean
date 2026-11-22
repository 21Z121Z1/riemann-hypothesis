import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1446
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1444
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1479
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAHEqOfMemRatPts
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1521
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0026
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfM
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0038
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1530
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0769
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfK
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KaUnfoldPfA
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KronHolPsiStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0039
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EnormPowLeInvMeasureMulLintegralBall
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0023
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0218
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0088
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.IsQProjOverOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralFundamentalSetConjFiniteIndexSubgroup
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeRel
section
noncomputable section

namespace GlobalTheory.UPel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {F : Type} [Field F] [NumberField F] [IsCMField F]

structure IntSim (D : Datum F) (p : ℕ) where
  c : ℕ
  k : ℕ
  c_cop : c.Coprime p
  k_cop : k.Coprime p
  g : ℕ → D.La →ₗ[𝓞 F] D.La
  compat : ∀ n m : ℕ, (n * m).Coprime p → ∀ a, ∃ b, g (n * m) a - g n a = n • b
  sim : ∀ n : ℕ, n.Coprime p → ∃ u : ℤ, IsCoprime u (n : ℤ) ∧
    ∀ a b, (n : ℤ) ∣ D.EF (g n a) (g n b) - c * u * D.EF a b
  onto : ∀ n : ℕ, n.Coprime p → ∀ a, ∃ b d, g n b = k • a + n • d

namespace IntSim

variable {D : Datum F} {p : ℕ}

def ofLinear (g : D.La →ₗ[𝓞 F] D.La) (c k : ℕ) (hc : c.Coprime p) (hk : k.Coprime p)
    (hg : ∀ x y, D.EF (g x) (g y) = c * D.EF x y) (hon : ∀ x, ∃ y, g y = k • x) : IntSim D p where
  c := c
  k := k
  c_cop := hc
  k_cop := hk
  g _ := g
  compat n m _ a := ⟨0, by simp⟩
  sim n _ := ⟨1, isCoprime_one_left, fun a b => by rw [hg]; simp⟩
  onto n _ a := let ⟨y, hy⟩ := hon a; ⟨y, 0, by simp [hy]⟩

def scalar (D : Datum F) (m : ℕ) (hm : m.Coprime p) : IntSim D p :=
  ofLinear (D := D) (m • LinearMap.id) (m ^ 2) m (Nat.Coprime.pow_left 2 hm) hm
    (fun x y => by simp [LinearMap.map_smul_of_tower]; ring) (fun x => ⟨x, by simp⟩)

def one (D : Datum F) (p : ℕ) : IntSim D p :=
  ofLinear (D := D) (p := p) LinearMap.id 1 1 (Nat.coprime_one_left p) (Nat.coprime_one_left p) (by simp) (fun x => ⟨x, by simp⟩)

def comp (g₁ g₂ : IntSim D p) : IntSim D p where
  c := g₁.c * g₂.c
  k := g₁.k * g₂.k
  c_cop := Nat.Coprime.mul g₁.c_cop g₂.c_cop
  k_cop := Nat.Coprime.mul g₁.k_cop g₂.k_cop
  g n := g₁.g n ∘ₗ g₂.g n
  compat n m h a := by
    obtain ⟨b₂, hb₂⟩ := g₂.compat n m h a
    obtain ⟨b₁, hb₁⟩ := g₁.compat n m h (g₂.g (n * m) a)
    refine ⟨b₁ + g₁.g n b₂, ?_⟩
    have e : g₂.g n a = g₂.g (n * m) a - n • b₂ := by rw [← hb₂]; abel
    simp only [LinearMap.comp_apply]
    rw [e, map_sub, map_nsmul, smul_add, ← hb₁]
    abel
  sim n h := by
    obtain ⟨u₁, hu₁, h₁⟩ := g₁.sim n h
    obtain ⟨u₂, hu₂, h₂⟩ := g₂.sim n h
    refine ⟨u₁ * u₂, hu₁.mul_left hu₂, fun a b => ?_⟩
    have := dvd_add (h₁ (g₂.g n a) (g₂.g n b)) (Dvd.dvd.mul_left (h₂ a b) (g₁.c * u₁))
    simp only [LinearMap.comp_apply]
    obtain ⟨q, hq⟩ := this
    exact ⟨q, by push_cast; linear_combination hq⟩
  onto n h a := by
    obtain ⟨b₁, d₁, h₁⟩ := g₁.onto n h a
    obtain ⟨b₂, d₂, h₂⟩ := g₂.onto n h b₁
    refine ⟨b₂, g₂.k • d₁ + g₁.g n d₂, ?_⟩
    simp only [LinearMap.comp_apply]
    rw [h₂, map_add, map_nsmul, map_nsmul, h₁]
    module

theorem scalar_k (D : Datum F) (m : ℕ) (hm : m.Coprime p) : (scalar D m hm).k = m := rfl

theorem scalar_c (D : Datum F) (m : ℕ) (hm : m.Coprime p) : (scalar D m hm).c = m ^ 2 := rfl

end IntSim

variable {S : Scheme.{0}}

def HeckeRel {D : Datum F} {p N N' : ℕ} (g : IntSim D p) {s : S ⟶ Sp (D.OEp p)} (o : Obj D p N' s)
    (o' : Obj D p N s) (ψ : o.A ⟶ o'.A) : Prop :=
  IsMonHom ψ ∧ (∀ a, o.act.act a ≫ ψ = ψ ≫ o'.act.act a) ∧ Etale ψ.left ∧
    (∀ x, o'.eta x = o.eta ((N' / (N * g.k)) • g.g N' x) ≫ ψ) ∧
    (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (t : Over.mk x ⟶ o.A),
      t ≫ ψ = 1 ↔ ∃ a, t = toUnit _ ≫ o.eta ((N' / g.k) • g.g N' a)) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (n : ℕ), 0 < n → n.Coprime p →
      ∀ (P Q : Over.mk x ⟶ o.A), P ^ n = 1 → Q ^ n = 1 → ∀ ζ : kˣ,
        Out.WeilIs o'.A o'.PP.L n (P ≫ ψ) (Q ≫ ψ) (unitOn ζ) →
          Out.WeilIs o.A o.PP.L ((g.k ^ 2 * n : ℕ) : ℤ) P Q (unitOn (ζ ^ g.c))

def IsHecke {D : Datum F} {p N N' : ℕ} (g : IntSim D p) (M' : IntModel D p N') (M : IntModel D p N)
    (π : M'.X ⟶ M.X) : Prop :=
  π ≫ M.s = M'.s ∧ ∃ (o : Obj D p N M'.s) (ψ : M'.univ.A ⟶ o.A), HeckeRel g M'.univ o ψ ∧ Nonempty (ObjMap o M.univ π)

end GlobalTheory.UPel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightFunctionCompactRightTranslate
section
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.EisRes

open scoped Pointwise

theorem iwaHt_mul_le_of_isCompact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), HidaSetting σ J X Y L a h →
    ∀ C : Set (GAd σ J), IsCompact C → ∃ K : ℝ, 0 ≤ K ∧ ∀ γ g, g ∈ C → h (γ * g) ≤ K * h γ := by
  intro F E _ _ _ _ _ σ n J r X Y L a h hS C hC
  have hcont : Continuous h := GlobalTheory.T.eisenstein_setting_height_continuous F E σ n J r X Y L a h hS
  obtain ⟨hCM, -, -, -, -, hAd, hI⟩ := hS
  haveI := hAd.lat
  have hK : IsCompact ((levelAll σ J L a : Set (GAd σ J)) * C) :=
    (GlobalTheory.Doubling.isCompact_levelAll hCM J L a).mul hC
  obtain ⟨K0, hK0⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max K0 0, le_max_right _ _, fun γ g hg => ?_⟩
  obtain ⟨p, l, hp, k, hk, rfl⟩ := hI.1 γ
  obtain ⟨p', l', hp', k', hk', hkg⟩ := hI.1 (k * g)
  have e1 : p * k * g = (p * p') * k' := by rw [mul_assoc, hkg, mul_assoc]
  have hpp : (matHom _ σ J (p * p')).1 * adMat F (col0 X) = (l * l').1 • adMat F (col0 X) := by
    rw [map_mul, Units.val_mul, Matrix.mul_assoc, hp', Matrix.mul_smul, hp, smul_smul, Units.val_mul, mul_comm (l' : AF F ⊗[F] E)]
  have h1 : h (p * k * g) = absE F E (l * l') := by rw [e1]; exact hI.2 _ _ hpp _ hk'
  have h2 : h (p * k) = absE F E l := hI.2 _ _ hp _ hk
  have h3 : h (k * g) = absE F E l' := by rw [hkg]; exact hI.2 _ _ hp' _ hk'
  have hb : h (k * g) ≤ max K0 0 :=
    ((le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hK0 _ (Set.mul_mem_mul hk hg))).trans (le_max_left _ _)
  rw [h1, h2, map_mul, NNReal.coe_mul, mul_comm (absE F E l : ℝ)]
  exact mul_le_mul_of_nonneg_right (h3 ▸ hb) (NNReal.coe_nonneg _)

end GlobalTheory.EisRes
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantExtensionMeasurableContDiffOnChart
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.PeakWeightSmooth

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem lact_inv_lact (X : Data E r) (γ : GL (Fin r) E) (y : Frame X.Ψ r) : lact γ⁻¹ (lact γ y) = y := by
  rw [KU.lact_lact X, inv_mul_cancel, KU.lact_one X]

theorem lact_lact_inv (X : Data E r) (γ : GL (Fin r) E) (y : Frame X.Ψ r) : lact γ (lact γ⁻¹ y) = y := by
  rw [KU.lact_lact X, mul_inv_cancel, KU.lact_one X]

theorem local_form (X : Data E r) (x : Frame X.Ψ r) (hx : IsOrth X x) (ρ R : ℝ) (η : V (nd X) → ℝ)
    (ψ : Frame X.Ψ r → ℝ) (hρR : ρ < R) (hR : ∀ z : V (nd X), ‖z‖ ≤ R → z ∈ OmF X x)
    (hψ : ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, ∀ z : V (nd X), ‖z‖ ≤ R → ψ (lact γ (rmul (cpt X x z) b)) = η z)
    (h0 : ∀ y, (¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ ρ ∧ y = lact γ (rmul (cpt X x z) b)) →
      ψ y = 0)
    (hloc : ∀ y ∈ X.dom, (¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ ρ ∧
      y = lact γ (rmul (cpt X x z) b)) → ∀ᶠ y' in 𝓝 y, ¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X),
        ‖z‖ ≤ ρ ∧ y' = lact γ (rmul (cpt X x z) b))
    {y : Frame X.Ψ r} (hy : y ∈ X.dom) :
    (∀ᶠ y' in 𝓝 y, ψ y' = 0) ∨
    ∃ (γ : GL (Fin r) E) (zOf : Frame X.Ψ r → V (nd X)) (U : Set (Frame X.Ψ r)),
      IsOpen U ∧ lact γ⁻¹ y ∈ U ∧ DifferentiableOn ℂ zOf U ∧
      ∀ᶠ y' in 𝓝 y, ψ y' = η (zOf (lact γ⁻¹ y')) := by
  by_cases hS : ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ ρ ∧ y = lact γ (rmul (cpt X x z) b)
  · right
    obtain ⟨γ, hγ, b, hb, z, hz, rfl⟩ := hS
    obtain ⟨Δ, zOf, bOf, hΔ, -, hzd, -, hsplit, hinv⟩ := lu_holds r X x hx
    have hUo : IsOpen {w | w ∈ X.dom ∧ Δ w ≠ 0} :=
      (IW.isOpen_dom X).inter (isOpen_ne_fun hΔ.continuous continuous_const)
    have hzO : z ∈ OmF X x := hR z (hz.trans hρR.le)
    have hmem : lact γ⁻¹ (lact γ (rmul (cpt X x z) b)) ∈ {w | w ∈ X.dom ∧ Δ w ≠ 0} := by
      rw [lact_inv_lact]
      exact ⟨OntoS.dom_rmul X hzO hb, (hinv z hzO b hb).1⟩
    refine ⟨γ, zOf, _, hUo, hmem, hzd, ?_⟩
    have hcont : ContinuousAt (fun y' => lact γ⁻¹ y') (lact γ (rmul (cpt X x z) b)) :=
      (KU.cont_lact X γ⁻¹).continuousAt
    have hU' : ∀ᶠ y' in 𝓝 (lact γ (rmul (cpt X x z) b)), lact γ⁻¹ y' ∈ {w | w ∈ X.dom ∧ Δ w ≠ 0} :=
      hcont.preimage_mem_nhds (hUo.mem_nhds hmem)
    have hzc : ContinuousAt (fun y' => zOf (lact γ⁻¹ y')) (lact γ (rmul (cpt X x z) b)) :=
      ContinuousAt.comp (f := fun y' => lact γ⁻¹ y')
        ((hzd.differentiableAt (hUo.mem_nhds hmem)).continuousAt) hcont
    have hval : zOf (lact γ⁻¹ (lact γ (rmul (cpt X x z) b))) = z := by
      rw [lact_inv_lact]; exact (hinv z hzO b hb).2.1
    have h2 : ‖zOf (lact γ⁻¹ (lact γ (rmul (cpt X x z) b)))‖ < R := by
      rw [hval]; exact lt_of_le_of_lt hz hρR
    have hnear : ∀ᶠ y' in 𝓝 (lact γ (rmul (cpt X x z) b)), ‖zOf (lact γ⁻¹ y')‖ < R :=
      hzc.norm.eventually_lt continuousAt_const h2
    filter_upwards [hU', hnear] with y' hy'U hy'n
    obtain ⟨hy'd, hy'Δ⟩ := hy'U
    obtain ⟨-, hbO, heq⟩ := hsplit _ hy'd hy'Δ
    have hy' : y' = lact γ (rmul (cpt X x (zOf (lact γ⁻¹ y'))) (bOf (lact γ⁻¹ y'))) := by
      rw [← heq, lact_lact_inv]
    conv_lhs => rw [hy']
    exact hψ γ hγ _ hbO _ hy'n.le
  · left
    filter_upwards [hloc y hy hS] with y' hy'
    exact h0 y' hy'

end GlobalTheory.PeakWeightSmooth

namespace GlobalTheory.PeakWeightSmooth

theorem measurable_and_contDiffOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) (ρ R : ℝ) (η : V (nd X) → ℝ) (ψ : Frame X.Ψ r → ℝ), IsOrth X x → ρ < R → (∀ z : V (nd X), ‖z‖ ≤ R → z ∈ OmF X x) → ContDiff ℝ ∞ η → (∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, ∀ z : V (nd X), ‖z‖ ≤ R → ψ (lact γ (rmul (cpt X x z) b)) = η z) → (∀ y, (¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ ρ ∧ y = lact γ (rmul (cpt X x z) b)) → ψ y = 0) → (∀ y ∈ X.dom, (¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ ρ ∧ y = lact γ (rmul (cpt X x z) b)) → ∀ᶠ y' in 𝓝 y, ¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ ρ ∧ y' = lact γ (rmul (cpt X x z) b)) → Measurable ψ ∧ ContDiffOn ℝ ∞ (fun w => ψ (cpt X x w)) (OmF X x) := by
  intro E _ _ _ r X x ρ R η ψ hx hρR hR hη hψ h0 hloc
  classical
  have hS_dom : ∀ y, (∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ ρ ∧
      y = lact γ (rmul (cpt X x z) b)) → y ∈ X.dom := by
    rintro y ⟨γ, hγ, b, hb, z, hz, rfl⟩
    exact KU.lact_dom X hγ (OntoS.dom_rmul X (hR z (hz.trans hρR.le)) hb)
  have hcont : ∀ y ∈ X.dom, ContinuousAt ψ y := by
    intro y hy
    rcases local_form X x hx ρ R η ψ hρR hR hψ h0 hloc hy with h | ⟨γ, zOf, U, hUo, hyU, hzd, hev⟩
    · exact (continuousAt_const (y := (0 : ℝ))).congr (h.mono fun _ h => h.symm)
    · have : ContinuousAt (fun y' => η (zOf (lact γ⁻¹ y'))) y :=
        hη.continuous.continuousAt.comp (((hzd.differentiableAt (hUo.mem_nhds hyU)).continuousAt).comp
          (KU.cont_lact X γ⁻¹).continuousAt)
      exact this.congr (hev.mono fun _ h => h.symm)
  have hzero : ∀ y, y ∉ X.dom → ψ y = 0 := fun y hy => h0 y (fun h => hy (hS_dom y h))
  constructor
  · have heq : ψ = X.dom.piecewise ψ (fun _ => 0) := by
      funext y
      by_cases hy : y ∈ X.dom
      · simp [Set.piecewise, hy]
      · simp [Set.piecewise, hy, hzero y hy]
    rw [heq]
    exact ContinuousOn.measurable_piecewise (fun y hy => (hcont y hy).continuousWithinAt)
      continuousOn_const (IW.isOpen_dom X).measurableSet
  · intro w hw
    refine ContDiffAt.contDiffWithinAt ?_
    have hc : ContinuousAt (cpt X x) w := (IW.cpt_diff X x).continuous.continuousAt
    rcases local_form X x hx ρ R η ψ hρR hR hψ h0 hloc (y := cpt X x w) hw with
      h | ⟨γ, zOf, U, hUo, hyU, hzd, hev⟩
    · have h' : ∀ᶠ w' in 𝓝 w, ψ (cpt X x w') = 0 := hc.eventually h
      exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq h'
    · have hg : Differentiable ℂ (fun w' => lact γ⁻¹ (cpt X x w')) := by
        have e : (fun w' => lact γ⁻¹ (cpt X x w')) = cpt X (lact γ⁻¹ x) := by
          funext w'; rw [KU.cpt_lact]
        rw [e]; exact IW.cpt_diff X _
      have hN : (fun w' => lact γ⁻¹ (cpt X x w')) ⁻¹' U ∈ 𝓝 w :=
        hg.continuous.continuousAt.preimage_mem_nhds (hUo.mem_nhds hyU)
      have hΦd : DifferentiableOn ℂ (fun w' => zOf (lact γ⁻¹ (cpt X x w')))
          ((fun w' => lact γ⁻¹ (cpt X x w')) ⁻¹' U) :=
        hzd.comp hg.differentiableOn (fun _ h => h)
      have hΦ : ContDiffAt ℂ ∞ (fun w' => zOf (lact γ⁻¹ (cpt X x w'))) w :=
        GlobalTheory.SCV.contDiffAt_of_differentiableOn hΦd hN _
      have hev' : ∀ᶠ w' in 𝓝 w, ψ (cpt X x w') = η (zOf (lact γ⁻¹ (cpt X x w'))) := hc.eventually hev
      exact ((hη.contDiffAt).comp w (hΦ.restrict_scalars ℝ)).congr_of_eventuallyEq hev'

end GlobalTheory.PeakWeightSmooth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantMeasureChartBallOrthonormalLowerBound
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal

namespace GlobalTheory.BallVol

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem spread_zero (X : Data E r) (hr : 0 < r) (τ : X.Ψ) : X.spread (fun _ _ => 0) τ = 0 := by
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  simp [Data.spread]

theorem nd_le (X : Data E r) : nd X ≤ X.Ψ.card * (r * r) := by
  unfold nd
  rw [Fintype.card_prod, Fintype.card_coe]
  refine Nat.mul_le_mul_left _ ?_
  calc Fintype.card {p : Fin r × Fin r // p.2 < p.1} ≤ Fintype.card (Fin r × Fin r) :=
        Fintype.card_subtype_le _
    _ = r * r := by simp

theorem nat_bound (f r n : ℕ) (hf : 1 ≤ f) (hr : 1 ≤ r) (hn : n ≤ f * (r * r)) :
    2 * n * (200 * r ^ 3 * f) + n * n + 1 ≤ 402 * (f * r) ^ 8 := by
  set a := f * r with ha
  have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hra : r ≤ a := by rw [ha]; exact Nat.le_mul_of_pos_left r (by omega)
  have hfa : f ≤ a := by rw [ha]; exact Nat.le_mul_of_pos_right f (by omega)
  have hna : n ≤ a * a := hn.trans (by rw [ha, ← Nat.mul_assoc]; exact Nat.mul_le_mul_left _ hra)
  have h1 : 2 * n * (200 * r ^ 3 * f) ≤ 400 * a ^ 8 := by
    have e : 2 * n * (200 * r ^ 3 * f) ≤ 400 * ((a * a) * (a ^ 3 * a)) := by
      have := Nat.mul_le_mul hna (Nat.mul_le_mul (Nat.pow_le_pow_left hra 3) hfa)
      nlinarith
    refine e.trans (Nat.mul_le_mul_left _ ?_)
    calc a * a * (a ^ 3 * a) = a ^ 6 := by ring
      _ ≤ a ^ 8 := Nat.pow_le_pow_right ha1 (by norm_num)
  have h2 : n * n ≤ a ^ 8 := by
    calc n * n ≤ (a * a) * (a * a) := Nat.mul_le_mul hna hna
      _ = a ^ 4 := by ring
      _ ≤ a ^ 8 := Nat.pow_le_pow_right ha1 (by norm_num)
  have h3 : 1 ≤ a ^ 8 := Nat.one_le_pow _ _ ha1
  omega

theorem real_bound (f r n : ℕ) (hf : 1 ≤ f) (hr : 1 ≤ r) (hn : n ≤ f * (r * r)) :
    Real.exp (-(402 * ((f : ℝ) * r) ^ 8)) ≤ Real.exp (-(1 / 10)) *
      (Real.pi ^ n * (1 / (200 * (r : ℝ) ^ 3 * f)) ^ (2 * n) / n.factorial) := by
  set K : ℝ := 200 * (r : ℝ) ^ 3 * f with hK
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hK1 : 1 ≤ K := by
    have : (1 : ℝ) ≤ (r : ℝ) ^ 3 := one_le_pow₀ hr'
    rw [hK]; nlinarith
  have hKpos : 0 < K := by linarith

  have hδ : Real.exp (-K) ≤ 1 / K := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ hKpos (by linarith [Real.add_one_le_exp K])
  have hδn : Real.exp (-(2 * n * K)) ≤ (1 / K) ^ (2 * n) := by
    calc Real.exp (-(2 * n * K)) = Real.exp (-K) ^ (2 * n) := by
          rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
      _ ≤ (1 / K) ^ (2 * n) := pow_le_pow_left₀ (Real.exp_pos _).le hδ _
  have hpi : (1 : ℝ) ≤ Real.pi ^ n := one_le_pow₀ (by linarith [Real.pi_gt_three])
  have hfac : (n.factorial : ℝ) ≤ Real.exp ((n : ℝ) * n) := by
    have h1 : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
    have h2 : (n : ℝ) ^ n ≤ Real.exp n ^ n :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith [Real.add_one_le_exp (n : ℝ)]) _
    rw [← Real.exp_nat_mul] at h2
    exact h1.trans h2
  have hfpos : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hN := nat_bound f r n hf hr hn
  have hNR : 2 * (n : ℝ) * K + n * n + 1 ≤ 402 * ((f : ℝ) * r) ^ 8 := by
    rw [hK]; exact_mod_cast hN
  have hmain : Real.exp (-(402 * ((f : ℝ) * r) ^ 8)) ≤
      Real.exp (-(1 / 10)) * (Real.exp (-(2 * n * K)) / Real.exp ((n : ℝ) * n)) := by
    rw [← Real.exp_sub, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  refine hmain.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
  calc Real.exp (-(2 * n * K)) / Real.exp ((n : ℝ) * n)
      ≤ (1 / K) ^ (2 * n) / n.factorial := div_le_div₀ (by positivity) hδn hfpos hfac
    _ ≤ Real.pi ^ n * (1 / K) ^ (2 * n) / n.factorial := by
        gcongr
        exact le_mul_of_one_le_left (by positivity) hpi

theorem ballvol : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), 0 < X.p0 → X.p0 < r →
    ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x →
    ENNReal.ofReal (Real.exp (-(C * ((X.Ψ.card : ℝ) * r) ^ 8))) ≤
      ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x (Metric.ball (0 : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X))
        (1 / (100 * (r : ℝ) ^ 2)) ∩ ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x) := by
  refine ⟨402, by norm_num, ?_⟩
  intro E _ _ _ r X x hp0 hpr hx
  have hr : 0 < r := lt_of_le_of_lt (Nat.zero_le _) hpr
  set la : Wt X.Ψ r := fun _ _ => 0 with hla
  set w : ℝ := ∑ τ, X.spread la τ with hw
  have hw0 : w = 0 := Finset.sum_eq_zero fun τ _ => spread_zero X hr τ
  have hcard : ((X.Ψ.card : ℕ) : ℝ) = fdeg E := by
    rw [← Fintype.card_coe, QuadraticCoefficientForms.card_Psi X]
  have hf1 : (1 : ℝ) ≤ (X.Ψ.card : ℝ) := by rw [hcard]; exact one_le_field_half_degree
  have hf1n : 1 ≤ X.Ψ.card := by exact_mod_cast hf1
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  set δ := GlobalTheory.LevGeo.chartRad E r w with hδ
  have hδeq : δ = 1 / (200 * (r : ℝ) ^ 3 * (X.Ψ.card : ℝ)) := by
    rw [hδ, GlobalTheory.LevGeo.chartRad, hw0, zero_add, hcard]
  have hδpos : 0 < δ := by rw [hδeq]; positivity
  have hδle : δ ≤ 1 / (100 * (r : ℝ) ^ 2) := by
    rw [hδeq]
    refine one_div_le_one_div_of_le (by positivity) ?_
    have h3 : (r : ℝ) ^ 2 ≤ (r : ℝ) ^ 3 := pow_le_pow_right₀ hr1 (by norm_num)
    have h4 : (r : ℝ) ^ 3 ≤ (r : ℝ) ^ 3 * (X.Ψ.card : ℝ) := le_mul_of_one_le_right (by positivity) hf1
    nlinarith
  have hnear : ∀ z : V (nd X), ‖z‖ ≤ δ → cpt X x z ∈ X.dom ∧
      Real.exp (-(1 / 20)) ≤ X.nfac la (cpt X x z) ^ 2 ∧ Real.exp (-(1 / 10)) ≤ densF X x z :=
    fun z hz => GlobalTheory.ChartNearOne.chart_near_one E r X la w x hr hx le_rfl z hz
  have hsubO : Metric.ball (0 : V (nd X)) δ ⊆ OmF X x := fun z hz =>
    (hnear z (le_of_lt (mem_ball_zero_iff.1 hz))).1
  have hsub : Metric.ball (0 : V (nd X)) δ ⊆
      Metric.ball 0 (1 / (100 * (r : ℝ) ^ 2)) ∩ OmF X x := fun z hz =>
    ⟨Metric.ball_subset_ball hδle hz, hsubO hz⟩
  refine le_trans ?_ (measure_mono hsub)
  have hm : muF X x (Metric.ball 0 δ) =
      ∫⁻ z in Metric.ball (0 : V (nd X)) δ, ENNReal.ofReal (densF X x z) := by
    rw [muF, withDensity_apply _ measurableSet_ball, Measure.restrict_restrict measurableSet_ball,
      Set.inter_eq_left.2 hsubO]
  rw [hm]
  have hn := nd_le X
  calc ENNReal.ofReal (Real.exp (-(402 * ((X.Ψ.card : ℝ) * r) ^ 8)))
      ≤ ENNReal.ofReal (Real.exp (-(1 / 10))) * volume (Metric.ball (0 : V (nd X)) δ) := by
        rw [GlobalTheory.volume_ball_euclideanSpace_complex 0 hδpos, Fintype.card_fin,
          ← ENNReal.ofReal_mul (Real.exp_pos _).le]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hδeq]
        exact real_bound X.Ψ.card r (nd X) hf1n hr hn
    _ = ∫⁻ z in Metric.ball (0 : V (nd X)) δ, ENNReal.ofReal (Real.exp (-(1 / 10))) := by
        rw [setLIntegral_const, mul_comm]
    _ ≤ _ := setLIntegral_mono' measurableSet_ball fun z hz =>
        ENNReal.ofReal_le_ofReal (hnear z (le_of_lt (mem_ball_zero_iff.1 hz))).2.2

end

end GlobalTheory.BallVol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteAndFlatTorsion
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbTorsionAnyBase

open ReciprocityTheory.ChartRestriction.G.Out

theorem isFinite_and_flat_mulA (S : Scheme.{0}) (A : Over S) [GrpObj A] (hA : IsAbelianScheme A)
    (k : ℕ) (hk : 1 ≤ k) : IsFinite (mulA A k).left ∧ Flat (mulA A k).left := by
  have hc := hA.comm
  have hsm := hA.smooth
  have hpr := hA.proper
  have hm := GlobalTheory.AbLaw.MulN.isMonHom_mulA A k
  have hg : ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S),
      IsFinite ((Over.pullback t).map (mulA A k)).left := fun K _ _ t => by
    rw [GlobalTheory.MulFiniteFlat.pullback_map_mulA]
    exact GlobalTheory.MulFiniteAny.isFinite_mulA K _ (TLinPf.isAb_pullback t A hA) k hk
  have h1 : IsProper ((mulA A k).left ≫ A.hom) := by rw [Over.w]; exact hpr
  have h2 : IsProper (mulA A k).left := IsProper.of_comp _ A.hom
  have h3 : LocallyQuasiFinite (mulA A k).left :=
    LocallyQuasiFinite.of_finite_preimage_singleton _
      (GlobalTheory.MulFiniteFlat.finite_preimage_of_geomFibres _ hg)
  have hf : IsFinite (mulA A k).left := .of_isProper_of_locallyQuasiFinite _
  refine ⟨hf, GlobalTheory.flat_of_isFinite_of_finitePresentation_of_flat_geometric_fibres S _ _ _
    inferInstance inferInstance inferInstance hf fun K _ _ t => ?_⟩
  exact (GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected K _
    (TLinPf.isAb_pullback t A hA) _ inferInstance (hg K t)).1

theorem isFinite_and_flat_torsion : ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B], IsAbelianScheme B → ∀ N : ℕ, 1 ≤ N → IsFinite (torsion B N).hom ∧ Flat (torsion B N).hom := by
  intro S B _ hB N hN
  obtain ⟨h1, h2⟩ := isFinite_and_flat_mulA S B hB N hN
  rw [Out.mulA, ← GrpTangent.mulN_eq_pow] at h1 h2
  exact ⟨MorphismProperty.of_isPullback (P := @IsFinite) (GrpTangent.isPullback_torsion B N) h1,
    MorphismProperty.of_isPullback (P := @Flat) (GrpTangent.isPullback_torsion B N) h2⟩

end GlobalTheory.AbTorsionAnyBase
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProjOverOfIsQProjOverOfIsProper
section
namespace GlobalTheory.UPel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel

theorem isProjOver_of_isQProjOver_of_isProper :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) (s : X ⟶ Sp R),
      IsQProjOver s → IsProper s → IsProjOver s := by
  intro R _ _ X s hq hp
  exact GlobalTheory.SchemeWords.isProjOver_iff.mpr ⟨hq, hp⟩

end GlobalTheory.UPel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralFundamentalSetConjFiniteIndexSubgroupStatement
section
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_fundamentalSet_conj_finiteIndex_subgroup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (hΨ : X'.Ψ = X.Ψ) (δ : GL (Fin r) E) (x0 : Frame X.Ψ r) (x0' : Frame X'.Ψ r) (FF : Set (V (nd X))) (FF' : Set (V (nd X'))) (Φ : Frame X.Ψ r → ℝ≥0∞), X'.Gm = X.Gm → X'.p0 = X.p0 → (∀ v w, herm X.Gm ((δ : Matrix (Fin r) (Fin r) E).mulVec v) ((δ : Matrix (Fin r) (Fin r) E).mulVec w) = herm X.Gm v w) → X'.Γ.map (MulAut.conj δ).toMonoidHom ≤ X.Γ → (X'.Γ.map (MulAut.conj δ).toMonoidHom).relIndex X.Γ ≠ 0 → IsOrth X x0 → IsOrth X' x0' → IsFundSet X x0 FF → IsFundSet X' x0' FF' → Measurable Φ → (∀ γ ∈ X.Γ, ∀ x ∈ X.dom, Φ (lact γ x) = Φ x) → (∀ b ∈ Bor X.Ψ r, ∀ x ∈ X.dom, Φ (rmul x b) = Φ x) → ∫⁻ z in FF', Φ (lact δ (hΨ ▸ cpt X' x0' z)) ∂(muF X' x0') = ((X'.Γ.map (MulAut.conj δ).toMonoidHom).relIndex X.Γ : ℝ≥0∞) * ∫⁻ z in FF, Φ (cpt X x0 z) ∂(muF X x0) := by
  first | exact @GlobalTheory.SubgroupUnfold.lintegral_fundSet_conj_subgroup | exact GlobalTheory.SubgroupUnfold.lintegral_fundSet_conj_subgroup | (intros; apply GlobalTheory.SubgroupUnfold.lintegral_fundSet_conj_subgroup <;> assumption)
end

