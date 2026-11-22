import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1760
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1625
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsHomFamilyOfPureTypeComplexTriple
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1749
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1748
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1744
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1752
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1719
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1753
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1727
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1754
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0973
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0968
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVeryAmpleBasisSectionsAbelianSchemeOverDvr
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.exists_veryAmpleBy_basis_of_dvr : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ (M : LB G.left) (m : ℕ) (t₀ : Fin (m + 1) → M.Sec), M.IsLB → GlobalTheory.AbLaw.VeryAmpleBy G.hom M t₀ → ∃ (N : ℕ) (t : Fin (N + 1) → M.Sec), GlobalTheory.AbLaw.VeryAmpleBy G.hom M t ∧ ∀ u : M.Sec, ∃! c : Fin (N + 1) → W, u = ∑ j, GlobalTheory.AbLaw.cst G.hom ⊤ (c j) • t j := by
  intro W _ _ _ G _ hG M m t₀ hM hv
  have hflat : Flat G.hom := by
    haveI := hG.smooth
    infer_instance
  obtain ⟨n, t, ht⟩ := GlobalTheory.T.exists_basis_lineBundleSections_projective_over_dvr W G.left G.hom M hflat ⟨M, hM, m, t₀, hv⟩ hM
  have hne : Nonempty G.left := by
    obtain ⟨x⟩ : Nonempty (Sp W) := inferInstance
    exact ⟨(η[G]).left x⟩
  obtain ⟨x⟩ := hne
  obtain ⟨i₀, hi₀⟩ := TopologicalSpace.Opens.mem_iSup.1 (hv.1.ge (Set.mem_univ x))
  have hn : n ≠ 0 := by
    rintro rfl
    obtain ⟨c, hc, -⟩ := ht (t₀ i₀)
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hc
    rw [hc] at hi₀
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hi₀
    have hk' : x ∈ G.left.basicOpen (0 : Γ(G.left, M.U k)) := hk
    rw [Scheme.basicOpen_zero] at hk'
    exact hk'
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  choose a ha using fun i => (ht (t₀ i)).exists
  exact ⟨N, t, GlobalTheory.T.isVeryAmpleBySections_of_linear_span_combination W G.left G.hom M m N t₀ t a hM hv ha, ht⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilPairingEqCmIntegerOfPureType
section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CM.PureHom

section Lift

variable {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} {g g' : ℕ}

theorem linear_lift_unique (u : HolUnif A L g) (u' : HolUnif A' L' g')
    (h₂ : ∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) (h₁ : ∀ v, IsTangent v → ∃! w, u'.IsDiff w v)
    (f : A ⟶ A') [IsMonHom f] {F F' : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)}
    (hF : ∀ z, u'.ex (F z) = u.ex z ≫ f) (hF' : ∀ z, u'.ex (F' z) = u.ex z ≫ f) : F = F' := by
  refine LinearMap.ext fun w => ?_
  obtain ⟨v, ⟨hv, hd⟩, -⟩ := h₂ w
  exact (h₁ _ (HomLinear.isTangent_comp f hv)).unique (HomLinear.isDiff_comp u u' f F hF hv hd)
    (HomLinear.isDiff_comp u u' f F' hF' hv hd)

end Lift

def diagMul {E : Type} [Field E] {g : ℕ} (ty : Fin g → (E →+* ℂ)) (s : E) : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) where
  toFun z k := ty k s * z k
  map_add' z w := by funext k; simp [mul_add]
  map_smul' c z := by funext k; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

open PureTriple in

theorem exists_weilEq_smul_of_pure : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (A B : PAT H (Sp ℂ)) (p q : ℕ), p + q = 1 → (∀ τ : 𝓞 E →+* ℂ, (τ H.rt = H.rt0 → LieMult A.t.act (𝟙 (Sp ℂ)) τ p) ∧ (τ H.rt ≠ H.rt0 → LieMult A.t.act (𝟙 (Sp ℂ)) τ q)) → ∀ (f₁ f₂ : A.t.G ⟶ B.t.G), Serre.IsLinearHom A.t.act B.t.act f₁ → Serre.IsLinearHom A.t.act B.t.act f₂ → ∃ g : 𝓞 E, WeilEq B.t.PP.L f₁ f₂ A.t.PP.L (A.t.act.act g) (𝟙 _) (𝟙 (Sp ℂ)) := by
  intro E _ _ _ H A B p q hpq hdet f₁ f₂ hf₁ hf₂
  have hT : ThetaUnifAV := thetaUnifAV_all
  have hL : Out.Laws := abelianSchemeLaws_all.1
  obtain ⟨gA, ty, hty⟩ := AllClasses.exists_isTypeFn H p q
  obtain ⟨uA, HA, χA, -, hA, -⟩ := PureType.exists_isThetaUnif hT A.pol
  obtain ⟨uB, HB, χB, -, hB, -⟩ := PureType.exists_isThetaUnif hT B.pol
  obtain ⟨D, Pe, F, hp, hq, hP, hF, hE, hact⟩ := exists_datum_period hT hL A hty hdet uA hA
  obtain ⟨-, -, -, -, -, hA2, -⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH hT A.pol _ uA HA χA hA
  obtain ⟨EfB, hEB, -, -, hB1, hB2, -⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH hT B.pol _ uB HB χB hB
  obtain ⟨F₁, hF₁, hF₁Λ, -⟩ := HomLinear.exists_linear_of_isMonHom A.t.G B.t.G A.ab B.ab _ _ _ _ uA uB hB1 hB2
    f₁ hf₁.isMonHom
  obtain ⟨F₂, hF₂, hF₂Λ, -⟩ := HomLinear.exists_linear_of_isMonHom A.t.G B.t.G A.ab B.ab _ _ _ _ uA uB hB1 hB2
    f₂ hf₂.isMonHom
  choose ρB hρB using fun s : 𝓞 E => (HomLinear.exists_linear_of_isMonHom B.t.G B.t.G B.ab B.ab _ _ _ _ uB uB hB1 hB2
    (B.t.act.act s) (B.t.act.hom s)).imp fun _ h => h.1
  let G : 𝓞 E → (Fin A.pol.g → ℂ) →ₗ[ℂ] (Fin A.pol.g → ℂ) := fun s =>
    F.toLinearMap ∘ₗ diagMul ty (s : E) ∘ₗ F.symm.toLinearMap
  have hG : ∀ s z, uA.ex (G s z) = uA.ex z ≫ A.t.act.act s := fun s z => by
    have e := hact s (F.symm z)
    rw [F.apply_symm_apply] at e
    exact e
  have hGP : ∀ s a, G s (F (Pe a)) = F (Pe (s • a)) := fun s a => by
    simp only [G, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    congr 1
    funext k
    simp only [diagMul, LinearMap.coe_mk, AddHom.coe_mk, hP.1]
  have hcomm : ∀ (f : A.t.G ⟶ B.t.G), Serre.IsLinearHom A.t.act B.t.act f →
      ∀ Fl : (Fin A.pol.g → ℂ) →ₗ[ℂ] (Fin B.pol.g → ℂ), (∀ z, uB.ex (Fl z) = uA.ex z ≫ f) →
      ∀ s z, Fl (G s z) = ρB s (Fl z) := by
    intro f hf Fl hFl s z
    haveI := hf.isMonHom
    haveI := A.t.act.hom s
    have e := linear_lift_unique uA uB hA2 hB1 (A.t.act.act s ≫ f) (F := Fl ∘ₗ G s) (F' := ρB s ∘ₗ Fl)
      (fun z => by rw [LinearMap.comp_apply, hFl, hG, Category.assoc])
      (fun z => by rw [LinearMap.comp_apply, hρB, hFl, hf.comm, Category.assoc])
    exact LinearMap.congr_fun e z
  have hadj : ∀ s z w, hermForm HB (ρB s z) w = hermForm HB z (ρB (H.bar s) w) := fun a =>
    (weilEq_iff_hermForm_eq hT hL B.pol B.pol B.pol B.pol uB uB uB uB HB HB χB χB hB hB (B.t.act.act a) (𝟙 _) (𝟙 _)
      (B.t.act.act (H.bar a)) (ρB a) LinearMap.id LinearMap.id (ρB (H.bar a)) (hρB a)
      (fun _ => (Category.comp_id _).symm) (fun _ => (Category.comp_id _).symm) (hρB _)).1
      (weilEq_of_lamEq hL ℂ B.pol B.pol B.pol B.pol _ _ _ _ (B.t.act.hom a) inferInstance inferInstance
        (B.t.act.hom _) (by
          unfold LamEq
          rw [Category.comp_id, Category.comp_id]
          exact B.t.adj a))
  have mem₁ : ∀ a, F₁ (F (Pe a)) ∈ uB.Λ := fun a => hF₁Λ _ ((hF _).2 ⟨a, rfl⟩)
  have mem₂ : ∀ a, F₂ (F (Pe a)) ∈ uB.Λ := fun a => hF₂Λ _ ((hF _).2 ⟨a, rfl⟩)
  let β : D.La → D.La → ℤ := fun a b => EfB ⟨_, mem₁ a⟩ ⟨_, mem₂ b⟩
  have hβ : ∀ a b, (β a b : ℝ) = (hermForm HB (F₁ (F (Pe a))) (F₂ (F (Pe b)))).im := fun a b => hEB _ _
  have hadd₁ : ∀ x y z, β (x + y) z = β x z + β y z := fun x y z => by
    have e : (⟨_, mem₁ (x + y)⟩ : uB.Λ) = ⟨_, mem₁ x⟩ + ⟨_, mem₁ y⟩ := Subtype.ext (by simp)
    show EfB _ _ = EfB _ _ + EfB _ _
    rw [e, map_add, LinearMap.add_apply]
  have hadd₂ : ∀ x y z, β x (y + z) = β x y + β x z := fun x y z => by
    have e : (⟨_, mem₂ (y + z)⟩ : uB.Λ) = ⟨_, mem₂ y⟩ + ⟨_, mem₂ z⟩ := Subtype.ext (by simp)
    show EfB _ _ = EfB _ _ + EfB _ _
    rw [e, map_add]
  have hadjβ : ∀ (s : 𝓞 E) x y, β (s • x) y = β x (H.bar s • y) := fun s x y => by
    have e : (β (s • x) y : ℝ) = β x (H.bar s • y) := by
      rw [hβ, hβ, ← hGP, ← hGP, hcomm f₁ hf₁ F₁ hF₁, hcomm f₂ hf₂ F₂ hF₂, hadj]
    exact_mod_cast e
  obtain ⟨γ, hγ, hβγ⟩ := GlobalTheory.T.exists_linear_endomorphism_of_conjugate_adjoint_form E H D β hadd₁ hadd₂ hadjβ
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_smul_of_rank_one' E H D (by rw [hp, hq]; exact hpq) γ hγ
  refine ⟨c, (weilEq_iff_hermForm_eq hT hL A.pol A.pol B.pol A.pol uA uA uB uA HB HA χB χA hB hA f₁ f₂
    (A.t.act.act c) (𝟙 _) F₁ F₂ (G c) LinearMap.id hF₁ hF₂ (hG c) (fun _ => (Category.comp_id _).symm)).2 ?_⟩
  refine HermWeil.hermForm_eq_of_im HB HA F₁ F₂ (G c) LinearMap.id uA.full uA.full fun z hz w hw => ?_
  obtain ⟨a, ha⟩ := AddMonoidHom.mem_range.1 ((hF (F.symm z)).1 (by rwa [F.apply_symm_apply]))
  obtain ⟨b, hb⟩ := AddMonoidHom.mem_range.1 ((hF (F.symm w)).1 (by rwa [F.apply_symm_apply]))
  have ez : z = F (Pe a) := by rw [ha, F.apply_symm_apply]
  have ew : w = F (Pe b) := by rw [hb, F.apply_symm_apply]
  subst ez ew
  rw [← hβ, hβγ, hc, ← hE, LinearMap.id_apply, hGP]

end GlobalTheory.CM.PureHom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePlaceComponentAdeleNormEqLocalNorm
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.NormAtPlace

theorem evFin_norm_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F) (x : AE F E),
    evFin F v (Algebra.norm (AF F) x) = Algebra.norm (Fv F v) (compFin F E v x) := by
  intro F E _ _ _ _ _ v x
  classical
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let e := Module.finBasis F E
  let b := Algebra.TensorProduct.basis (AF F) e
  let b' := Algebra.TensorProduct.basis (Fv F v) e
  have hrepr : ∀ (z : AF F ⊗[F] E) i, b'.repr (compFin F E v z) i = evFin F v (b.repr z i) := by
    intro z i
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a y =>
      simp only [compFin, b, b', AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply, Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply,
        smul_eq_mul, map_mul, AlgHom.commutes]
    | add y z hy hz => simp only [map_add, Finsupp.add_apply, hy, hz]
  have hb : ∀ j, compFin F E v (b j) = b' j := by
    intro j
    simp [compFin, b, b', Algebra.TensorProduct.basis_apply]
  have hmat : Algebra.leftMulMatrix b' (compFin F E v x) = (Algebra.leftMulMatrix b x).map (evFin F v) := by
    ext i j
    rw [Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
      ← hb j, ← map_mul, hrepr]
  rw [Algebra.norm_eq_matrix_det b', Algebra.norm_eq_matrix_det b, hmat]
  exact AlgHom.map_det (evFin F v) (Algebra.leftMulMatrix b x)

end GlobalTheory.NormAtPlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSectionNeZeroAtNumberFieldPointStatement
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatSection_ne_zero_at_numberField_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K), LiesOn Z y → evR Xo c s.sig y ≠ 0 := by
  first | exact @GlobalTheory.FlatPointNe.evR_sig_ne_zero | exact GlobalTheory.FlatPointNe.evR_sig_ne_zero | (intros; apply GlobalTheory.FlatPointNe.evR_sig_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatTensorSupportBoundedByUniformizerPowStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory ValuativeRel
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatTensor_support_bounded_by_uniformizer_pow : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (G : Grid k) (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k) (ϖ : kˣ) (e : ℕ) (T : G.Args → ℂ) (keep : Bool) (g : G.VertexGroup), IsUnif ϖ → G.IsTensor ϖ e (oppositePath G.m) T → ∃ n : ℕ, ∀ (x : ColArgs G) (y : RowArgs G), flatTensor hs ψ ν (moved G keep g T) x y ≠ 0 → (∀ j, j < G.m → ∀ r s, (j + 1 = G.m → r ≠ topLast G (j + 1)) → valuation k (x j r s) ≤ valuation k (((ϖ ^ n)⁻¹ : kˣ) : k)) ∧ ∀ i, i < G.m → ∀ r s, valuation k (y i r s) ≤ valuation k (((ϖ ^ n)⁻¹ : kˣ) : k) := by
  first | exact @GlobalTheory.FunObj.FlatSupp.flatTensor_support | exact GlobalTheory.FunObj.FlatSupp.flatTensor_support | (intros; apply GlobalTheory.FunObj.FlatSupp.flatTensor_support <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatTensorVanishesUnlessLastRowBounded
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory ValuativeRel
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV

noncomputable section

namespace GlobalTheory.FunObj.FlatLast

open GlobalTheory.RootEx

section Step
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

open Classical in

theorem stepPt_add_apply (x₀ : Matrix n n' k) (e δ : StepVar n c n' → k) (a : n ⊕ Fin c) (b : n' ⊕ Fin (c + 1)) :
    stepPt x₀ (e + δ) a b =
      stepPt x₀ e a b + if h : Free (c / 2 + 1) (a, b) ∨ Kept (a, b) then δ ⟨(a, b), h⟩ else 0 := by
  simp only [stepPt, Matrix.add_apply, Matrix.of_apply, Pi.add_apply]
  split_ifs <;> ring

end Step

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {G : Grid k}

open Classical in

def shiftVar (j₀ : Fin (G.m - 1)) (r : ℕ) (t : k) : Vars G := fun j w =>
  if j = j₀ ∧ Sum.elim (fun a : Fin (topRank G (j + 1)) => (a : ℕ) = r) (fun _ => False) w.1.1 ∧
    w.1.2.isRight = true then t else 0

theorem valuation_shiftVar_le (j₀ : Fin (G.m - 1)) (r : ℕ) {t s₀ : k} (ht : valuation k t ≤ valuation k s₀)
    (j : Fin (G.m - 1)) (w) : valuation k (shiftVar j₀ r t j w) ≤ valuation k s₀ := by
  unfold shiftVar
  split_ifs
  · exact ht
  · simp

theorem ch_shift (x : ColArgs G) (e : Vars G) (j₀ : Fin (G.m - 1)) (r : ℕ) (t : k) (j : Fin (G.m - 1)) :
    ch (stepPt (x j) ((e + shiftVar j₀ r t) j)) = ch (stepPt (x j) (e j)) := by
  unfold ch
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.add_apply, stepPt_add_apply]
  split_ifs <;> simp [shiftVar]

theorem rowVar_shift (x : ColArgs G) (e : Vars G) (j₀ : Fin (G.m - 1)) (r : ℕ) (t : k) (j : ℕ) (s) :
    rowVar x (e + shiftVar j₀ r t) j s = rowVar x e j s := by
  unfold rowVar
  split_ifs with h
  · refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs
    · rw [Pi.add_apply, stepPt_add_apply]
      split_ifs <;> simp [shiftVar]
    · rfl
  · rfl

theorem colVar_shift (x : ColArgs G) (e : Vars G) (j₀ : Fin (G.m - 1)) (hj₀ : (j₀ : ℕ) + 2 = G.m) (r : ℕ) (t : k)
    (j : Fin (G.m - 1)) (r' : Fin (topRank G (j + 1))) :
    colVar x (e + shiftVar j₀ r t) j r' = colVar x e j r' + if j = j₀ ∧ (r' : ℕ) = r then t else 0 := by
  unfold colVar
  rw [Pi.add_apply, stepPt_add_apply]
  congr 1
  by_cases hj : j = j₀
  · subst hj
    rw [dif_pos (Or.inr ⟨by rw [show G.m - 2 - (j : ℕ) = 0 by omega]; exact ⟨0, rfl⟩, rfl⟩)]
    simp [shiftVar]
  · simp [shiftVar, hj]

theorem phase_shift (x : ColArgs G) (e : Vars G) (j₀ : Fin (G.m - 1)) (hj₀ : (j₀ : ℕ) + 2 = G.m)
    (r : Fin (topRank G ((j₀ : ℕ) + 1))) (t : k) :
    phase x (e + shiftVar j₀ r t) = phase x e + rowVar x e ((j₀ : ℕ) + 1) r * t := by
  unfold phase
  have key : ∀ j : Fin (G.m - 1), (ch (stepPt (x j) ((e + shiftVar j₀ r t) j)) +
      if Even (G.m - 2 - j) then ∑ r', rowVar x (e + shiftVar j₀ r t) (j + 1) r' *
        colVar x (e + shiftVar j₀ r t) j r' else 0) =
      (ch (stepPt (x j) (e j)) + if Even (G.m - 2 - j) then ∑ r', rowVar x e (j + 1) r' * colVar x e j r' else 0) +
      if j = j₀ then rowVar x e ((j₀ : ℕ) + 1) r * t else 0 := by
    intro j
    rw [ch_shift]
    simp only [rowVar_shift, colVar_shift x e j₀ hj₀]
    by_cases hj : j = j₀
    · subst hj
      have hev : Even (G.m - 2 - (j : ℕ)) := by rw [show G.m - 2 - (j : ℕ) = 0 by omega]; exact ⟨0, rfl⟩
      rw [if_pos hev, if_pos hev, if_pos rfl]
      simp only [true_and, mul_add, Finset.sum_add_distrib, add_assoc]
      congr 2
      simp_rw [Fin.val_inj, mul_ite, mul_zero]
      rw [Finset.sum_ite_eq']
      simp
    · simp [hj]
  rw [Finset.sum_congr rfl fun j _ => key j, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

variable (hs : 1 ≤ G.s)

theorem valuation_downMap_sub_le (x : ColArgs G) (e δ : Vars G) {s₀ : k}
    (hδ : ∀ j w, valuation k (δ j w) ≤ valuation k s₀) (j : ℕ) (a b) :
    valuation k (downMap hs x (e + δ) j a b - downMap hs x e j a b) ≤ valuation k s₀ := by
  classical
  unfold downMap
  split_ifs with h1 h2
  · simp only [reindex_apply, submatrix_apply, Pi.add_apply]
    rw [stepPt_add_apply, add_sub_cancel_left]
    split_ifs
    · exact hδ _ _
    · simp
  · simp
  · simp

theorem valuation_fill_sub_le (x : ColArgs G) (y : RowArgs G) (e δ : Vars G) {s₀ : k}
    (hδ : ∀ j w, valuation k (δ j w) ≤ valuation k s₀) (b : Edge) (r s) :
    valuation k ((fill hs x y (e + δ) - fill hs x y e) b r s) ≤ valuation k s₀ := by
  rcases b with ⟨i, j⟩ | ⟨i, j⟩
  · simp only [fill, Pi.sub_apply]
    split_ifs with h
    · simp only [Matrix.sub_apply, transpose_apply, submatrix_apply]
      exact valuation_downMap_sub_le hs x e δ hδ j _ _
    · simp
  · simp only [fill, Pi.sub_apply]
    split_ifs with h
    · simp
    · simp

end GlobalTheory.FunObj.FlatLast

namespace GlobalTheory.FunObj.FlatLast
open GlobalTheory.RootEx

theorem flatTensor_lastRow_bounded : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (G : Grid k) (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] (ϖ : kˣ) (e : ℕ) (T : G.Args → ℂ) (keep : Bool) (g : G.VertexGroup), 2 ≤ G.m → IsUnif ϖ → HasConductor ψ 1 → G.IsTensor ϖ e (oppositePath G.m) T → ∃ n : ℕ, ∀ (x : ColArgs G) (y : RowArgs G), flatTensor hs ψ ν (moved G keep g T) x y ≠ 0 → ∀ s, valuation k (x (G.m - 1) (topLast G (G.m - 1 + 1)) s) ≤ valuation k (((ϖ ^ n)⁻¹ : kˣ) : k) := by
  intro k _ _ _ _ _ _ G hs ψ ν _ ϖ e T keep g hm hϖ hψ hT
  obtain ⟨n, -, hper⟩ := GlobalTheory.MovedBound.moved_bounded_locConst G ϖ e T keep g hϖ hT
  refine ⟨n, fun x y hF => ?_⟩
  let j₀ : Fin (G.m - 1) := ⟨G.m - 2, by omega⟩
  have hj₀ : (j₀ : ℕ) + 2 = G.m := by simp only [j₀]; omega
  suffices key : ∀ r : Fin (topRank G ((j₀ : ℕ) + 1)),
      valuation k (x ((j₀ : ℕ) + 1) (topLast G ((j₀ : ℕ) + 1 + 1)) r) ≤ valuation k (((ϖ ^ n)⁻¹ : kˣ) : k) by
    have h : G.m - 1 = (j₀ : ℕ) + 1 := by omega
    rw [h]
    exact key
  intro r
  by_contra hlt
  have hu : x ((j₀ : ℕ) + 1) (topLast G ((j₀ : ℕ) + 1 + 1)) r ∉ cball (1 * (ϖ ^ n)⁻¹) := by
    simpa [cball] using hlt
  obtain ⟨t, ht, hne⟩ := hψ.exists_ne_one (ϖ ^ n) hu
  set u := x ((j₀ : ℕ) + 1) (topLast G ((j₀ : ℕ) + 1 + 1)) r with hu_def
  have hrow : ∀ e' : Vars G, rowVar x e' ((j₀ : ℕ) + 1) r = u := fun e' => by
    rw [rowVar, dif_neg (by omega)]
  let δ : Vars G := shiftVar j₀ r (-t)
  have hδ : ∀ j w, valuation k (δ j w) ≤ valuation k ((ϖ ^ n : kˣ) : k) :=
    valuation_shiftVar_le _ _ (by simpa [cball, Valuation.map_neg] using ht)
  have hS : ∀ e' : Vars G, moved G keep g T (fill hs x y (e' + δ)) = moved G keep g T (fill hs x y e') := fun e' => by
    have := hper (fill hs x y e') (fill hs x y (e' + δ) - fill hs x y e')
      (fun b _ r s => valuation_fill_sub_le hs x y e' δ hδ b r s)
    rwa [add_sub_cancel] at this
  have hI : ∀ e' : Vars G, flatIntegrand hs ψ (moved G keep g T) x y (e' + δ) =
      (ψ (t * u) : ℂ) * flatIntegrand hs ψ (moved G keep g T) x y e' := fun e' => by
    unfold flatIntegrand
    rw [hS, phase_shift x e' j₀ hj₀ r (-t), hrow,
      show -(phase x e' + u * -t) = -phase x e' + t * u by ring, AddChar.map_add_eq_mul, Circle.coe_mul]
    ring
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hFeq : flatTensor hs ψ ν (moved G keep g T) x y =
      (ψ (t * u) : ℂ) * flatTensor hs ψ ν (moved G keep g T) x y := by
    have : SigmaFinite ν := inferInstance
    have : ν.IsAddRightInvariant := inferInstance
    have : (varsVol G ν).IsAddRightInvariant := by unfold varsVol; infer_instance
    unfold flatTensor
    calc ∫ e', flatIntegrand hs ψ (moved G keep g T) x y e' ∂(varsVol G ν)
        = ∫ e', flatIntegrand hs ψ (moved G keep g T) x y (e' + δ) ∂(varsVol G ν) :=
          (integral_add_right_eq_self _ δ).symm
      _ = ∫ e', (ψ (t * u) : ℂ) * flatIntegrand hs ψ (moved G keep g T) x y e' ∂(varsVol G ν) := by simp_rw [hI]
      _ = _ := integral_const_mul (ψ (t * u) : ℂ) _
  have hne' : (ψ (t * u) : ℂ) ≠ 1 := fun h => hne (Circle.ext (by simpa using h))
  have : (1 - (ψ (t * u) : ℂ)) * flatTensor hs ψ ν (moved G keep g T) x y = 0 := by
    rw [sub_mul, one_mul, ← hFeq, sub_self]
  rcases mul_eq_zero.1 this with h | h
  · exact hne' (sub_eq_zero.1 h).symm
  · exact hF h

end GlobalTheory.FunObj.FlatLast
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetsOriginOppositeSignVacuumConjPeriod
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FunObj.FockChi

theorem fockIn_chi_zero : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (W : G.Weil) {U : Set T} (N : GlobalTheory.FunObj.Std G U) (δ t0 : ℂ), Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ → δ ≠ 0 → Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (Formalism.MainNotions.TaylorLogMetric.lamOf D D.host.ccK δ) t0 → ∀ i : ℕ, i + 1 ≤ D.R.m → ∀ e0 : Formalism.MainNotions.TaylorLogMetric.VC D (G.pS (.chi i D.R.m : Pair T)).rank (G.pT (.chi i D.R.m : Pair T)).rank → ℂ, Formalism.MainNotions.StandardLatticesGL3.oddE0 D D.host.ccK δ t0 _ _ e0 → ∀ f, IsVacO W.ψ W.θ _ _ (G.cartS W.cart (.chi i D.R.m)) (G.onT W.cart (.chi i D.R.m)) (N.latS (.chi i D.R.m) : Set _) (N.latT (.chi i D.R.m) : Set _) f → ∃ c : ℂˣ, ∀ k : FVar D (G.pT (.chi i D.R.m : Pair T)).rank (G.pS (.chi i D.R.m : Pair T)).rank →₀ ℕ, GlobalTheory.FunObj.fockIn W N.frC (.chi i D.R.m) f (MvPolynomial.monomial k 1) 0 = c * starRingEnd ℂ ((k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) e0) := by
  intro D T L sc G W U N δ t0 hc hδ ht i hi e0 he f hf
  have hcf := GlobalTheory.T.isVacuum_conj_of_negHermitianSpace _ _ _ _ _ _ _ _ f hf
  obtain ⟨c, hc'⟩ := GlobalTheory.T.fockJets_unitVacuum_eq_unit_mul_periodJets W.ψ W.θ (G.V (.grid (i + 1) D.R.m)) (G.V (.grid i D.R.m)) (W.cart (.grid (i + 1) D.R.m)) (W.cart (.grid i D.R.m))
    (N.fr _) (N.fr _) (N.fr_on _ ⟨hi, rfl⟩) (N.fr_on _ ⟨by omega, rfl⟩)
    (W.cart_is _ ⟨hi, le_rfl⟩) (W.cart_is _ ⟨by omega, le_rfl⟩) δ t0 hc hδ ht e0 he _ hcf
  refine ⟨Units.map (starRingEnd ℂ).toMonoidHom c, fun k => ?_⟩
  have h2 := GlobalTheory.T.fockVector_negHermitianSpace_conj_monomial W.ψ W.θ (G.V (.grid (i + 1) D.R.m)) (G.V (.grid i D.R.m)) (W.cart (.grid (i + 1) D.R.m)) (W.cart (.grid i D.R.m))
    (N.frC (.grid (i + 1) D.R.m)) (N.frC (.grid i D.R.m)) f hf.1 hf.2.inf k 0
  have e1 : N.frC (.grid (i + 1) D.R.m) = fun τ => (N.fr (.grid (i + 1) D.R.m)).1.map (tauE D τ) := rfl
  have e2 : N.frC (.grid i D.R.m) = fun τ => (N.fr (.grid i D.R.m)).1.map (tauE D τ) := rfl
  show pureTensorO _ _ _ _ _ _ _ _ f _ 0 = _
  rw [h2, e1, e2, hc' k, map_mul]
  rfl

end GlobalTheory.FunObj.FockChi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalSquaringPathsBaseChangeAndHomStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalSquaringPaths_baseChange_and_hom : (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R : Type) [CommRing R], ∀ (R' : Type) [CommRing R'] (φ : R →+* R') (c : R) (u : R') (b : Sp R ⟶ S) (ξ : Sp (PowerSeries R) ⟶ G.left), IsPath G c b ξ → IsPath G (φ c) (spMap φ ≫ b) (spMap ((PowerSeries.rescale u).comp (PowerSeries.map φ)) ≫ ξ) ∧ ∀ [IsLocalRing R] (n : ℕ) (V : S.Opens) (τ : Fin n → Γ(Lie G, V)) (w : Fin n → R), ⊤ ≤ b ⁻¹ᵁ V → ∀ (U : G.left.Opens) (hU : ⊤ ≤ ξ ⁻¹ᵁ U), HasTan G b ξ τ w → ∀ (hU' : ⊤ ≤ (spMap ((PowerSeries.rescale u).comp (PowerSeries.map φ)) ≫ ξ) ⁻¹ᵁ U) (V' : S.Opens) (hV : V' ≤ V) (he : V' ≤ unitSec G ⁻¹ᵁ U) (hb : ⊤ ≤ b ⁻¹ᵁ V') (f : Γ(G.left, U)), PowerSeries.coeff 1 (evAt (spMap ((PowerSeries.rescale u).comp (PowerSeries.map φ)) ≫ ξ) hU' f) = ∑ i, u * φ (w i) * φ (evAt b hb (dualApp (τ i) hV (dUnit G he f)))) ∧ (∀ (S : Scheme.{0}) (G H : Over S) [GrpObj G] [GrpObj H] (q : G ⟶ H) [IsMonHom q] (R : Type) [CommRing R] (c : R) (b : Sp R ⟶ S) (ξ : Sp (PowerSeries R) ⟶ G.left), (IsPath G c b ξ → IsPath H c b (ξ ≫ q.left)) ∧ triv G b ≫ q.left = triv H b ∧ sqr G ≫ q.left = q.left ≫ sqr H) := by
  first | exact @GlobalTheory.Nef.paths_bc | exact GlobalTheory.Nef.paths_bc | (intros; apply GlobalTheory.Nef.paths_bc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramedPointCoordinatesMemSpanEigenLatticeStatement
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.framedPoint_coordinates_mem_span_eigenLattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (ρ : E →+* ℂ) (tt : 𝓞 E →+* 𝓞 K), (∀ a, ((tt a : 𝓞 K) : K) = algebraMap c.F K (embK c ρ a)) → ∀ (u : Fin (Dw.mult ρ) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F ρ u → ∀ j, u j ∈ Submodule.span K (F.eigLat B.t.act tt : Set (Fin F.P₀.g → K)) := by
  first | exact @GlobalTheory.PtDeg.frameCoord_mem_span_eigLat | exact GlobalTheory.PtDeg.frameCoord_mem_span_eigLat | (intros; apply GlobalTheory.PtDeg.frameCoord_mem_span_eigLat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramedPointGenericFibreCoordinatesEqFrameStatement
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.framedPoint_genericFibre_coordinates_eq_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (ρ : E →+* ℂ) (u : Fin (Dw.mult ρ) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F ρ u → ∀ (T : CDVR) (iK : K →+* T.Fr), letI := (iK.comp (algebraMap c.F K)).toAlgebra; ∀ (yT : FrPt Xo c T.Fr), FrMap ({ iK with commutes' := fun _ => rfl } : K →ₐ[c.F] T.Fr) y yT → ∀ (t' : SAB H (Sp T.Fr)) (n' : SABMap t' t₀ (spMap iK)) (m1' : SABMap t' Xo.univ.t yT.x), m1'.φ = n'.φ ≫ m1.φ → ∀ (v' : Fin F.P₀.g → (epsR T.Fr ⟶ t'.G)), IsLieBasis v' → (∀ k, (v' k).left ≫ n'.φ ≫ m2.φ = spMap (Formalism.L2.Pj.dualMap iK) ≫ (F.v k).left ≫ F.φ) → ∀ (C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) T.Fr) (a : T.Fr) (y' : FrPt Xo c T.Fr), FrChg C a yT y' → ∀ (i : Fin (Dw.mult ρ)) (u'' : Sp (DualNumber T.Fr) ⟶ t'.G.left), u'' ≫ t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) → u'' ≫ m1'.φ = y'.u ρ i → ∃ w'' : epsR T.Fr ⟶ t'.G, w''.left = u'' ∧ IsLieComb (∑ j, C ρ i j • fun k => iK (u j k)) v' w'' := by
  first | exact @GlobalTheory.PtDeg.frame_genFib_coords | exact GlobalTheory.PtDeg.frame_genFib_coords | (intros; apply GlobalTheory.PtDeg.frame_genFib_coords <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreIntegralTangentInSpanLieBasisStatement
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericFibre_integral_tangent_in_span_lieBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (K : Type) [Field K] [NumberField K] (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (T : CDVR) (iK : K →+* T.Fr) (ρV : 𝓞 K →+* T.V), (algebraMap T.V T.Fr).comp ρV = iK.comp (algebraMap (𝓞 K) K) → ∀ (G : GlobalTheory.CM.PAT H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (n : SABMap G.t B.t (spMap ρV)) (n' : SABMap t' t₀ (spMap iK)) (m2' : SABMap t' G.t (spMap (algebraMap T.V T.Fr))), m2'.φ ≫ n.φ = n'.φ ≫ m2.φ → ∀ (v' : Fin F.P₀.g → (epsR T.Fr ⟶ t'.G)), IsLieBasis v' → (∀ k, (v' k).left ≫ n'.φ ≫ m2.φ = spMap (Formalism.L2.Pj.dualMap iK) ≫ (F.v k).left ≫ F.φ) → ∀ (vV : Fin F.P₀.g → (epsR T.V ⟶ G.t.G)) (M : Fin F.P₀.g → Fin F.P₀.g → K), IsLieBasis vV → (∀ k, ∃ w : epsR K ⟶ F.P₀.A, IsLieComb (M k) F.v w ∧ spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)) ≫ (vV k).left ≫ n.φ = spMap (Formalism.L2.Pj.dualMap iK) ≫ w.left ≫ F.φ) → ∀ (ub : epsOver T.V T.V ⟶ G.t.G) (u'' : Sp (DualNumber T.Fr) ⟶ t'.G.left), IsTan ub → u'' ≫ m2'.φ = spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)) ≫ ub.left → ∃ (a : Fin F.P₀.g → T.V) (w'' : epsR T.Fr ⟶ t'.G), w''.left = u'' ∧ IsLieComb (∑ k, algebraMap T.V T.Fr (a k) • fun l => iK (M k l)) v' w'' := by
  first | exact @GlobalTheory.PtDeg.LieModel.generic_coords_in_span | exact GlobalTheory.PtDeg.LieModel.generic_coords_in_span | (intros; apply GlobalTheory.PtDeg.LieModel.generic_coords_in_span <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridCharactersUnramifiedStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grid_characters_unramified : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T), Lc.Is μ₀ → ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → v ∉ G.pl.S0 → ∀ i : Fin D.R.m, GlobalTheory.WeilParts.UnramAt e (G.ch.chi (D.R.m - i)) ∧ GlobalTheory.WeilParts.UnramAt e Lc.eta := by
  first | exact @GlobalTheory.GridUnr.chi_eta_unramAt | exact GlobalTheory.GridUnr.chi_eta_unramAt | (intros; apply GlobalTheory.GridUnr.chi_eta_unramAt <;> assumption)
end

