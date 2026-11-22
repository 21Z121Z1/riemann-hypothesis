import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0055
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0059
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0061
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0052
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0053
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBasisLatticeNear
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NsmulEqZeroOfCast
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemPadicAlgClValuationSubringIffNormLeOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0058
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsMulPullSec
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0051
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsScalarFormTraceForm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBundleOnAdmissibleModel
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

theorem exists_isEE_of_adm : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens), S.HasTests → S.admitted M U₀ → ∃ EE : M.Lat S.J, S.IsEE M U₀ EE ∧ (∀ z : M.Z, IsClosed ({z} : Set M.Z) → EE.E z = Submodule.span (M.O z) {v | ∃ (c : S.TT M z →+ ZMod S.N) (k : _) (x₀ : S.Gam) (i : S.J), M.Div (S.FF (S.TT M z) c) k z ∧ x₀ ∈ S.supI M z ∧ v = fun j => S.th x₀ / S.FF _ c k * algebraMap o Ω (S.proj _ c j i)}) := by
  intro o Ω _ _ _ hb S M U₀ hT hA
  have hO : S.Over₀ M U₀ := hA.1
  haveI := hb.ft
  haveI := hb.char
  have hll := @GlobalTheory.ZH.classical_points_and_local_regularity o Ω _ _ _ _ _ M U₀ hO.normal
  have hte := @GlobalTheory.ZH.exists_at_test_of_cen o Ω _ _ _ _ S M U₀ hT hO
  have hwt := @GlobalTheory.ZH.test_weights o Ω _ _ _ _ S
  have h0a := @GlobalTheory.ZH.ThetaSys.mem_supI_iff_and_HH_eq_ker o Ω _ _ _ _ S M U₀ hO
  have h0b := @GlobalTheory.ZH.isoFree_TT_and_supI_specializes o Ω _ _ _ _ S M U₀ hO hll hte h0a
  have h11 := @GlobalTheory.thetaSys_norm_FF_le_exp o Ω _ _ _ _ S hwt
  have h12 := @GlobalTheory.norm_val_FF_eq_of_div o Ω _ _ _ _ S M U₀ hO h0a h11 hte
  have hne := @GlobalTheory.ZH.FF_TT_ne_zero o Ω _ _ _ _ S M U₀ hO hll hte h0a h0b hwt
  have h2g := @GlobalTheory.ZH.comparison_function_regular o Ω _ _ _ _ S M U₀ hO hll hte h0a h0b hwt h11 h12
  have h2ge := @GlobalTheory.ZH.FirstIneq.ff_div_ff_mem_of_specializes o Ω _ _ _ _ S M U₀ hO hll hte h0a h0b hwt h11 h12
  have h2le := @GlobalTheory.ZH.ThetaSys.FF_div_FF_mem_O_of_valuationRing o Ω _ _ _ _ S M U₀ hO h0b h2g
  have h3h := @GlobalTheory.ZH.span_lattice_eq_of_valuationRing o Ω _ _ _ _ S M U₀ hA h0b hne h2ge h2le
  have h3b := @GlobalTheory.ZH.exists_basis_lattice_near o Ω _ _ _ _ S M U₀ hA h0b hne
  obtain ⟨EE, hE₁, hE₂⟩ := @GlobalTheory.ZH.WeightBundle.exists_lat o Ω _ _ _ _ S M U₀ hA hll.2 h0b hne h3h h3b
  exact ⟨EE, @GlobalTheory.ZH.isEE_of_span_weightSpaces o Ω _ _ _ _ S M U₀ EE hA h0a h0b hne hwt h12 hE₁ hE₂, hE₁⟩

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsClassicalPointLiftingResiduePoint
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory

theorem natCast_self_residueField_padicAlgCl_eq_zero (p : ℕ) [hp : Fact p.Prime] :
    ((p : ℕ) : kb p) = 0 := by
  rw [← map_natCast (IsLocalRing.residue (OO p)), IsLocalRing.residue_eq_zero_iff,
    Valuation.mem_maximalIdeal_iff]
  have : (((p : ℕ) : OO p) : PadicAlgCl p) = (p : PadicAlgCl p) := rfl
  rw [this, PadicAlgCl.valuation_p]
  have h1 : (1 : NNReal) < p := by exact_mod_cast hp.out.one_lt
  rw [div_lt_one (lt_trans zero_lt_one h1)]
  exact h1

theorem ker_isMaximal_of_forall_pow_eq_one {A k : Type*} [CommRing A] [Field k]
    (hk : ∀ x : k, x ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧ x ^ n = 1) (φ : A →+* k) :
    (RingHom.ker φ).IsMaximal := by
  refine Ideal.isMaximal_iff.mpr ⟨by simp, fun J a hJ ha haJ => ?_⟩
  obtain ⟨n, hn, h⟩ := hk (φ a) ha
  have h1 : 1 - a ^ n ∈ J := hJ (by simp [RingHom.mem_ker, h])
  have h2 : a ^ n ∈ J := J.pow_mem_of_mem haJ n hn
  simpa using J.add_mem h1 h2

theorem isClosed_image_point_of_forall_pow_eq_one {k : Type} [Field k]
    (hk : ∀ x : k, x ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧ x ^ n = 1) {X : Scheme.{0}} [JacobsonSpace X]
    (x : Sp k ⟶ X) (s : Sp k) : IsClosed ({x s} : Set X) := by
  obtain ⟨V, hV, φ, rfl⟩ := exists_affineOpen_factor_of_isLocalRing x
  have h := hV.fromSpec.isOpenEmbedding.preimage_closedPoints
  have hs : Spec.map φ s ∈ closedPoints (Spec Γ(X, V)) := by
    refine (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr ?_
    have := (s : PrimeSpectrum k).isPrime
    have e : (s : PrimeSpectrum k).asIdeal = ⊥ := Ideal.eq_bot_of_prime _
    have : (Spec.map φ s : PrimeSpectrum Γ(X, V)).asIdeal = RingHom.ker φ.hom := by
      change Ideal.comap φ.hom (s : PrimeSpectrum k).asIdeal = _
      rw [e]; rfl
    rw [this]
    exact ker_isMaximal_of_forall_pow_eq_one hk φ.hom
  rw [← h] at hs
  rw [Scheme.Hom.comp_apply]
  exact hs

theorem exists_residueField_factor_of_apply_eq {k : Type} [Field k] {X : Scheme.{0}}
    (x : Sp k ⟶ X) (s : Sp k) (z : X) (hz : x s = z) :
    ∃ r : X.residueField z ⟶ CommRingCat.of k, Spec.map r ≫ X.fromSpecResidueField z = x := by
  obtain rfl : s = IsLocalRing.closedPoint k := Subsingleton.elim _ _
  subst hz
  exact ⟨_, Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k X x⟩

theorem exists_integral_point_lifting_residue_point :
    ∀ (X : Scheme.{0}) [IsIntegral X] (π : X ⟶ Sp ℤ) [Flat π] [LocallyOfFiniteType π] (U : X.Opens),
      (U : Set X).Nonempty → ∀ (p : ℕ) [Fact p.Prime],
        (∀ x : Sp (kb p) ⟶ X, ∃ b : Sp (OO p) ⟶ X, rPt p ≫ b = x ∧ Set.range (gPt p ≫ b) ⊆ U) ∧
        (∀ (x : Sp (kb p) ⟶ X) (s : Sp (kb p)), IsClosed ({x s} : Set X)) := by
  intro X _ π _ _ U hU p hp
  obtain ⟨hJ, hfin, -⟩ := jacobson_closedPoints_tools_int X π
  obtain ⟨-, hord, hgal⟩ := GlobalTheory.T.kb_isAlgClosed_and_conj' p
  have hcl : ∀ (x : Sp (kb p) ⟶ X) (s : Sp (kb p)), IsClosed ({x s} : Set X) :=
    fun x s => isClosed_image_point_of_forall_pow_eq_one hord x s
  refine ⟨fun x => ?_, hcl⟩
  let s : Sp (kb p) := IsLocalRing.closedPoint (kb p)
  obtain ⟨q, hq, y, hy, hyU⟩ := padicAlgCl_integral_points.1 X π (x s) (hcl x s) U hU
  have hfz := hfin _ (hcl x s)
  obtain ⟨r', hr'⟩ := exists_residueField_factor_of_apply_eq x s _ rfl
  have hy' : (rPt q ≫ y) (IsLocalRing.closedPoint (kb q)) = x s := by
    refine (Scheme.Hom.comp_apply _ _ _).trans ((congrArg y ?_).trans hy)
    exact IsLocalRing.comap_closedPoint (IsLocalRing.residue (OO q))
  obtain ⟨r, hr⟩ := exists_residueField_factor_of_apply_eq (rPt q ≫ y) _ _ hy'
  obtain rfl : p = q := by
    have h1 : ((p : ℕ) : X.residueField (x s)) = 0 := by
      apply r'.hom.injective
      rw [map_natCast, map_zero]
      exact natCast_self_residueField_padicAlgCl_eq_zero p
    have h2 : ((q : ℕ) : X.residueField (x s)) = 0 := by
      apply r.hom.injective
      rw [map_natCast, map_zero]
      exact natCast_self_residueField_padicAlgCl_eq_zero q
    have := (CharP.charP_iff_prime_eq_zero (R := X.residueField (x s)) hp.out).mpr h1
    have := (CharP.charP_iff_prime_eq_zero (R := X.residueField (x s)) hq.out).mpr h2
    exact CharP.eq (X.residueField (x s)) ‹CharP _ p› ‹CharP _ q›
  obtain ⟨σ, hσ⟩ := hgal (X.residueField (x s)) r.hom r'.hom
  refine ⟨spMap σ.toRingHom ≫ y, ?_, ?_⟩
  · let τ : kb p →+* kb p := IsLocalRing.ResidueField.map (σ : OO p →+* OO p)
    have e1 : rPt p ≫ spMap σ.toRingHom = spMap τ ≫ rPt p := by
      refine (Spec.map_comp _ _).symm.trans (Eq.trans ?_ (Spec.map_comp _ _))
      rfl
    have e2 : r ≫ CommRingCat.ofHom τ = r' := by
      ext a
      obtain ⟨c, hc⟩ := IsLocalRing.residue_surjective (r.hom a)
      change τ (r.hom a) = r'.hom a
      rw [← hσ a c hc, ← hc]
      rfl
    rw [← Category.assoc, e1, Category.assoc]
    refine (congrArg (spMap τ ≫ ·) hr.symm).trans (Eq.trans ?_ hr')
    rw [← e2, Spec.map_comp, Category.assoc]
  · rintro _ ⟨t, rfl⟩
    apply hyU
    refine ⟨t, ?_⟩
    simp only [Scheme.Hom.comp_apply]
    congr 1
    have := (t : PrimeSpectrum (PadicAlgCl p)).isPrime
    have e : (t : PrimeSpectrum (PadicAlgCl p)).asIdeal = ⊥ := Ideal.eq_bot_of_prime _
    apply PrimeSpectrum.ext
    ext a
    change (a : PadicAlgCl p) ∈ (t : PrimeSpectrum (PadicAlgCl p)).asIdeal ↔
      ((σ a : OO p) : PadicAlgCl p) ∈ (t : PrimeSpectrum (PadicAlgCl p)).asIdeal
    rw [e]
    simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsExpansionTermUnitClosedFibre
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

namespace GlobalTheory.PsiRing

theorem exists_thick_eq_closedPoint (R : Type) [CommRing R] [IsLocalRing R] (I : Ideal R) (hI : I ≠ ⊤) (e : ℕ) :
    ∃ p, thick R I e p = IsLocalRing.closedPoint R := by
  have h : IsLocalRing.closedPoint R ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (I ^ (e + 1)))) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker, PrimeSpectrum.mem_zeroLocus]
    exact fun x hx => IsLocalRing.le_maximalIdeal hI (Ideal.pow_le_self (Nat.succ_ne_zero e) hx)
  exact h

theorem exists_unit_term :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), I ≠ ⊤ → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (k : ℕ) (σ : U.SecGT (𝟙_ _) k) (f : ∀ α, SecBT D (𝟙_ _) k α), U.ExpT (𝟙_ _) k σ f → FibNZ (𝟙_ _ ⊗ G).hom σ → ∃ (T : Over (Spec (CommRingCat.of R))) (y : T ⟶ D.P.A) (z : T.left) (J : (T.left ⟶ D.P.A.left) → D.P.L.ι) (α : D.X), Good D.P.L z J ∧ T.hom z = IsLocalRing.closedPoint R ∧ (∀ b ∈ I, Geo.Tor.cst T.hom z b = 0) ∧ IsUnit (sval (f α) (lift (toUnit T) y).left z J) := by
  intro R _ _ _ I hI D A G _ _ U k σ f hE hF
  obtain ⟨z₀, hz₀, hn⟩ := hF (IsLocalRing.closedPoint R)
  obtain ⟨p, hp⟩ := exists_thick_eq_closedPoint R I hI 0
  have h₁ : G.hom ((snd (𝟙_ _) G).left z₀) = thick R I 0 p := by
    rw [hp, ← hz₀, ← Scheme.Hom.comp_apply, Over.w]
  obtain ⟨z, hz, hz'⟩ := Scheme.Pullback.exists_preimage_pullback _ _ h₁
  let T : Over (Spec (CommRingCat.of R)) := (Over.map (thick R I 0)).obj (thickObj R I 0 G)
  let y : T ⟶ D.P.A := (U.gt 0).pG
  let x : T ⟶ G := fstG I 0 G
  have hG : (lift (toUnit T) x).left ≫ (snd _ G).left = x.left := by rw [← Over.comp_left, lift_snd]
  have hB : (lift (toUnit T) y).left ≫ (snd _ D.P.A).left = y.left := by rw [← Over.comp_left, lift_snd]
  have hf : (lift (toUnit T) y).left ≫ (fst _ D.P.A).left = (lift (toUnit T) x).left ≫ (fst _ G).left := by
    rw [← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]
  have hr : (lift (toUnit T) x).left z = z₀ := by
    have hi : lift (toUnit T) x = x ≫ (λ_ G).inv := by ext1 <;> simp [toUnit_unique]
    have hj : (snd (𝟙_ _) G).left ≫ (λ_ G).inv.left = 𝟙 _ := by
      rw [← Over.comp_left, ← leftUnitor_hom, Iso.hom_inv_id, Over.id_left]
    have hx : x.left z = (snd (𝟙_ _) G).left z₀ := hz
    rw [hi, Over.comp_left, Scheme.Hom.comp_apply, hx, ← Scheme.Hom.comp_apply, hj]
    rfl
  obtain ⟨JG, hJG⟩ := exists_good_pt (Z := T.left) U.P.L.isLB z
  obtain ⟨J, hJ⟩ := exists_good_pt (Z := T.left) D.P.isLB z
  obtain ⟨s, hs⟩ := hE 0
  obtain ⟨-, hsum⟩ := hs T.left (𝟙 _) _ _ (hG.trans (Category.id_comp _).symm) (hB.trans (Category.id_comp _).symm)
    hf z JG J hJG hJ
  have hu : IsUnit (sval σ (lift (toUnit T) x).left z JG) :=
    (MulPullSec.mem_nonzeroLocus_iff σ _ z hJG).1 (hr ▸ hn)
  obtain ⟨α, -, hα⟩ := IsLocalRing.exists_of_isUnit_sum
    ((congrArg IsUnit hsum).mp (((Units.isUnit _).pow k).mul hu))
  refine ⟨T, y, z, J, α, hJ, ?_, fun b hb => ?_, isUnit_of_mul_isUnit_left hα⟩
  · have : T.hom = pullback.snd G.hom (thick R I 0) ≫ thick R I 0 := rfl
    rw [this, Scheme.Hom.comp_apply, hz', hp]
  · refine (Geo.Tor.cst_comp (pullback.snd G.hom (thick R I 0)) (Ideal.Quotient.mk (I ^ (0 + 1))) z b).trans ?_
    rw [Ideal.Quotient.eq_zero_iff_mem.2 (by simpa using hb), Geo.Tor.cst, map_zero, gs_eq _ _ ⊤ trivial, map_zero,
      map_zero]

end GlobalTheory.PsiRing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFgSubalgebraSpecFactorThroughOpenStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fg_subalgebra_spec_factor_through_open : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω), R.FG → ∀ V : (Sp R).Opens, (V : Set (Sp R)).Nonempty → ∃ (R' : Subalgebra o Ω) (h : R ≤ R'), R'.FG ∧ ∃ τ : Sp R' ⟶ V.toScheme, τ ≫ V.ι = spMap (Subalgebra.inclusion h).toRingHom := by
  first | exact @GlobalTheory.exists_fg_subalgebra_spec_factors_open | exact GlobalTheory.exists_fg_subalgebra_spec_factors_open | (intros; apply GlobalTheory.exists_fg_subalgebra_spec_factors_open <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGoodTorsionTranslateGeometricPoint
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal

noncomputable section
namespace GlobalTheory.ThetaReal
open GlobalTheory.ThetaPtMove

theorem exists_good_translate : Laws → ∀ (S : Scheme.{0}) (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (n : ℕ), 2 ≤ n → (n : K) ≠ 0 → ∀ (th : LB.Sec (LPow P.A P.L 1 (baseOver S))), UnivBasis P 1 (fun _ : Fin 1 => SecM.ofSec P.A th) → ∀ a : Over.mk x ⟶ P.A, ∃ y : Over.mk x ⟶ P.A, y ^ n = 1 ∧ ∀ (z : baseOver S ⟶ P.A) (τ : LB.Gen (LB.LinComb P.L (Y := (baseOver S).left) (K := Fin 1) (fun _ => z.left) (fun _ => 1))) (v : Γ((baseOver S).left, ⊤)), (Over.homMk x (by simp) : Over.mk x ⟶ baseOver S) ≫ z = a * y → τ.IsGen → IsValueAt P.A P.L 1 th z τ v → v ≠ 0 := by
  intro hL S P K _ _ x n hn hK th hth a
  let β : Over.mk x ⟶ baseOver S := Over.homMk x (by simp)
  have : IsAffine (Over.mk x).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of K)))
  have : Nontrivial Γ((Over.mk x).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  obtain ⟨c, hc⟩ := hth (Over.mk x) β
  have h₀ : SecM.ofSec P.A (VVRank.pullS P.A 1 β th) ≠ 0 := fun e => c.ne_zero 0 ((hc 0).trans e)
  obtain ⟨y, hy, hu⟩ := GlobalTheory.UT.ExactTerm.exists_good_point hL.goodPt hL.polBaseChange P x hn hK _ h₀ a
  refine ⟨y, hy, fun z τ v hz _ hv h0 => ?_⟩
  let p : (Over.mk x).left := IsLocalRing.closedPoint K
  obtain ⟨J, hJ⟩ := GlobalTheory.ConstFam.exists_good' P.isLB p
  have q := hu p J hJ
  have e : (ptSecT P.A (a * y)).left ≫ (β ▷ P.A).left = β.left ≫ (ptSecT P.A z).left := by
    rw [← Over.comp_left, ← Over.comp_left, ← hz]
    congr 1
    ext1 <;> simp [ptSecT, β]
  rw [VVRank.sv_pullS _ _ _ _ _ _ hJ, e, sv_of_isValueAt hv _ p hJ, h0,
    GlobalTheory.UT.ExactTerm.gs_zero' β.left p ⊤ trivial, MulZeroClass.zero_mul] at q
  exact not_isUnit_zero q

end GlobalTheory.ThetaReal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsPullDegOfComparison
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

noncomputable section

namespace GlobalTheory.PsiRing

theorem exists_isPullDeg_of_cmp : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (φ : R →+* V) (D : DegPre R) (D' : DegPre V) (β : D'.P.A.left ⟶ D.P.A.left) (v : LB.Iso D'.P.L (D.P.L.pull β)) (xe : D'.X ≃+ D.X), IsGrpPullback D'.P.A D.P.A (spMap φ) β → v.IsGen → (∀ x, (D'.c x).left ≫ β = spMap φ ≫ (D.c (xe x)).left) → RigCmp φ D D' β v → ∀ gam : (TK V).left ⟶ (TK R).left, gam ≫ jK R = jK V ≫ spMap φ → PsiCmp D D' β v xe gam → D.TauBimult → ∃ hD : IsPullDeg φ D D', hD.e.hom.left ≫ pullback.fst _ _ = β ∧ HEq hD.w v ∧ hD.xe = xe := by
  intro R V _ _ _ _ φ D D' β v xe gp hv hc hr gam hgam hψ hB
  obtain ⟨e, me, he⟩ := grpPullback_iso gp (isGrpPullback_pullback D.P.A (specOf φ))
  subst he
  have hE : eSec D'.P.A ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) = specOf φ ≫ eSec D.P.A :=
    (cubeMapOf gp).e_comm
  obtain ⟨W, hW, ⟨ψW⟩⟩ := PsiSpread.exists_psiOn D hB
  obtain ⟨gW, hgW⟩ : ∃ gW : (TK R).left ⟶ (TW W).left, gW ≫ W.ι = jK R :=
    ⟨IsOpenImmersion.lift W.ι (jK R) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact TauPull.jK_mem y W ⟨_, hW⟩), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨lam, l₁, l₂⟩ : ∃ lam : (TK R).left ⟶ (jK R ⁻¹ᵁ W).toScheme, lam ≫ (jK R ⁻¹ᵁ W).ι = 𝟙 _ ∧
      lam ≫ (jK R ∣_ W) = gW :=
    ⟨(isPullback_morphismRestrict (jK R) W).lift _ _ (hgW.trans (Category.id_comp _).symm),
      (isPullback_morphismRestrict (jK R) W).lift_snd _ _ _,
      (isPullback_morphismRestrict (jK R) W).lift_fst _ _ _⟩
  refine ⟨⟨e, me, v, hv, hE, ?_, xe, hc, W, ψW, gam ≫ gW,
    (Category.assoc _ _ _).trans ((congrArg (gam ≫ ·) hgW).trans hgam), fun x => ?_⟩, rfl, HEq.rfl, rfl⟩
  · exact (maps_iff v _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf φ) _
      (rigPull_le (G' := D'.P.A) (G := D.P.A) _ (specOf φ) hE D.P.L) (fun _ => rfl)).2 hr
  · obtain ⟨b, -, vb⟩ := exists_up ((isGen_iff v).1 hv) D.P.isLB D'.P.isLB (D'.psi x) (D'.psi_gen x)
    have hx : D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) = gam ≫ D.xK (xe x) :=
      (Category.assoc _ _ _).trans ((congrArg (jK V ≫ ·) (hc x)).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ (D.c (xe x)).left) hgam.symm).trans (Category.assoc _ _ _))))
    refine ⟨b, fun jN jL => unit_ext fun y hy => ?_, corr_of_val D.P.isLB fun y J hJ => ?_⟩
    · have e₁ := vb _ (𝟙 _) y jN (fun _ => jL) (GeneratorPullback.mapsAt_le_b _ _ _ _ jN jL hy) (GeneratorPullback.mapsAt_le_a _ _ _ _ jN jL hy)
      rw [pw, Fintype.prod_unique] at e₁
      refine (gm_res _ y _ hy _).trans (e₁.trans (Eq.symm ((map_mul _ _ _).trans
        (congrArg₂ (· * ·) ?_ (gm_res _ y _ hy _)))))
      exact (map_zpow _ _ _).trans (congrArg (· ^ (-1 : ℤ)) (gm_pull _ _ y _ hy _))
    · obtain ⟨q, hq⟩ := exists_chart D'.P.isLB (D'.xK x y)
      obtain ⟨p, hp⟩ : ∃ p, p = J (D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) := ⟨_, rfl⟩
      have mp : (e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) (D'.xK x y) ∈ D.P.L.U p := hp ▸ hJ _
      have e₁ := vb _ (𝟙 _) y (fun _ => p) (fun _ => q) (Set.mem_iInter.2 fun _ => mp) (Set.mem_iInter.2 fun _ => hq)
      have e₂ := hψ x _ (𝟙 _) y (fun _ => p) (fun _ => q) (fun _ => mp) (fun _ => hq)
      have w₁ := (val_pull hJ _ _ _).symm.trans ((val_corr hJ (ψW.psi_eq (xe x)) (gam ≫ lam)).trans (val_pull hJ _ _ _))
      rw [Category.assoc, Category.assoc, l₁, l₂, Category.comp_id] at w₁
      refine (val_of b _ y J (fun _ => p) (fun _ => by rw [Category.id_comp, hp])).trans (e₁.trans (e₂.symm.trans
        (Eq.trans ?_ (val_pull hJ _ _ _).symm)))
      rw [Category.id_comp, Category.id_comp]
      exact (val_of (D.psi (xe x)) gam y J (fun _ => p) (fun _ => by rw [hp, hx])).symm.trans w₁.symm

end GlobalTheory.PsiRing

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsPullDegOfVal
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

noncomputable section
namespace GlobalTheory.FieldPull
open GlobalTheory.ArcPull GlobalTheory.PsiEvenPull

theorem nonempty_psiOn_field {K : Type} [Field K] (D : DegPre K) : Nonempty (PsiOn D ⊤) := by
  refine nonempty_psiOn_top D fun χ => (psiUnitOn_univ_iff D χ).2 ?_
  let σ : FractionRing K ≃+* K := (FractionRing.algEquiv K K).toRingEquiv
  let s : Sp K ⟶ (TK K).left := spMap σ.toRingHom
  have h₁ : s ≫ jK K = 𝟙 _ := by
    refine (spMap_comp _ _).symm.trans ((congrArg spMap (RingHom.ext fun x => ?_)).trans (Spec.map_id (CommRingCat.of K)))
    exact (FractionRing.algEquiv K K).commutes x
  have h₂ : jK K ≫ s = 𝟙 _ := by
    refine (spMap_comp _ _).symm.trans ((congrArg spMap (RingHom.ext fun x => ?_)).trans (Spec.map_id (CommRingCat.of (FractionRing K))))
    exact (FractionRing.algEquiv K K).injective ((FractionRing.algEquiv K K).commutes _)
  obtain ⟨t, ht, vt⟩ := exists_gen D.P.isLB (K' := PUnit) (φ' := fun _ => ((D.c χ).left : Sp K ⟶ _)) (ε' := fun _ => -1)
    (fun U _ h => Finset.prod_congr rfl fun _ _ => congrArg (fun q => h q ^ (-1 : ℤ)) (by
      show s ≫ jK K ≫ (D.c χ).left = _
      rw [← Category.assoc, h₁, Category.id_comp]))
    (LB.pullGen D.P.L _ _ (D.psi χ) s) (DVR.pullGen_isGen _ _ _ _ (D.psi_gen χ) s)
  refine ⟨t, ht, corr_of_val D.P.isLB fun y J hJ => ?_⟩
  refine (val_pull hJ _ _ _).trans ((vt _ _ y J hJ).trans ((val_pull hJ _ _ _).trans ?_))
  exact congrArg (fun q => val (D.psi χ) q y J) ((Category.assoc _ _ _).trans
    ((congrArg (𝟙 _ ≫ ·) h₂).trans (Category.id_comp _)))

theorem exists_isPullDeg_of_val {K₀ K : Type} [Field K₀] [Field K] (i : K₀ →+* K) (D : DegPre K₀) (D' : DegPre K)
    {Φ : D'.P.A.left ⟶ D.P.A.left} (gp : IsGrpPullback D'.P.A D.P.A (spMap i) Φ)
    (w : LB.Iso D'.P.L (D.P.L.pull Φ)) (hw : PGen w)
    (hr : PMaps w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => eSec D.P.A) (fun _ => 1) D'.rig D.rig (spMap i))
    (xe : D'.X ≃+ D.X) (hc : ∀ x, (D'.c x).left ≫ Φ = spMap i ≫ (D.c (xe x)).left)
    (hψ : ∀ (x : D'.X) (z : (TK K).left) J J', Good D.P.L z J → Good D'.P.L z J' →
      val (D.psi (xe x)) (genMap i.injective) z J = (om w z J J' (D'.xK x))⁻¹ * val (D'.psi x) (𝟙 _) z J') :
    ∃ hD : IsPullDeg i D D', proj hD = Φ ∧ hD.xe = xe ∧ HEq hD.w w := by
  obtain ⟨ψW⟩ := nonempty_psiOn_field D
  obtain ⟨e, e_hom, he⟩ := grpPullback_iso gp (isGrpPullback_pullback D.P.A (specOf i))
  subst he
  have hE : eSec D'.P.A ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) = specOf i ≫ eSec D.P.A :=
    (cubeMapOf gp).e_comm
  obtain ⟨g, hg⟩ : ∃ g : (TK K).left ⟶ (TW (⊤ : (Sp K₀).Opens)).left, g ≫ (⊤ : (Sp K₀).Opens).ι = jK K ≫ specOf i :=
    ⟨IsOpenImmersion.lift (⊤ : (Sp K₀).Opens).ι (jK K ≫ specOf i) (by
      rw [Scheme.Opens.range_ι]; exact Set.subset_univ _), IsOpenImmersion.lift_fac _ _ _⟩
  have sq : g ≫ (⊤ : (Sp K₀).Opens).ι = genMap i.injective ≫ jK K₀ :=
    hg.trans ((Category.id_comp _).symm.trans (fracMap_sq i.injective))
  obtain ⟨lam, l₁, l₂⟩ : ∃ lam : (TK K).left ⟶ (jK K₀ ⁻¹ᵁ ⊤).toScheme, lam ≫ (jK K₀ ⁻¹ᵁ ⊤).ι = genMap i.injective ∧
      lam ≫ (jK K₀ ∣_ ⊤) = g :=
    ⟨(isPullback_morphismRestrict (jK K₀) ⊤).lift _ _ sq,
      (isPullback_morphismRestrict (jK K₀) ⊤).lift_snd _ _ _,
      (isPullback_morphismRestrict (jK K₀) ⊤).lift_fst _ _ _⟩
  have hx : ∀ x, g ≫ (toUnit (TW ⊤) ≫ D.c (xe x)).left =
      D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) := fun x => by
    show g ≫ (⊤ : (Sp K₀).Opens).ι ≫ (D.c (xe x)).left = (jK K ≫ (D'.c x).left) ≫ _
    rw [Category.assoc, hc, ← Category.assoc, hg, Category.assoc]
  choose b hb vb using fun x => exists_gen D.P.isLB (K' := PUnit)
    (φ' := fun _ => D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i)) (ε' := fun _ => -1)
    (fun U _ h => Finset.prod_congr rfl fun _ _ => congrArg (fun q => h q ^ (-1 : ℤ)) (hx x))
    (LB.pullGen D.P.L _ _ (ψW.psi (xe x)) g) (DVR.pullGen_isGen _ _ _ _ (ψW.psi_gen _) g)
  choose psi hpsi vpsi using fun x => DegPull.exists_down_val hw D.P.isLB D'.P.isLB (K := PUnit)
    (φ' := fun _ => D'.xK x) (ε := fun _ => -1) (fun _ => rfl) (b x) (hb x)
  have eψ : ∀ x, psi x = D'.psi x := fun x => TorusExt.gen_ext_val D'.P.isLB (hpsi x) (D'.psi_gen x) fun y J' hJ' => by
    obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB y
    have v := vpsi x _ (𝟙 _) y _ _ (hJ.mem _ (𝟙 _)) (hJ'.mem _ (𝟙 _))
    have u := (val_pull hJ _ _ _).symm.trans ((val_corr hJ (ψW.psi_eq (xe x)) lam).trans (val_pull hJ _ _ _))
    rw [l₁, l₂, hψ x y J J' hJ hJ'] at u
    have v₁ : val (b x) (𝟙 _) y J = val (ψW.psi (xe x)) g y J :=
      (vb x _ _ y J hJ).trans ((val_pull hJ _ _ _).trans (by rw [Category.id_comp]))
    have v₂ : val (b x) (𝟙 _) y J = (om w y J J' (D'.xK x))⁻¹ * val (psi x) (𝟙 _) y J' := by
      refine v.trans (congrArg₂ (· * ·) ?_ rfl)
      rw [pw, Fintype.prod_unique, zpow_neg_one]
      simp only [om, Category.id_comp]
    exact mul_left_cancel (v₂.symm.trans (v₁.trans u))
  refine ⟨⟨e, e_hom, w, (isGen_iff w).2 hw, hE, ?_, xe, hc, ⊤, ψW, g, hg, fun x => ⟨b x, fun jN jL => ?_,
      corr_of_val D.P.isLB fun y J hJ => vb x _ _ y J hJ⟩⟩, rfl, rfl, HEq.rfl⟩
  · exact (maps_iff w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf i) _
      (rigPull_le (G' := D'.P.A) (G := D.P.A) _ (specOf i) hE D.P.L) (fun _ => rfl)).2 hr
  · rw [← eψ]
    refine unit_ext fun y hy => ?_
    have v := vpsi x _ (𝟙 _) y jN (fun _ => jL) (GeneratorPullback.mapsAt_le_b _ _ _ _ jN jL hy) (GeneratorPullback.mapsAt_le_a _ _ _ _ jN jL hy)
    refine (gm_res _ y _ hy _).trans (v.trans (Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_
      (gm_res _ y _ hy _)))))
    rw [pw, Fintype.prod_unique]
    exact (map_zpow _ _ _).trans (congrArg (· ^ (-1 : ℤ)) (gm_pull (𝟙 _) _ y _ hy _))

theorem pmaps_rig {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
    {D' : DegPre R'} (hD : IsPullDeg φ D D') :
    PMaps hD.w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => eSec D.P.A) (fun _ => 1) D'.rig D.rig (spMap φ) :=
  (maps_iff hD.w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf φ) _
    (rigPull_le (proj hD) (specOf φ) hD.he D.P.L) (fun _ => rfl)).1 hD.w_rig

end GlobalTheory.FieldPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPsiGeneratingOnWholeSpectrumStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_psi_generating_on_whole_spectrum : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R), ∃ ψ h, Nonempty (PsiOn (setPsi D ψ h) ⊤) := by
  first | exact @GlobalTheory.PsiTop.exists_setPsi_psiOn_top | exact GlobalTheory.PsiTop.exists_setPsi_psiOn_top | (intros; apply GlobalTheory.PsiTop.exists_setPsi_psiOn_top <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FourthSideRespectsRigSymmetryCubeStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourthSide_respects_rig_symmetry_cube : ∀ (hG : GlobalFnsSt) (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (I : Ideal R) (I' : Ideal V) (φ : R →+* V), I.map φ ≤ I' → ∀ (D : DegPre R) (D' : DegPre V) (A : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of V))) [GrpObj G'] [IsCommMonObj G'] (U : PreU I D A G) (P' : CP G') (F : G'.left ⟶ G.left) (hF : F ≫ G.hom = G'.hom ≫ spMap φ) (wL : LB.Iso P'.L.L (U.P.L.L.pull F)), IsCPMap P' U.P (spMap φ) F hF wL → ∀ (β : D'.P.A.left ⟶ D.P.A.left) (hβ : β ≫ D.P.A.hom = D'.P.A.hom ≫ spMap φ) (v : LB.Iso D'.P.L (D.P.L.pull β)), IsCPMap (CP.ofDegPre hG D') (CP.ofDegPre hG D) (spMap φ) β hβ v → ∀ (e : ℕ) (g' : GtCoord I' D' e G') (h : (thickObj V I' e G').left ⟶ (thickObj R I e G).left), h ≫ (fstG I e G).left = (fstG I' e G').left ≫ F → g'.pG.left ≫ β = h ≫ (U.gt e).pG.left → ∀ w' : LB.Iso (P'.L.L.pull (fstG I' e G').left) (D'.P.L.pull g'.pG.left), (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj V I' e G').left) (z : Z) (jM : D.P.L.ι) (jM' : D'.P.L.ι) (jL : U.P.L.L.ι) (jL' : P'.L.L.ι), β (g'.pG.left (r z)) ∈ D.P.L.U jM → g'.pG.left (r z) ∈ D'.P.L.U jM' → F ((fstG I' e G').left (r z)) ∈ U.P.L.L.U jL → (fstG I' e G').left (r z) ∈ P'.L.L.U jL' → gw v (r ≫ g'.pG.left) z jM jM' * gw w' r z jM' (fun _ => jL') = gw (U.w e) (r ≫ h) z jM (fun _ => jL) * gw wL (r ≫ (fstG I' e G').left) z jL jL') → ∀ (T : Over (Spec (CommRingCat.of (V ⧸ I' ^ (e + 1))))) (z : T.left) (JG : (T.left ⟶ G'.left) → P'.L.L.ι) (J : (T.left ⟶ D'.P.A.left) → D'.P.L.ι), Good P'.L.L z JG → Good D'.P.L z J → ∀ W : (T ⟶ thickObj V I' e G') → (T.left.presheaf.stalk z)ˣ, (∀ x, W x = gw w' x.left z (J (x.left ≫ g'.pG.left)) (fun _ => JG (x.left ≫ (fstG I' e G').left))) → (val (L := D'.P.L) (φ := fun _ : PUnit => eSec D'.P.A) (ε := fun _ => 1) D'.rig (T.hom ≫ thick V I' e) z J = W 1 * val (L := P'.L.L) (φ := fun _ : PUnit => eSec G') (ε := fun _ => 1) P'.L.rig (T.hom ≫ thick V I' e) z JG) ∧ (∀ x : T ⟶ thickObj V I' e G', val D'.sym (x.left ≫ g'.pG.left) z J * W x = W x⁻¹ * val P'.sym (x.left ≫ (fstG I' e G').left) z JG) ∧ ∀ x y u : T ⟶ thickObj V I' e G', @id (T.left.presheaf.stalk z)ˣ (cubV D'.cub (T := (Over.map (thick V I' e)).obj T) z J ((Over.map (thick V I' e)).map x ≫ g'.pG) ((Over.map (thick V I' e)).map y ≫ g'.pG) ((Over.map (thick V I' e)).map u ≫ g'.pG)) * W (x * y) * W (x * u) * W (y * u) * W 1 = W (x * y * u) * W x * W y * W u * @id (T.left.presheaf.stalk z)ˣ (cubV P'.c (T := (Over.map (thick V I' e)).obj T) z JG ((Over.map (thick V I' e)).map x ≫ fstG I' e G') ((Over.map (thick V I' e)).map y ≫ fstG I' e G') ((Over.map (thick V I' e)).map u ≫ fstG I' e G')) := by
  first | exact @GlobalTheory.LN.FourthSide.fourth_side_vals | exact GlobalTheory.LN.FourthSide.fourth_side_vals | (intros; apply GlobalTheory.LN.FourthSide.fourth_side_vals <;> assumption)
end

