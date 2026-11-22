import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1876
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2212
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2213
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalRingCardinality.Bundle0007
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0015
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1682
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2166
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2192
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2112
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2099
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2143
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2188
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2139
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2214
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2183

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftLeftInvariant
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThKRatInv

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem resEtaPow_div {K : Subgroup (AF F)ˣ} {χ χ' : Chr F E} {n m : ℕ} (h : ResEtaPow K χ n) (h' : ResEtaPow K χ' m) :
    ResEtaPow K (χ / χ') (n + m) := by
  intro x
  rw [MonoidHom.div_apply, Circle.coe_div, h x, h' x]
  split_ifs
  · simp
  · rw [pow_add, div_eq_mul_inv, ← inv_pow, inv_neg_one]

theorem isHecke_div {χ χ' : Chr F E} (h : IsHecke F E χ) (h' : IsHecke F E χ') : IsHecke F E (χ / χ') := by
  refine ⟨?_, fun x => ?_⟩
  · show Continuous fun x => χ x / χ' x
    exact h.1.div' h'.1
  · rw [MonoidHom.div_apply, h.2 x, h'.2 x, div_one]

theorem polData_le_schA {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (B : Base F E) (M : Model σ X W) (hM : M.IsGood B.ψ) :
    PolData B M ≤ schA F (Fin n × Fin d) := by
  refine Submodule.span_le.2 ?_
  rintro Φ ⟨f, -, φ, hSB, hev, rfl⟩
  exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB ((hev.and hM.std).mono fun v hv => hv.1.trans hv.2)

theorem I_rat_inv (hT : ThetaBasic) {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (B : Base F E) (M : Model σ X W)
    {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ} (hP : IsPair B M χX χW om r s r' s')
    (Φ : Fn F n d) (hΦ : Φ ∈ PolData B M) (γ : UA σ W.J) (hγ : γ ∈ ratU σ W.J) (h : UA σ W.J) :
    M.I om Φ (γ * h) = M.I om Φ h := by
  have hS : Φ ∈ schA F (Fin n × Fin d) := polData_le_schA B M hP.good hΦ
  have hinv := ((hT F E σ B n d X W M χX χW om r s r' s' hP).1 Φ hS).2.1
  unfold Model.I
  congr 1
  funext g
  simpa using hinv 1 (one_mem _) γ hγ g h

theorem ratInv : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → (∀ Φ ∈ PolData B G.M, ∀ γ ∈ ratU σ G.W.J, ∀ h, G.M.I om Φ (γ * h) = G.M.I om Φ h) ∧ ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ γ ∈ ratU σ G.W.J, ∀ h, G.M'.I om' Φ' (γ * h) = G.M'.I om' Φ' h := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ _
  have hTB : ThetaBasic := GlobalTheory.T.theta_basic_properties hK.base
  have hV : IsPair B G.M X.β (X.β / X.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) :=
    { base := hT.base, herm := hT.geo.hV, skew := hT.geo.hW, good := hT.geo.hM, hX := hT.chars.heckeβ,
      hW := isHecke_div hT.chars.heckeβ hT.chars.heckeα, resX := hT.chars.resβ,
      resW := resEtaPow_div hT.chars.resβ hT.chars.resα, weil := hT.weil }
  have hV' : IsPair B G.M' X.α (X.α / X.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) :=
    { base := hT.base, herm := hT.geo.hV', skew := hT.geo.hW, good := hT.geo.hM', hX := hT.chars.heckeα,
      hW := isHecke_div hT.chars.heckeα hT.chars.heckeβ, resX := hT.chars.resα,
      resW := by rw [add_comm a a']; exact resEtaPow_div hT.chars.resα hT.chars.resβ, weil := hT.weil' }
  exact ⟨fun Φ hΦ γ hγ h => I_rat_inv hTB B G.M hV Φ hΦ γ hγ h,
    fun Φ' hΦ' γ hγ h => I_rat_inv hTB B G.M' hV' Φ' (Submodule.mem_inf.1 hΦ').1 γ hγ h⟩

end GlobalTheory.ThKRatInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaOneMapBaseTupleOfCharacterisationExtremalStatement
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaOneMap_baseTuple_of_characterisation_extremal : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → TieIn T R κ v₀ → IoExt R → ∀ (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (i : Fin D.R.m), OMPins T R κ v₀ O i → OneMapRow0 T R κ v₀ O i := by
  first | exact @GlobalTheory.OneMapTies.oneMapRow0_of_ties_core | exact GlobalTheory.OneMapTies.oneMapRow0_of_ties_core | (intros; apply GlobalTheory.OneMapTies.oneMapRow0_of_ties_core <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaOneMapIdentityEveryNormalisedFamilyStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaOneMap_identity_every_normalised_family : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) , GlobalTheory.Hk3.Core R F → TieIn T R κ v₀ → IoExt R → ∀ i, GlobalTheory.OneMapAll.IdentityRow T R κ v₀ i := by
  first | exact @GlobalTheory.OneMapAll.identityRow_of_core | exact GlobalTheory.OneMapAll.identityRow_of_core | (intros; apply GlobalTheory.OneMapAll.identityRow_of_core <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSectionInverseImageBaseProductFunction
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.Cl

theorem lpow_le {S : Scheme.{0}} (P : PolAV S) (T : Over S) (k : ℤ) (j : Fin 1 → P.L.ι) :
    (LPow P.A P.L k T).U j ≤ (snd T P.A).left ⁻¹ᵁ P.L.U (j 0) :=
  LB.wchart_le P.L (fun _ : Fin 1 => (snd T P.A).left) j 0

theorem appLE_swap {X Y : Scheme.{0}} (φ : Y ⟶ X) {U U' : X.Opens} {V V' : Y.Opens} (h : V ≤ φ ⁻¹ᵁ U) (h' : V' ≤ φ ⁻¹ᵁ U')
    (a : V' ≤ V) (b : U' ≤ U) (f : Γ(X, U)) :
    (Y.presheaf.map (homOfLE a).op).hom ((φ.appLE U V h).hom f) =
      (φ.appLE U' V' h').hom ((X.presheaf.map (homOfLE b).op).hom f) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

theorem linComb_g_one {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (i j : Fin 1 → L.ι) :
    ((LB.LinComb L (fun _ : Fin 1 => φ) (fun _ => ((1 : ℕ) : ℤ))).g i j).val =
      (φ.appLE (L.U (i 0) ⊓ L.U (j 0)) (LB.wchart L (fun _ : Fin 1 => φ) i ⊓ LB.wchart L (fun _ : Fin 1 => φ) j)
        (le_inf (inf_le_left.trans (LB.wchart_le L (fun _ : Fin 1 => φ) i 0))
          (inf_le_right.trans (LB.wchart_le L (fun _ : Fin 1 => φ) j 0)))).hom (L.g (i 0) (j 0)).val := by
  unfold LB.LinComb
  dsimp only
  rw [Fin.prod_univ_one, Nat.cast_one, zpow_one]
  rfl

def pullSec1 {S : Scheme.{0}} (P : PolAV S) (T : Over S) (s : P.L.Sec) :
    LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) T) where
  f j := ((snd T P.A).left.appLE _ _ (lpow_le P T _ j)).hom (s.f (j 0))
  compat i j := by
    have h := congrArg ((snd T P.A).left.appLE (P.L.U (i 0) ⊓ P.L.U (j 0))
      ((LPow P.A P.L ((1 : ℕ) : ℤ) T).U i ⊓ (LPow P.A P.L ((1 : ℕ) : ℤ) T).U j)
      (le_inf (inf_le_left.trans (lpow_le P T _ i)) (inf_le_right.trans (lpow_le P T _ j)))).hom (s.compat (i 0) (j 0))
    rw [map_mul] at h
    refine (appLE_swap _ _ _ _ _ _).trans (h.trans (congrArg₂ (· * ·) ?_ (appLE_swap _ _ _ _ _ _).symm))
    exact (linComb_g_one P.L (snd T P.A).left i j).symm

theorem pullbackSectionToBaseChangedAbelian_isInverseImage {S : Scheme.{0}} (P : PolAV S) (T : Over S) (s : P.L.Sec) : IsPolAVSectionInverseImage P T s (pullSec1 P T s) :=
  fun _ _ => rfl

theorem ptSecT_snd' {S : Scheme.{0}} (A : Over S) [GrpObj A] {T : Over S} (z : T ⟶ A) :
    (ptSecT A z).left ≫ (snd T A).left = z.left := by
  rw [← Over.comp_left, ptSecT, lift_snd]

theorem valR_appLE' {R : Type} [CommRing R] {X Y : Scheme.{0}} (x : Sp R ⟶ Y) (φ : Y ⟶ X) (U : X.Opens) (V : Y.Opens)
    (h : V ≤ φ ⁻¹ᵁ U) (hx : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(X, U)) :
    valR x V ((φ.appLE U V h).hom f) = valR (x ≫ φ) U f := by
  have h' : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U := fun p hp => h (hx hp)
  rw [valR, valR, dif_pos hx, dif_pos h', ← CommRingCat.comp_apply (φ.appLE U V h), Scheme.Hom.appLE_comp_appLE]

theorem valR_eq_valAt' {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (U : X.Opens) (f : Γ(X, U)) : valR x U f = valAt' x U f := by
  unfold valR valAt' valAt
  congr

theorem powerSectionFunctionInFrame_of_inverseImage {P : PolAV (Sp ℂ)} {g : ℕ} (u : HolUnif P.A P.L g) (s : P.L.Sec) (θ) (h : u.IsFn s θ)
    (th) (H : IsPolAVSectionInverseImage P (baseOver (Sp ℂ)) s th) : FnT u 1 th θ := by
  intro i z hz
  have e := ptSecT_snd' P.A (T := baseOver (Sp ℂ)) (u.ex z)
  have hx : ⊤ ≤ (ptSecT P.A (T := baseOver (Sp ℂ)) (u.ex z)).left ⁻¹ᵁ
      (LPow P.A P.L ((1 : ℕ) : ℤ) (baseOver (Sp ℂ))).U (fun _ => i) := fun p hp =>
    val_le P.A P.L (T := baseOver (Sp ℂ)) (u.ex z) (fun _ => i) (Set.mem_iInter.2 fun _ => hz hp)
  rw [H i (lpow_le P _ _ fun _ => i), pow_one, ← h i z hz, ← valR_eq_valAt']
  refine (valR_appLE' _ _ _ _ _ hx _).trans ?_
  exact congrArg (fun y => valR y (P.L.U i) (s.f i)) e

theorem eq_of_fnT {P : PolAV (Sp ℂ)} {g : ℕ} (u : HolUnif P.A P.L g) (k : ℕ)
    (t t' : LB.Sec (LPow P.A P.L (k : ℤ) (baseOver (Sp ℂ)))) (f) (h : FnT u k t f) (h' : FnT u k t' f) (j) :
    t.f j = t'.f j := by
  obtain ⟨i, rfl⟩ : ∃ i : P.L.ι, j = fun _ => i := ⟨j 0, funext fun a => congrArg j (Subsingleton.elim _ _)⟩
  have hp : (baseOver (Sp ℂ) ⊗ P.A).hom = pullback.fst (𝟙 (Sp ℂ)) P.A.hom := Category.comp_id _
  have := P.isAb.smooth
  have : Smooth (baseOver (Sp ℂ) ⊗ P.A).hom := by rw [hp]; infer_instance
  have := isReduced_of_smooth_complex _ (baseOver (Sp ℂ) ⊗ P.A).hom inferInstance
  refine ComplexPoints.eq_of_valAt'_eq (baseOver (Sp ℂ) ⊗ P.A).hom _ _ _ fun x hx hi => ?_
  let x' : baseOver (Sp ℂ) ⟶ baseOver (Sp ℂ) ⊗ P.A := Over.homMk x hx
  obtain ⟨z, hz⟩ := u.ex_onto (x' ≫ snd _ _)
  have e : ptSecT P.A (T := baseOver (Sp ℂ)) (u.ex z) = x' := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [ptSecT, lift_fst]
      refine Over.OverMorphism.ext ?_
      exact ((Category.comp_id _).symm.trans (Over.w (x' ≫ fst _ _))).symm
    · rw [ptSecT, lift_snd]; exact hz
  obtain rfl : (ptSecT P.A (T := baseOver (Sp ℂ)) (u.ex z)).left = x := congrArg (·.left) e
  have hz' : ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i := by
    intro p hp
    have := lpow_le P _ (k : ℤ) (fun _ => i) (hi hp)
    rw [← ptSecT_snd' P.A (T := baseOver (Sp ℂ)) (u.ex z)]
    exact this
  rw [← valR_eq_valAt', ← valR_eq_valAt']
  exact (h i z hz').trans (h' i z hz').symm

theorem thetaSection_fnT_thetaChar_and_unique : ∀ (g : ℕ) (x : KeyIn ℂ) (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (c : ℂ) (W : Fin g → Fin g → ℂ), NF x hg u τ a b c W → (∃ th, IsPolAVSectionInverseImage x.P (baseOver (Sp ℂ)) x.th th) ∧ (∀ th, IsPolAVSectionInverseImage x.P (baseOver (Sp ℂ)) x.th th → FnT u 1 th fun z => c * thetaChar τ a b z) ∧ ∀ (k : ℕ) (t t' : LB.Sec (LPow x.P.A x.P.L (k : ℤ) (baseOver (Sp ℂ)))) f, FnT u k t f → FnT u k t' f → ∀ j, t.f j = t'.f j :=
  fun _ x _ u _ _ _ _ _ h => ⟨⟨_, pullbackSectionToBaseChangedAbelian_isInverseImage x.P _ x.th⟩, powerSectionFunctionInFrame_of_inverseImage u x.th _ h.2.2.2.2.2.2.2.1,
    fun k t t' f => eq_of_fnT u k t t' f⟩

end GlobalTheory.MBLow.Cl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopPairDForm
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogKSDiv

open TopForm

section Pair

variable {k A : Type} [CommRing k] [CommRing A] (α : k →+* A) {n : ℕ}

def topPair (D : Fin n → (letI := α.toAlgebra; Derivation k A A)) : Forms α n →ₗ[A] A :=
  letI := α.toAlgebra
  exteriorPower.alternatingMapLinearEquiv (Matrix.detRowAlternating.compLinearMap
    (LinearMap.pi fun j => (KaehlerDifferential.linearMapEquivDerivation k A).symm (D j)))

end Pair

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

abbrev PairIx (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) : Type :=
  Σ τ : {τ : E →+* ℂ // τ (H.rt : E) = H.rt0}, Fin (Dw.mult τ.1) × Fin (Dw.mult ((starRingEnd ℂ).comp τ.1))

def symPair {R : Type} [CommRing R] {n : ℕ} (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (P : PairIx H Dw) :
    Matrix (Fin n) (Fin n) R :=
  Matrix.of fun a b =>
    (if a = e ⟨P.1.1, P.2.1⟩ ∧ b = e ⟨(starRingEnd ℂ).comp P.1.1, P.2.2⟩ then 1 else 0) +
      (if a = e ⟨(starRingEnd ℂ).comp P.1.1, P.2.2⟩ ∧ b = e ⟨P.1.1, P.2.1⟩ then 1 else 0)

abbrev genPt (TF : TorFlag Xo c) (Z : Comp Xo c) [IsIntegral (X₀ TF.Y Z)] : Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z :=
  (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))

abbrev GenDer (TF : TorFlag Xo c) (Z : Comp Xo c) [IsIntegral (X₀ TF.Y Z)] : Type :=
  letI := (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)).toAlgebra
  Derivation c.F (X₀ TF.Y Z).functionField (X₀ TF.Y Z).functionField

def GenKS (TF : TorFlag Xo c) (Z : Comp Xo c) [IsIntegral (X₀ TF.Y Z)]
    (w : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber (X₀ TF.Y Z).functionField) ⟶ TF.Y.t.G.left))
    (D : Fin Dw.dim → GenDer TF Z) : Prop :=
  letI := (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)).toAlgebra
  ∃ (U : TF.Y.X.affineOpens) (_ : U.1 ≤ barComp TF.Y Z) (ρ : Γ(TF.Y.X, U.1) →+* (X₀ TF.Y Z).functionField)
    (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n)
    (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)) (ε : Fin Dw.dim ≃ PairIx H Dw)
    (Dl : Fin Dw.dim → LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U),
    spMap ρ ≫ LogKS.chart U = genPt TF Z ≫ (barComp TF.Y Z).ι ∧
    (∀ i, IsTanAtG TF.Y.t (LogKS.chart U) (v i)) ∧
    (∀ w', IsTanAtG TF.Y.t (LogKS.chart U) w' →
      ∃! cf : Fin n → Γ(TF.Y.X, U.1), IsCombAtG TF.Y.t (LogKS.chart U) v cf w') ∧
    (∀ τ i, w τ i = spMap (dualMap ρ) ≫ v (e ⟨τ, i⟩)) ∧
    (∀ j, LogKS.IsKS TF.Y.t (LogKS.interior TF.Y) U v (Dl j).1 (symPair e (ε j))) ∧
    ∀ j r, (show Derivation c.F (X₀ TF.Y Z).functionField (X₀ TF.Y Z).functionField from D j) (ρ r) = ρ ((Dl j).1 r)

end GlobalTheory.LogKSDiv

namespace GlobalTheory.LogKSDiv

open TopForm

theorem topPair_dForm {k A : Type} [CommRing k] [CommRing A] (α : k →+* A) {n : ℕ}
    (D : Fin n → (letI := α.toAlgebra; Derivation k A A)) (f : Fin n → A) :
    topPair α D (dForm α f) = (Matrix.of fun i j => (letI := α.toAlgebra; (D j : Derivation k A A)) (f i)).det := by
  letI := α.toAlgebra
  rw [dForm_eq, topPair, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, AlternatingMap.compLinearMap_apply]
  change Matrix.det (Matrix.of _) = _
  congr 1
  ext i j
  exact Derivation.liftKaehlerDifferential_comp_D (D j) (f i)

end GlobalTheory.LogKSDiv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopSelfIntersectionNefLeCuspFormGrowth
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic
open GlobalTheory.ThickeningDetermines (secIdeal)
open scoped TensorProduct
open NumberField Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.HSApp
open GlobalTheory.AllWt (wtOf cuspOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open Filter
open scoped ENNReal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NefCuspGrowth

theorem ofReal_le_growth (D : ℕ) (h : ℕ → ℕ) (r : ℕ → ℕ∞) {c : ℝ} (hc : 0 ≤ c)
    (ht : Tendsto (fun m : ℕ => (h m : ℝ) / (m : ℝ) ^ D) atTop (nhds (c / D.factorial)))
    (hle : ∀ m, (h m : ℕ∞) ≤ r (m + 1)) : ENNReal.ofReal c ≤ CompHt.growth D r := by
  have hf : (0 : ℝ) < D.factorial := by positivity
  have h1 : Tendsto (fun m : ℕ => (m : ℝ) / ((m : ℝ) + 1)) atTop (nhds 1) := tendsto_natCast_div_add_atTop 1
  have h2 : Tendsto (fun m : ℕ => (D.factorial : ℝ) * ((h m : ℝ) / (m : ℝ) ^ D * ((m : ℝ) / ((m : ℝ) + 1)) ^ D))
      atTop (nhds c) := by
    have := (ht.mul (h1.pow D)).const_mul (D.factorial : ℝ)
    rwa [one_pow, mul_one, mul_div_cancel₀ _ hf.ne'] at this
  have h3 := (ENNReal.tendsto_ofReal h2).limsup_eq
  rw [CompHt.growth, ← Filter.limsup_nat_add _ 1, ← h3]
  refine limsup_le_limsup ?_
  filter_upwards [eventually_gt_atTop 0] with m hm
  have hm' : (m : ℝ) ≠ 0 := by positivity
  have e : (D.factorial : ℝ) * ((h m : ℝ) / (m : ℝ) ^ D * ((m : ℝ) / ((m : ℝ) + 1)) ^ D) =
      (D.factorial : ℝ) * (h m : ℝ) / ((m + 1 : ℕ) : ℝ) ^ D := by
    push_cast
    rw [div_pow]
    field_simp
  rw [e, ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
    ENNReal.ofReal_natCast, ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast]
  exact ENNReal.div_le_div_right (mul_le_mul_right (by exact_mod_cast ENat.toENNReal_le.2 (hle m)) _) _

section Comp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c)

theorem cls_L₀_nsmul (u : AllWt.Weight Dw) (k : ℕ) :
    cls (L₀ X Z (k • u)) (isLB_L₀ X Z (k • u)) = k • cls (L₀ X Z u) (isLB_L₀ X Z u) := by
  induction k with
  | zero =>
    have e := cls_common_add (common₀ X Z) (0 : AllWt.Weight Dw) 0
    simp only [add_zero] at e
    rw [zero_smul]
    exact (left_eq_add.1 e).symm ▸ rfl
  | succ k ih =>
    have e := cls_common_add (common₀ X Z) (k • u) u
    rw [succ_nsmul, succ_nsmul, ← ih]
    exact e

end Comp

section Inj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c)
  {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

theorem mul_mem_vanBd (u : AllWt.Weight Dw) (k : ℕ) (h : u + k • u = (k + 1) • u)
    {θ : H0 (str₀ X Z) (L₀ X Z u) ⊤} (hθ : θ ∈ vanBd X Z u) (g : H0 (str₀ X Z) (L₀ X Z (k • u)) ⊤) :
    ((common₀ X Z).addChart h).mul θ g ∈ vanBd X Z ((k + 1) • u) := by
  intro y hy i hi
  obtain ⟨t, ha, hb, hc⟩ := ((common₀ X Z).addChart h).cover y
  rw [H0.germ_change i (((common₀ X Z).addChart h).c t) y (memTop y) hi hc,
    ((common₀ X Z).addChart h).germ_mul θ g t y (memTop y) ha hb hc]
  exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (hθ y hy _ ha))

theorem finrank_le_rank [IsIntegral (Y₀ X Z)] (u : AllWt.Weight Dw) (k : ℕ) (hC : CuspIso X Z U ((k + 1) • u))
    {θ : H0 (str₀ X Z) (L₀ X Z u) ⊤} (hθ : θ ∈ vanBd X Z u) (hθ0 : θ ≠ 0) :
    (Module.finrank c.F (H0 (str₀ X Z) (L₀ X Z (k • u)) ⊤) : ℕ∞) ≤
      Cardinal.toENat (Module.rank c.F (cuspOn U Z ((k + 1) • wtOf Dw u 0))) := by
  have h : u + k • u = (k + 1) • u := by rw [succ_nsmul, add_comm]
  let C := (common₀ X Z).addChart h
  let φ : H0 (str₀ X Z) (L₀ X Z (k • u)) ⊤ →ₗ[c.F] Cusp Z U ((k + 1) • u) :=
    ofSpace X Z U ((k + 1) • u) ∘ₗ Submodule.inclusion hC.2 ∘ₗ
      LinearMap.codRestrict _ (C.mul θ) (mul_mem_vanBd X Z u k h hθ)
  have hφ : Function.Injective φ := by
    refine (ofSpace_injective X Z U _).comp ((Submodule.inclusion_injective hC.2).comp fun g g' e => ?_)
    have e' : C.mul θ g = C.mul θ g' := congrArg Subtype.val e
    by_contra hne
    refine GlobalTheory.Vanishing.ProdNe.mul_ne_zero C θ (g - g') hθ0 (sub_ne_zero.2 hne) ?_
    rw [map_sub, e', sub_self]
  have e : cuspOn U Z ((k + 1) • wtOf Dw u 0) = Cusp Z U ((k + 1) • u) := by
    rw [CompHt.nsmul_wtOf, smul_zero]
  rw [e]
  have hr := LinearMap.rank_le_of_injective φ hφ
  by_cases hfin : FiniteDimensional c.F (H0 (str₀ X Z) (L₀ X Z (k • u)) ⊤)
  · rw [← Module.finrank_eq_rank] at hr
    exact (Cardinal.toENat_nat _).symm.le.trans (OrderHomClass.mono Cardinal.toENat hr)
  · rw [Module.finrank_of_not_finite hfin]
    exact bot_le

end Inj

theorem topSelf_le_growthOn : GlobalTheory.Published.NefNumerics → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l)
    (Y : Model Xo c (RingHom.id c.F)) (X : FlagCover Y) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)
    (u : AllWt.Weight Dw), IsVariety₀ X Z → 1 ≤ dimFlag Dw → (∀ la, CuspIso X Z U la) → (∃ f : Cusp Z U u, f ≠ 0) →
    letI := algebraΓOfHom (str₀ X Z); IsNef c.F (L₀ X Z u) →
    ENNReal.ofReal (topSelfIntersection c.F (L₀ X Z u) (dimFlag Dw) : ℝ) ≤ GlobalTheory.CompHt.growthOn U Z (wtOf Dw u 0) := by
  intro hN E _ _ _ H Dw l Xo c Y X Z r U u hV hD hC hf
  obtain ⟨f, hf⟩ := hf
  letI := algebraΓOfHom (str₀ X Z)
  intro hnef
  let S : LinSys c.F := ⟨Y₀ X Z, str₀ X Z, dimFlag Dw, L₀ X Z u, isLB_L₀ X Z u, 0, Fin.elim0⟩
  have hS : S.IsVariety := ⟨hV.1, hV.2.1, hV.2.2, hD⟩
  haveI : IsIntegral (Y₀ X Z) := hS.isIntegral
  have hp : IsProjOver (strHom c.F (Y₀ X Z)) := by
    rw [strHom_eq (f := str₀ X Z) fun _ => rfl]
    exact hV.2.1
  have hdim : topologicalKrullDim (Y₀ X Z) = dimFlag Dw := ImageDegree.topologicalKrullDim_eq S hS
  have ht := hN.2.2.tendsto hp hdim hnef
  have h0 := hN.2.2.topSelf_nonneg hp hdim hnef
  let θ := ((hC u).1.equiv f).1
  have hθ : θ ∈ vanBd X Z u := (hC u).1.space_le ((hC u).1.equiv f).2
  have hθ0 : θ ≠ 0 := fun e => hf ((hC u).1.equiv.map_eq_zero_iff.1 (Subtype.ext e))
  rw [CompHt.growthOn, dimFlag_eq]
  refine ofReal_le_growth (dimFlag Dw) (fun m => lbH0 c.F (lbPow (L₀ X Z u) m)) _ (Int.cast_nonneg h0) ht fun m => ?_
  rw [lineBundleGlobalSectionsDim_congr_picardClass (isLB_lbPow (isLB_L₀ X Z u) m) (isLB_L₀ X Z (m • u))
    (by rw [cls_lbPow (isLB_L₀ X Z u), cls_L₀_nsmul]), ← H0.finrank_top]
  exact finrank_le_rank X Z U u m (hC _) hθ hθ0

end GlobalTheory.NefCuspGrowth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricRatioFamilyEstimate
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField IsDedekindDomain
open GlobalTheory.FunObj.SqNum (nuH halfRank IsTor)

noncomputable section

namespace GlobalTheory.ThmAUpper

theorem thmA_upper : GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.ToricRatioConjugates → SetAt →
    (Closed FamHyp fun Fm _ => EvPt Fm fun x _ i _ => |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) → FieldDat → TorEx →
    (Lf (Fitted @Comparison₂) fun p _ d _ _ => ThA d.G p.P.A3.A.μ0 p.R.mu) := by
  intro hG hS hdl hF hT
  refine Lf.mono (Lf.and (GlobalTheory.T.fitted_ties_bound_eventual _ hS hdl hF) (GlobalTheory.T.fitted_ties_bound_eventual _ hS hdl hT)) ?_
  intro D L hT Gi Gl Kc Y cX ex Csz p CF d C CH hp hd
  refine ⟨hd, fun ⟨hf, ht⟩ w hw => ⟨GlobalTheory.T.norm_not_mem_prime_away_from_mu p CF d hp hd w hw, fun l hl hlw i j s Λ Λd z hs1 hs2 hΛ hΛd hz => ?_⟩⟩
  have hw' : D.plEq (D.plEq.symm w) = w := D.plEq.apply_symm_apply w
  have hl' : D.what₂.places.resChar (D.plEq.symm w) = l := resChar_eq _ hl (by rw [hw']; exact hlw)
  have key := GlobalTheory.T.cm_abelian_field_data_of_toric_ratio p CF d hp hd hG hf ht (D.plEq.symm w) (xiH_twisted p w hw).1 i j s Λ Λd z hs1 hs2
    (by rw [← nuH_twisted p d.G w hw]; exact hΛ) (by rw [hl']; exact hΛd) hz
  rw [hw', hl'] at key
  exact key

end GlobalTheory.ThmAUpper
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransporterMovesAllFramesOfDenseOpen
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem movesAt_of_dense : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)), ∀ (γ : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l) (k k' : (uAt r v i).Comp) (a : GL (Fin D.R.r) D.host.E) (hm : GlobalTheory.LevelCusp.IsMatch ((uAt r v i).X k) ((uAt r v i).X k') a) (O : Set (Frame ((uAt r v i).X k).Ψ D.R.r)), IsOpen O → O.Nonempty → O ⊆ ((uAt r v i).X k).dom → O ⊆ closure {x | ∃ hx : x ∈ ((uAt r v i).X k).dom, MovesAt p r i v γ k k' a hm x hx} → ∀ (x : Frame ((uAt r v i).X k).Ψ D.R.r) (hx : x ∈ ((uAt r v i).X k).dom), MovesAt p r i v γ k k' a hm x hx := by
  intro D L hT Gi Gl Kc Y cX ex Csz p hp r h hr i v γ k k' a hm O hO hOn hOd hOc x hx
  obtain ⟨o, ho⟩ := hOn
  obtain ⟨h1, k'', c, hc, hM⟩ := GlobalTheory.T.transporter_moves_nearby_frames_of_dense p hp r h hr i v γ k k' a hm o (hOd ho)
  obtain ⟨N, hN, hNM⟩ := h1 (Filter.mem_of_superset (hO.mem_nhds ho) hOc)
  exact GlobalTheory.T.transporter_movesAt_of_movesAt_open_set p hp r h hr i v γ k k' k'' a c hm hc (interior N ∩ O) (isOpen_interior.inter hO)
    ⟨o, mem_interior_iff_mem_nhds.2 hN, ho⟩ (fun w hw => hOd hw.2)
    (fun w hw hwW => ⟨hNM w hw (interior_subset hwW.1), hM w hw⟩) x hx (hM x hx)

end GlobalTheory.ShareOn

end
end

