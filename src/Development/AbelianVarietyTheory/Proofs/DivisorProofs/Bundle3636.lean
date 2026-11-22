import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3412
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3624
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3607
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3634
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3450
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3471
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3381
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3635
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0435
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0415
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0858
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3632
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2475
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2409
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3365
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3439
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3479
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2973
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3531
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructure
section
namespace GlobalTheory

theorem abelianDeRham : GlobalTheory.Published.AbelianDeRham :=
  GlobalTheory.abelianDeRham_of_hodge_dual_poincare GlobalTheory.T.abelianScheme_deRham_locallyFree_hodgeDegenerates GlobalTheory.T.dualAbelianScheme_exists_biduality
    (GlobalTheory.PoincareDeRhamDualityProof.poincareDeRhamDuality_of_hodge GlobalTheory.T.abelianScheme_deRham_locallyFree_hodgeDegenerates GlobalTheory.T.dualAbelianScheme_exists_biduality)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeHomLiftingNilpotentDividedPowers
section
namespace GlobalTheory

theorem abelianScheme_hom_lifting_nilpotent_dividedPowers : GlobalTheory.Published.AbelianLifting :=
  GlobalTheory.LiftFour.abelianLifting_of_four GlobalTheory.T.abelianScheme_deRham_locallyFree_hodgeDegenerates GlobalTheory.T.dualAbelianScheme_exists_biduality
    (GlobalTheory.PoincareDeRhamDualityProof.poincareDeRhamDuality_of_hodge GlobalTheory.T.abelianScheme_deRham_locallyFree_hodgeDegenerates GlobalTheory.T.dualAbelianScheme_exists_biduality)
    GlobalTheory.UnobTop.abelianUnobstructed

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyExistsDualPairStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianVariety_exists_dual_pair : ∀ (K : Type) [Field K] (A : AbVar K), ∃ (B : AbVar K) (P : LB (A.X ⊗ B.X).left), IsDualPair A B P ∧ B.dim = A.dim := by
  first | exact @GlobalTheory.AV.exists_dualPair | exact GlobalTheory.AV.exists_dualPair | (intros; apply GlobalTheory.AV.exists_dualPair <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithSelfIntersectionMonoOfIsNefStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithSelfIntersection_mono_of_isNef : GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (A B : HermLB p) (α β : ℝ), A.IsNef D → B.IsNef D → Le B A → A.IsSelfInter α → B.IsSelfInter β → β ≤ α := by
  first | exact @GlobalTheory.HSNefMono.selfInter_mono_of_isNef | exact GlobalTheory.HSNefMono.selfInter_mono_of_isNef | (intros; apply GlobalTheory.HSNefMono.selfInter_mono_of_isNef <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDlogAddCoboundaryAbLocus
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KS

noncomputable section

namespace GlobalTheory.CechH1Local

local macro "opens_le" : tactic =>
  `(tactic| (rw [SetLike.le_def]; intro y hy; simp only [TopologicalSpace.Opens.mem_inf] at hy ⊢; aesop))

theorem isCob_of_refine_le {Y : Scheme.{0}} {I K : Type} (Uc : I → Y.Opens) (c : C1 Uc) (hc : IsCoc Uc c)
    (V : K → Y.Opens) (σ : K → I) (hV : ∀ p, V p ≤ Uc (σ p)) (hVt : ∀ i, Uc i ≤ ⨆ p, V p)
    (B : ∀ p, Γ(Y, V p)) (hB : ∀ p p', rsT (c (σ p) (σ p')) (V p ⊓ V p') =
      rsT (B p') (V p ⊓ V p') - rsT (B p) (V p ⊓ V p')) : IsCob Uc c := by
  have hV' : ∀ p y, y ∈ V p → y ∈ Uc (σ p) := fun p y h => hV p h
  have cov : ∀ O : Y.Opens, O ≤ ⨆ p, V p → O ≤ ⨆ p, O ⊓ V p := by
    intro O hO x hx
    obtain ⟨p, hp⟩ := TopologicalSpace.Opens.mem_iSup.1 (hO hx)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨p, hx, hp⟩
  have glue : ∀ i, ∃ t : Γ(Y, Uc i), ∀ p, rsT t (Uc i ⊓ V p) =
      rsT (B p) (Uc i ⊓ V p) + rsT (c (σ p) i) (Uc i ⊓ V p) := by
    intro i
    refine exists_rsT_eq (fun p => Uc i ⊓ V p) (fun p => inf_le_left) (cov _ (hVt i)) _ fun p p' => ?_
    have h1 := congrArg (fun s => rsT s ((Uc i ⊓ V p) ⊓ (Uc i ⊓ V p'))) (hB p p')
    have h2 := congrArg (fun s => rsT s ((Uc i ⊓ V p) ⊓ (Uc i ⊓ V p'))) (hc (σ p) (σ p') i)
    simp only [rsT_add, rsT_sub] at h1 h2 ⊢
    simp (disch := opens_le) only [rsT_rsT] at h1 h2 ⊢
    linear_combination h1 - h2
  choose t ht using glue
  refine ⟨t, fun i j => ?_⟩
  refine eq_of_rsT_eq (fun p => Uc i ⊓ Uc j ⊓ V p) (fun p => inf_le_left)
    (cov _ (inf_le_left.trans (hVt i))) _ _ fun p => ?_
  have h1 := congrArg (fun s => rsT s (Uc i ⊓ Uc j ⊓ V p)) (ht i p)
  have h2 := congrArg (fun s => rsT s (Uc i ⊓ Uc j ⊓ V p)) (ht j p)
  have h3 := congrArg (fun s => rsT s (Uc i ⊓ Uc j ⊓ V p)) (hc (σ p) i j)
  simp only [rsT_add, rsT_sub] at h1 h2 h3 ⊢
  simp (disch := opens_le) only [rsT_rsT] at h1 h2 h3 ⊢
  linear_combination h1 - h2 + h3

theorem rsT_field {Z : Scheme.{0}} {d : ∀ W : Z.Opens, Γ(Z, W) → Γ(Z, W)} (hd : IsField ⊤ d) {O O' : Z.Opens}
    (h : O' ≤ O) (f : Γ(Z, O)) : rsT (d O f) O' = d O' (rsT f O') := by
  rw [rsT_of_le h, rsT_of_le h, hd.2.2 _ _ h le_top]

theorem rsT_appLE {Y X : Scheme.{0}} (π : Y ⟶ X) (V : X.Opens) {O O' : Y.Opens} (h : O ≤ π ⁻¹ᵁ V) (h' : O' ≤ O)
    (r : Γ(X, V)) : rsT ((π.appLE V O h).hom r) O' = (π.appLE V O' (h'.trans h)).hom r := by
  rw [rsT_of_le h']
  exact congrArg (fun φ => φ.hom r) (Scheme.Hom.appLE_map π h (homOfLE h').op)

theorem rsT_unit {Z : Scheme.{0}} {T O : Z.Opens} (h : O ≤ T) (u : Γ(Z, T)ˣ) :
    rsT u.val O * rsT u⁻¹.val O = 1 := by
  rw [← rsT_mul, Units.mul_inv, rsT_one h]

theorem isCoc_dlg {Z : Scheme.{0}} (L : LB Z) (hL : L.IsLB) {d : ∀ W : Z.Opens, Γ(Z, W) → Γ(Z, W)}
    (hd : IsField ⊤ d) {J : Type} (W : J → Z.Opens) (j : J → L.ι) (hj : ∀ i, W i ≤ L.U (j i)) :
    IsCoc W (fun i i' => d (W i ⊓ W i') (rsT (L.g (j i) (j i')).val (W i ⊓ W i')) *
      rsT (L.g (j i) (j i'))⁻¹.val (W i ⊓ W i')) := by
  intro i i' i''
  set O := W i ⊓ W i' ⊓ W i''
  have l₁ : O ≤ W i ⊓ W i' := inf_le_left
  have l₂ : O ≤ W i' ⊓ W i'' := le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have l₃ : O ≤ W i ⊓ W i'' := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have m₁ : W i ⊓ W i' ≤ L.U (j i) ⊓ L.U (j i') := inf_le_inf (hj i) (hj i')
  have m₂ : W i' ⊓ W i'' ≤ L.U (j i') ⊓ L.U (j i'') := inf_le_inf (hj i') (hj i'')
  have m₃ : W i ⊓ W i'' ≤ L.U (j i) ⊓ L.U (j i'') := inf_le_inf (hj i) (hj i'')
  have k : ∀ (a b : J) (l : O ≤ W a ⊓ W b) (m : W a ⊓ W b ≤ L.U (j a) ⊓ L.U (j b)),
      rsT (d (W a ⊓ W b) (rsT (L.g (j a) (j b)).val (W a ⊓ W b)) * rsT (L.g (j a) (j b))⁻¹.val (W a ⊓ W b)) O =
        d O (rsT (L.g (j a) (j b)).val O) * rsT (L.g (j a) (j b))⁻¹.val O := by
    intro a b l m
    rw [rsT_mul, rsT_field hd l, rsT_rsT m l, rsT_rsT m l]
  rw [k i i' l₁ m₁, k i' i'' l₂ m₂, k i i'' l₃ m₃]
  have T3 : O ≤ L.U (j i) ⊓ L.U (j i') ⊓ L.U (j i'') :=
    le_inf (le_inf (l₁.trans (m₁.trans inf_le_left)) (l₁.trans (m₁.trans inf_le_right)))
      (l₂.trans (m₂.trans inf_le_right))
  have co := congrArg (fun u => rsT (Units.val u) O) (hL.cocycle (j i) (j i') (j i''))
  simp only [Units.val_mul, rsT_mul] at co
  have e : ∀ {T T' : Z.Opens} (h : T' ≤ T) (u : Γ(Z, T)ˣ), (res h u).val = resG Z h u.val := fun _ _ => rfl
  have r : ∀ {T T' : Z.Opens} (h : T' ≤ T) (s : Γ(Z, T)), O ≤ T' → rsT (resG Z h s) O = rsT s O :=
    fun h s hO => by rw [← rsT_of_le h, rsT_rsT h hO]
  rw [e, e, e, r _ _ T3, r _ _ T3, r _ _ T3] at co
  set a := rsT (L.g (j i) (j i')).val O
  set b := rsT (L.g (j i') (j i'')).val O
  set a' := rsT (L.g (j i) (j i'))⁻¹.val O
  set b' := rsT (L.g (j i') (j i''))⁻¹.val O
  set e' := rsT (L.g (j i) (j i''))⁻¹.val O
  have ha : a * a' = 1 := rsT_unit (l₁.trans m₁) _
  have hb : b * b' = 1 := rsT_unit (l₂.trans m₂) _
  have he : rsT (L.g (j i) (j i'')).val O * e' = 1 := rsT_unit (l₃.trans m₃) _
  rw [← co] at he ⊢
  have hdm := hd.2.1 O le_top a b
  rw [hdm]
  linear_combination (-(d O a * a' + d O b * b')) * he + (d O a * b * e') * ha + (d O b * a * e') * hb

theorem exists_dlog_add_coboundary_abLocus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R), (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (c : R), c = ∏ i, tt i → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (dd' : Fin n → Fld t.G.left), (∀ a, IsInv t.G (v' a) (dd' a)) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι) (hW : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1), ⨆ i, W i = t.G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1 → (∀ i, W i ≤ t.PP.L.U (j i)) → ∀ z : C1 W, IsCoc W z → ∃ (cc : Fin n → Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)) (y : ∀ i, Γ(t.G.left, W i)), ∀ i i', z i i' = ∑ b, GlobalTheory.HeatV.cst t.G.hom (GlobalTheory.HeatV.bo R c).1 (inf_le_left.trans (hW i)) (cc b) * (dd' b (W i ⊓ W i') (rsT (t.PP.L.g (j i) (j i')).val (W i ⊓ W i')) * rsT (t.PP.L.g (j i) (j i'))⁻¹.val (W i ⊓ W i')) + (rsT (y i') (W i ⊓ W i') - rsT (y i) (W i ⊓ W i')) := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt htt hab c hc n v' dd' hdd J W j hW hWc hj z hz
  let K := {p : t.G.left.affineOpens × J // p.1.1 ≤ W p.2}
  let V : K → t.G.left.Opens := fun p => p.1.1.1
  let σ : K → J := fun p => p.1.2
  have hVσ : ∀ p, V p ≤ W (σ p) := fun p => p.2
  have hVt : ∀ i, W i ≤ ⨆ p, V p := by
    intro i x hx
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ := t.G.left.isBasis_affineOpens.exists_subset_of_mem_open hx (W i).isOpen
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨(⟨U, hU⟩, i), hUW⟩, hxU⟩
  have cover : ⨆ p, V p = t.G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1 := by
    refine le_antisymm (iSup_le fun p => (hVσ p).trans (hW _)) ?_
    rw [← hWc]
    exact iSup_le hVt
  let z' : C1 V := fun p p' => rsT (z (σ p) (σ p')) (V p ⊓ V p')
  have hz' : IsCoc V z' := by
    intro p p' p''
    have h := congrArg (fun s => rsT s (V p ⊓ V p' ⊓ V p'')) (hz (σ p) (σ p') (σ p''))
    simp only [rsT_add] at h
    have l₁ : V p ⊓ V p' ⊓ V p'' ≤ W (σ p) ⊓ W (σ p') ⊓ W (σ p'') :=
      inf_le_inf (inf_le_inf (hVσ p) (hVσ p')) (hVσ p'')
    simp only [z']
    rw [rsT_rsT (inf_le_inf (hVσ p) (hVσ p')) inf_le_left, rsT_rsT (inf_le_inf (hVσ p') (hVσ p''))
      (le_inf (inf_le_left.trans inf_le_right) inf_le_right),
      rsT_rsT (inf_le_inf (hVσ p) (hVσ p'')) (le_inf (inf_le_left.trans inf_le_left) inf_le_right)]
    rwa [rsT_rsT inf_le_left l₁, rsT_rsT (le_inf (inf_le_left.trans inf_le_right) inf_le_right) l₁,
      rsT_rsT (le_inf (inf_le_left.trans inf_le_left) inf_le_right) l₁] at h
  obtain ⟨cc, y', hy'⟩ := GlobalTheory.T.basis_tangent_module_localized_abelian_locus E H R t P m tt htt hab c hc n v' dd' hdd K V (fun p => j (σ p))
    (fun p => (hVσ p).trans (hW _)) cover (fun p => (hVσ p).trans (hj _)) (fun p => p.1.1.2) z' hz'
  let dl : Fin n → C1 W := fun b i i' => dd' b (W i ⊓ W i') (rsT (t.PP.L.g (j i) (j i')).val (W i ⊓ W i')) *
    rsT (t.PP.L.g (j i) (j i'))⁻¹.val (W i ⊓ W i')
  have hdl : ∀ b, IsCoc W (dl b) := fun b => isCoc_dlg t.PP.L t.PP.isLB (hdd b).1 W j hj
  let c0 : C1 W := fun i i' => z i i' - ∑ b, GlobalTheory.HeatV.cst t.G.hom (GlobalTheory.HeatV.bo R c).1
    (inf_le_left.trans (hW i)) (cc b) * dl b i i'
  let Cf : ∀ O : t.G.left.Opens, O ≤ t.G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1 → Fin n → Γ(t.G.left, O) :=
    fun O h b => (t.G.hom.appLE _ O h).hom (cc b)
  have key : ∀ (a a' : J) {O : t.G.left.Opens} (l : O ≤ W a ⊓ W a'),
      rsT (c0 a a') O = rsT (z a a') O - ∑ b, Cf O (l.trans (inf_le_left.trans (hW a))) b * rsT (dl b a a') O := by
    intro a a' O l
    simp only [c0]
    rw [rsT_sub, rsT_sum]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [rsT_mul, rsT_appLE _ _ _ l]
  have hc0 : IsCoc W c0 := by
    intro i i' i''
    have l₁ : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i' := inf_le_left
    have l₂ : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'' := le_inf (inf_le_left.trans inf_le_right) inf_le_right
    have l₃ : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'' := le_inf (inf_le_left.trans inf_le_left) inf_le_right
    have h0 := hz i i' i''
    rw [key i i' l₁, key i' i'' l₂, key i i'' l₃]
    have hs : ∑ b, Cf _ (l₁.trans (inf_le_left.trans (hW i))) b * rsT (dl b i i') (W i ⊓ W i' ⊓ W i'') +
        ∑ b, Cf _ (l₁.trans (inf_le_left.trans (hW i))) b * rsT (dl b i' i'') (W i ⊓ W i' ⊓ W i'') =
        ∑ b, Cf _ (l₁.trans (inf_le_left.trans (hW i))) b * rsT (dl b i i'') (W i ⊓ W i' ⊓ W i'') := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← mul_add, hdl b i i' i'']
    linear_combination h0 - hs
  have hB : ∀ p p', rsT (c0 (σ p) (σ p')) (V p ⊓ V p') = rsT (y' p') (V p ⊓ V p') - rsT (y' p) (V p ⊓ V p') := by
    intro p p'
    have l : V p ⊓ V p' ≤ W (σ p) ⊓ W (σ p') := inf_le_inf (hVσ p) (hVσ p')
    rw [key _ _ l, show rsT (z (σ p) (σ p')) (V p ⊓ V p') = z' p p' from rfl, hy' p p']
    have hs : ∀ b, rsT (dl b (σ p) (σ p')) (V p ⊓ V p') =
        dd' b (V p ⊓ V p') (rsT (t.PP.L.g (j (σ p)) (j (σ p'))).val (V p ⊓ V p')) *
          rsT (t.PP.L.g (j (σ p)) (j (σ p')))⁻¹.val (V p ⊓ V p') := fun b => by
      simp only [dl]
      rw [rsT_mul, rsT_field (hdd b).1 l, rsT_rsT (inf_le_inf (hj _) (hj _)) l, rsT_rsT (inf_le_inf (hj _) (hj _)) l]
    simp only [hs]
    ring
  obtain ⟨y, hy⟩ := isCob_of_refine_le W c0 hc0 V σ hVσ hVt y' hB
  refine ⟨cc, y, fun i i' => ?_⟩
  have := hy i i'
  simp only [c0] at this
  linear_combination this

end GlobalTheory.CechH1Local
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualAbelianScheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.ZM GlobalTheory.SiegelTor

open scoped CategoryTheory.Obj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dual_abelian_scheme : ∀ (Y : Scheme.{0}) (A G : Over Y) [GrpObj A] [IsCommMonObj A] [GrpObj G] [IsCommMonObj G] (χ : A ⟶ G) (P'' : LB (G2 G).left), IsAbelianScheme A → IsAbelianScheme G → IsMonHom χ → P''.IsLB → (∃ t : (P''.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) → (∃ t : (P''.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) → ∃ (D : Over Y) (_ : GrpObj D) (Q : LB (A ⊗ D).left) (h : A ⟶ D), IsAbelianScheme D ∧ GlobalTheory.AbDual.IsDual A D Q ∧ GlobalTheory.AbDual.IsAdditive (GlobalTheory.AbDual.swap Q) ∧ IsMonHom h ∧ LBIso (P''.pull (χ ⊗ₘ χ).left) (Q.pull (lift (fst A A) (snd A A ≫ h)).left) := by
  first | (exact @GlobalTheory.DualHomPull.exists_dual_hom) | (exact GlobalTheory.DualHomPull.exists_dual_hom) | (intros; apply GlobalTheory.DualHomPull.exists_dual_hom  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFanOrderIdealThetaCompactification
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem idealSt_holds : IdealSt := by
  intro g hg n hn hodd F Z z i hθ φ hφ
  obtain ⟨ι, _, W, hclo, hirr, hpart⟩ := GlobalTheory.T.exists_clopen_irreducible_partition_of_normal_proj n Z z hθ.1 hθ.2.1
  have key : ∀ c, ∃ (d : ℕ) (J : Z.IdealSheafData), 1 ≤ d ∧ (∀ x ∈ J.support, x ∈ W c ∧ x ∉ Set.range i) ∧
      ∀ (T : Trait F) (ξ : Sp T.V ⟶ Z), jK T.V ≫ ξ = T.y ≫ i → ξ (closedPoint T.V) ∈ W c →
        ∃ a : ℕ, (a : ℝ) = d * φ.evalZ T.β ∧ idlAlong J ξ = Ideal.span {T.ϖ ^ a} := by
    intro c
    obtain ⟨W8, X₁, ι₁, J₁, h1, h2, h4, h5⟩ :=
      GlobalTheory.T.exists_thetaSetup_ideal_over_clopen_component g n hg hn hodd F Z z i hθ φ hφ (W c) (hclo c) (hirr c)
    exact GlobalTheory.T.idealDescent_thetaModel_to_component_traitOrders g n hg hn hodd F Z z i hθ φ hφ (W c) (hclo c) (hirr c) W8 X₁ ι₁ J₁ h1 h2 h4 h5
  choose d J hd hJ hv using key
  exact GlobalTheory.T.exists_fanOrder_ideal_glued_clopen_pieces F i φ W J d hclo hpart hd hJ hv

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinExtCubicalSymmetricEvenFactor
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_finExt_cp_factor_even : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (_ : F.Alg) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∃ (R₀ : Type) (_ : CommRing R₀) (_ : IsDomain R₀) (_ : IsLocalRing R₀) (ρ₀ : R →+* R₀) (G₀ : Over (Sp R₀)) (_ : GrpObj G₀) (_ : IsCommMonObj G₀) (β₀ : G₀.left ⟶ G.left) (β₀₂ : (G2 G₀).left ⟶ (G2 G).left) (P : GlobalTheory.UU.CP G₀) (A₀ : PolAV (Sp (FractionRing R₀))) (gen₀ : (Over.pullback (jK R₀)).obj G₀ ≅ A₀.A), FinExt ρ₀ ∧ IsGrpPullback G₀ G (spMap ρ₀) β₀ ∧ Geo.Tor.IsSquare β₀ β₀₂ ∧ IsSemiAbelian G₀ ∧ LBIso (abelian₂ G₀ P.L.L) ((abelian₂ G' U'.LG.L).pull (β₀₂ ≫ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left)) ∧ EvenOn P ∧ IsMonHom gen₀.hom ∧ LBIso (A₀.L.pull gen₀.hom.left) (P.L.L.pull (pullback.fst G₀.hom (jK R₀))) := by
  intro R _ _ _ hR D D' F hA A' G' _ _ hG' U' oA oG hlin G _ _ hG inc pr hinc hpr hip hpi
  obtain ⟨R₁, _, _, _, ρ₁, G₁, _, _, β₁, β₁₂, A₁, gen₁, h1, h2, h3, h4, h5⟩ :=
    GlobalTheory.T.factorPairing_mumfordBundle_principal_polarisation R hR D D' F hA A' G' hG' U' oA oG hlin G hG inc pr hinc hpr hip hpi
  exact GlobalTheory.T.exists_evenCubicalStructure_of_idempotentFactor_biextension R hR D D' F A' G' hG' U' oA oG hlin G hG inc pr hinc hpr hip hpi R₁ ρ₁ G₁ β₁ β₁₂ A₁ gen₁
    h1 h2 h3 h4 h5

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteKernelNearDiagonalAmple
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.KernelNear

open GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.AbLaw

variable {S : Scheme.{0}} {G : Over S} [GrpObj G]

theorem evc_symm {P : LB (G ⊗ G).left} (hP : P.IsLB) (hs : LBIso P (P.pull (lift (snd G G) (fst G G)).left))
    {Y : Over S} (a b : Y ⟶ G) : evc hP a b = evc hP b a := by
  have e := congrArg (CechPic.pull (lift b a).left) ((cls_eq_iff hP (pull_isLB hP _)).2 hs)
  rw [cls_pull hP _ (pull_isLB hP _), ← pull_comp, ← Over.comp_left, comp_lift, lift_fst, lift_snd] at e
  exact e.symm

theorem evc_eq_zero_of_triv {P : LB (G ⊗ G).left} (hP : P.IsLB) {T : Over S} {x : T ⟶ G}
    (hx : Triv (P.pull (lift (snd G T ≫ x) (fst G T)).left)) {Y : Over S} (t : Y ⟶ T) (w : Y ⟶ G) :
    evc hP (t ≫ x) w = 0 := by
  have e := congrArg (CechPic.pull (lift w t).left) ((triv_ev_iff hP _ _).1 hx)
  rwa [pull_evc, map_zero, lift_snd_assoc, lift_fst] at e

theorem memKL_of_triv {P : LB (G ⊗ G).left} (hP : P.IsLB) (hs : LBIso P (P.pull (lift (snd G G) (fst G G)).left))
    (a₁ : IsAdditive P) (a₂ : IsAdditive (AbDual.swap P)) {T : Over S} {x : T ⟶ G}
    (hx : Triv (P.pull (lift (snd G T ≫ x) (fst G T)).left)) :
    MemKL G (P.pull (lift (𝟙 G) (𝟙 G)).left) x := by
  have hL : (P.pull (lift (𝟙 G) (𝟙 G)).left).IsLB := pull_isLB hP _
  have hD : (Out.translDiff G (P.pull (lift (𝟙 G) (𝟙 G)).left) x).IsLB := LB.isLB_linComb hL _ _
  have hdiag : ∀ {Y : Over S} (y : Y ⟶ G), CechPic.pull y.left (cls _ hL) = evc hP y y := fun y => by
    rw [cls_pull hP _ hL, ← pull_comp, ← Over.comp_left, comp_lift, Category.comp_id]
    rfl
  have z : cls _ hD = 0 := by
    have e₁ := pull_translDiff hL x hD (fst T G) (snd T G)
    rw [lift_fst_snd, Over.id_left, pull_id, hdiag, hdiag] at e₁
    rw [e₁, (isAdditive_iff hP).1 a₁, (GlobalTheory.BirigidLift.isAdditive_swap_iff hP).1 a₂,
      (GlobalTheory.BirigidLift.isAdditive_swap_iff hP).1 a₂, evc_eq_zero_of_triv hP hx, evc_eq_zero_of_triv hP hx,
      evc_symm hP hs (snd T G) (fst T G ≫ x), evc_eq_zero_of_triv hP hx]
    simp
  intro p
  refine ⟨⊤, trivial, (cls_eq_zero_iff (pull_isLB hD _)).1 ?_⟩
  rw [cls_pull hD, z, map_zero]

end GlobalTheory.KernelNear

namespace GlobalTheory.KernelNear

open GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.AbLaw

theorem exists_finite_kernel_near : ∀ (S' : Scheme.{0}) [IsLocallyNoetherian S'] (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsAbelianScheme G → P.IsLB → (∃ s : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, s.IsGen) → (∃ s : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, s.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → ∀ W : S'.Opens, (∀ V : S'.Opens, V ≤ W → Out.RelAmple ((Over.pullback V.ι).obj G) ((P.pull (Pdiv.PullbackComparison.pφ₂ V.ι G)).pull (lift (𝟙 ((Over.pullback V.ι).obj G)) (𝟙 ((Over.pullback V.ι).obj G))).left)) → ∀ s ∈ W, ∃ (V₀ : S'.Opens) (Z : Over S') (i : Z ⟶ G), s ∈ V₀ ∧ Mono i ∧ IsFinite (Z.hom ∣_ V₀) ∧ (∀ T : Over S', Set.range T.hom.base ⊆ (V₀ : Set S') → ∃ z : T ⟶ Z, z ≫ i = 1) ∧ (∀ (T : Over S') (a b : T ⟶ Z), Set.range T.hom.base ⊆ (V₀ : Set S') → ∃ c : T ⟶ Z, c ≫ i = (a ≫ i) * (b ≫ i)) ∧ (∀ (T : Over S') (a : T ⟶ Z), Set.range T.hom.base ⊆ (V₀ : Set S') → ∃ c : T ⟶ Z, c ≫ i = (a ≫ i)⁻¹) ∧ (∀ (T : Over S') (x : T ⟶ G), Set.range T.hom.base ⊆ (V₀ : Set S') → (∃ c : (P.pull (lift (snd G T ≫ x) (fst G T)).left).Gen, c.IsGen) → ∃ z : T ⟶ Z, z ≫ i = x) ∧ (∀ (T : Over S') (z : T ⟶ Z), Set.range T.hom.base ⊆ (V₀ : Set S') → ∀ p : T.left, ∃ U : T.left.Opens, p ∈ U ∧ ∃ c : (P.pull (lift (snd G (Over.mk (U.ι ≫ T.hom)) ≫ (Over.homMk U.ι : Over.mk (U.ι ≫ T.hom) ⟶ T) ≫ z ≫ i) (fst G (Over.mk (U.ι ≫ T.hom)))).left).Gen, c.IsGen) := by
  intro S' _ G _ _ P hG hP h₁ h₂ hs W hW s hsW
  obtain ⟨V₀, hV₀, hsV, hVW⟩ := exists_isAffineOpen_mem_and_subset (X := S') (U := W) hsW
  obtain ⟨D, _, Q, h, hDab, q, -, hh, e⟩ :=
    GlobalTheory.DualHomPull.exists_dual_hom S' G G (𝟙 G) P hG hG inferInstance hP h₁ h₂
  obtain ⟨a₁, a₂⟩ := GlobalTheory.CubeAxes.additive_of_triv_axes hG hP h₁ h₂
  have hD : ∀ {Y : Over S'} (a b : Y ⟶ G), evc hP a b = evc q.isLB a (b ≫ h) := fun a b => by
    have e' := (cls_eq_iff (pull_isLB hP _) (pull_isLB q.isLB _)).2 e
    rw [MonoidalCategory.id_tensorHom_id, Over.id_left, cls_pull hP _ (pull_isLB hP _), pull_id,
      cls_pull q.isLB _ (pull_isLB q.isLB _)] at e'
    rw [evc, e', ← pull_comp, ← Over.comp_left, comp_lift, lift_fst, ← Category.assoc, lift_snd]
    rfl
  have K : ∀ {T : Over S'} (x : T ⟶ G), Triv (P.pull (lift (snd G T ≫ x) (fst G T)).left) ↔ x ≫ h = 1 := by
    intro T x
    rw [triv_ev_iff hP, evc_symm hP hs, hD, Category.assoc]
    refine ⟨fun hx => q.eq_one _ ((triv_ev_iff q.isLB _ _).2 hx), fun hx => ?_⟩
    rw [hx, MonObj.comp_one]
    exact evc_one_right q.isLB q.zero _
  have : Mono (η[D]) := ⟨fun _ _ _ => toUnit_unique _ _⟩
  have kerh : ∀ {T : Over S'} (z : T ⟶ pullback h (η[D])), (z ≫ pullback.fst h (η[D])) ≫ h = 1 := fun z => by
    rw [Category.assoc, pullback.condition, ← Category.assoc, toUnit_unique (z ≫ pullback.snd _ _) (toUnit _)]
    rfl
  have fac : ∀ {T : Over S'} (x : T ⟶ G), x ≫ h = 1 → ∃ z : T ⟶ pullback h (η[D]), z ≫ pullback.fst h (η[D]) = x :=
    fun x hx => ⟨pullback.lift x (toUnit _) (by rw [hx]; rfl), pullback.lift_fst _ _ _⟩
  have hcl : IsClosedImmersion (pullback.fst h (η[D])).left := by
    have hpb := (IsPullback.of_hasPullback h (η[D])).map (Over.forget S')
    have := hDab.proper
    have : IsClosedImmersion ((η[D]).left ≫ D.hom) := by
      rw [Over.w (η[D])]
      exact (inferInstance : IsClosedImmersion (𝟙 S'))
    have : IsClosedImmersion (η[D]).left := IsClosedImmersion.of_comp _ D.hom
    exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) hpb.flip this
  refine ⟨V₀, pullback h (η[D]), pullback.fst h (η[D]), hsV, inferInstance,
    GlobalTheory.T.relatively_ample_closed_immersion S' G P hG hP V₀ hV₀ (hW V₀ fun _ hx => hVW hx) _ _ hcl
      (fun T z _ => memKL_of_triv hP hs a₁ a₂ ((K _).2 (kerh z))), ?_, ?_, ?_, ?_, ?_⟩
  · intro T _
    exact fac 1 (MonObj.one_comp h)
  · intro T a b _
    refine fac _ ?_
    rw [MonObj.mul_comp, kerh, kerh, _root_.mul_one]
  · intro T a _
    refine fac _ ?_
    rw [GrpObj.inv_comp, kerh, inv_one]
  · intro T x _ hx
    exact fac x ((K x).1 hx)
  · intro T z _ p
    refine ⟨⊤, trivial, (K _).2 ?_⟩
    rw [Category.assoc, Category.assoc, ← Category.assoc z, kerh, MonObj.comp_one]

end GlobalTheory.KernelNear
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFourierTermSystemTraitsChartThetaModelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fourierTermSystem_traits_chart_thetaModel : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ Q.X), Module.finrank ℤ Q.X ≤ g → (∀ k, t k ∈ maximalIdeal V ∧ t k ≠ 0) → (∀ k a b, δ k a b = δ k b a) → (∀ k a, 0 ≤ δ k a a) → (∀ a, a ≠ 0 → ∃ k, 0 < δ k a a) → Q.IsMonomialTau t δ → ∀ ξ : Sp V ⟶ Z, UnifOver F i ξ Q → ∀ l : ℕ, l.Prime → l ∣ n → ∀ j₀ : ℕ, ∃ (j : ℕ) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (_ : IsDomain (X₁.M.Z.presheaf.stalk z₁)) (Φ : VPre (id : ℤ → ℤ) g W (X₁.M.Z.presheaf.stalk z₁)) (y : Φ.Y) (ρ : V →+* Φ.V y) (e : Φ.X y ≃+ Q.X) (h : Fin (Φ.m y) ≃ Fin m) (c₀ : Φ.Q), j₀ ≤ j ∧ HasTraitsR X₁ z₁ Φ ∧ IsChartMemberP X₁ z₁ Φ ((l ^ j) ^ 2) Q ξ t δ y ρ e h ∧ (∀ y', IsUnit (Φ.u y' 0 c₀)) ∧ (∀ y', Φ.m y' ≠ 1 → y' = y) ∧ Φ.Exact ((l ^ j) ^ 2) ∧ Φ.ClassSums ((l ^ j) ^ 2) := by
  first | exact @GlobalTheory.Poinc.Sep.exists_vPre_traits_chart | exact GlobalTheory.Poinc.Sep.exists_vPre_traits_chart | (intros; apply GlobalTheory.Poinc.Sep.exists_vPre_traits_chart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLowerBaseOfTraitAbelianPartStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lower_base_of_trait_abelian_part : ∀ (n : ℕ), 3 ≤ n → Odd n → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → IsDiscreteValuationRing V → ∀ (b : cycAway n →+* V) (PB : PolAV (Sp V)) (r : ℕ) (c : (Fin r → ℤ) → (𝟙_ (Over (Sp V)) ⟶ PB.A)), (∀ a a', c (a + a') = c a * c a') → ∃ (L : LowBase (zetaAway n) n) (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (f : V →+* V') (κ : L.W →+* V') (e : (Fin L.T.r → ℤ) ≃+ (Fin r → ℤ)), L.h = PB.g ∧ IsCN V' ∧ IsDiscreteValuationRing V' ∧ Function.Injective f ∧ f.Finite ∧ IsLocalHom f ∧ IsLocalHom κ ∧ κ.comp L.T.b = f.comp b ∧ ∃ (B' : Over (Sp V')) (_ : GrpObj B') (β' : B'.left ⟶ PB.A.left) (β'' : B'.left ⟶ L.T.B.left) (β₂ : (G2 B').left ⟶ (G2 PB.A).left) (β₂' : (G2 B').left ⟶ (G2 L.T.B).left), IsGrpPullback B' PB.A (spMap f) β' ∧ IsGrpPullback B' L.T.B (spMap κ) β'' ∧ IsSquare β' β₂ ∧ IsSquare β'' β₂' ∧ LBIso ((abelian₂ PB.A PB.L).pull β₂) ((abelian₂ L.T.B L.T.M.L).pull β₂') ∧ ∀ a : Fin L.T.r → ℤ, ∃ x : Sp V' ⟶ B'.left, x ≫ B'.hom = 𝟙 _ ∧ x ≫ β' = spMap f ≫ (c (e a)).left ∧ x ≫ β'' = spMap κ ≫ (L.T.c₀ ((n : ℤ) • a)).left := by
  first | exact @GlobalTheory.TChart.exists_lowBase_of_trait | exact GlobalTheory.TChart.exists_lowBase_of_trait | (intros; apply GlobalTheory.TChart.exists_lowBase_of_trait <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymmetricKodairaSpencerAbelianLocusStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symmetric_kodairaSpencer_abelianLocus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (DV : Derivation ℤ Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1) Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1)), ∃ Θ₁ : Matrix (Fin n) (Fin n) Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1), Θ₁ᵀ = Θ₁ ∧ IsKS t ((Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) (fun a => spMap (dualMap (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)) ≫ (tv (v' a)).left) ⇑DV Θ₁ := by
  first | exact @GlobalTheory.KSAbLocusSymm.exists_symm_isKS_abLocus | exact GlobalTheory.KSAbLocusSymm.exists_symm_isKS_abLocus | (intros; apply GlobalTheory.KSAbLocusSymm.exists_symm_isKS_abLocus <;> assumption)
end

