import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1622
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsClosedImmersionIffPullRatio
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1613
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1637
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1632
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0894
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0876
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0826
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1631
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0036
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1630
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1643
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0586
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1633
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1634
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1635

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratingSectionsProjectiveMap
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LineQuot
open GlobalTheory.LB (resG_resG resG_self fun_ext_of_cover exists_fun_of_cover)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM sec_ext_of_cover exists_sec_of_cover)

namespace GlobalTheory.LineQuot.ExMap

variable {T : Scheme.{0}} {L Q : T.Modules}

def HBij (a : L ⟶ Q) (W : T.Opens) : Prop := ∀ V : T.Opens, V ≤ W → Function.Bijective (a.app V)

theorem HBij.mono {a : L ⟶ Q} {W W' : T.Opens} (h : HBij a W) (hW : W' ≤ W) : HBij a W' :=
  fun V hV => h V (hV.trans hW)

theorem hbij_iSup (a : L ⟶ Q) {κ : Type} (W : κ → T.Opens) (h : ∀ k, HBij a (W k)) :
    HBij a (⨆ k, W k) := by
  intro V hV
  have hc : V ≤ ⨆ k, V ⊓ W k := by rw [← inf_iSup_eq]; exact le_inf le_rfl hV
  constructor
  · intro s t e
    refine sec_ext_of_cover (fun k => V ⊓ W k) (fun _ => inf_le_left) hc fun k =>
      (h k _ inf_le_right).1 ?_
    rw [app_resM, app_resM, e]
  · intro t
    choose s hs using fun k => (h k _ (inf_le_right : V ⊓ W k ≤ W k)).2
      (resM Q (inf_le_left : V ⊓ W k ≤ V) t)
    obtain ⟨r, hr⟩ := exists_sec_of_cover (fun k => V ⊓ W k) (fun _ => inf_le_left) hc s fun k l =>
        (h k _ (inf_le_left.trans inf_le_right)).1 (by
          rw [app_resM, app_resM, hs, hs, resM_resM, resM_resM])
    refine ⟨r, sec_ext_of_cover (fun k => V ⊓ W k) (fun _ => inf_le_left) hc fun k => ?_⟩
    rw [← app_resM, hr, hs]

def good (a : L ⟶ Q) : T.Opens := ⨆ W : {W : T.Opens // HBij a W}, W.1

theorem hbij_good (a : L ⟶ Q) : HBij a (good a) := hbij_iSup a _ fun W => W.2

theorem le_good {a : L ⟶ Q} {W : T.Opens} (h : HBij a W) : W ≤ good a :=
  le_iSup (fun W : {W : T.Opens // HBij a W} => W.1) ⟨W, h⟩

def IsRatio (a b : L ⟶ Q) (V : T.Opens) (c : Γ(T, V)) : Prop :=
  ∀ (V' : T.Opens) (h : V' ≤ V) (t : Γ(L, V')), b.app V' t = resG T h c • a.app V' t

theorem IsRatio.res {a b : L ⟶ Q} {V : T.Opens} {c : Γ(T, V)} (hc : IsRatio a b V c) {W : T.Opens}
    (h : W ≤ V) : IsRatio a b W (resG T h c) := fun V' h' t => by
  rw [resG_resG]; exact hc V' _ t

theorem smul_ext (hL : IsVB L 1) {V : T.Opens} {c c' : Γ(T, V)}
    (h : ∀ (V' : T.Opens) (h' : V' ≤ V) (t : Γ(L, V')), resG T h' c • t = resG T h' c' • t) :
    c = c' := by
  choose O e _ hx hO he using fun x : V => hL.exists_affine (V := V) x.2
  refine fun_ext_of_cover O hO (fun x hx' => Opens.mem_iSup.2 ⟨⟨x, hx'⟩, hx _⟩) fun x => ?_
  have := (he x (O x) le_rfl).1 (a₁ := fun _ => resG T (hO x) c) (a₂ := fun _ => resG T (hO x) c') (by
    simp only [Fintype.linearCombination_apply, Fin.sum_univ_one]
    exact h _ _ _)
  exact congrFun this 0

theorem isRatio_unique (hL : IsVB L 1) {a b : L ⟶ Q} {V : T.Opens} (hV : HBij a V) {c c' : Γ(T, V)}
    (hc : IsRatio a b V c) (hc' : IsRatio a b V c') : c = c' :=
  smul_ext hL fun V' h t => (hV V' h).1 (by
    rw [Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul, ← hc V' h t, ← hc' V' h t])

theorem exists_isRatio (hL : IsVB L 1) {a : L ⟶ Q} (b : L ⟶ Q) {U : T.Opens} (hU : HBij a U) :
    ∃ c : Γ(T, U), IsRatio a b U c := by
  have loc : ∀ x : U, ∃ (O : T.Opens) (_ : (x : T) ∈ O) (hO : O ≤ U) (c : Γ(T, O)), IsRatio a b O c := by
    intro x
    obtain ⟨O, e, -, hx, hO, he⟩ := hL.exists_affine (V := U) x.2
    obtain ⟨u, hu⟩ := (hU O hO).2 (b.app O (e 0))
    obtain ⟨d, hd⟩ := (he O le_rfl).2 u
    simp only [Fintype.linearCombination_apply, Fin.sum_univ_one, resM_self] at hd
    refine ⟨O, hx, hO, d 0, fun V' h t => ?_⟩
    obtain ⟨g, hg⟩ := (he V' h).2 t
    simp only [Fintype.linearCombination_apply, Fin.sum_univ_one] at hg
    subst hg
    rw [Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul, app_resM, app_resM, ← hu, ← hd,
      Scheme.Modules.Hom.app_smul, resM_smul, smul_comm]
  choose O hx hO c hc using loc
  have hcov : U ≤ ⨆ x, O x := fun x hx' => Opens.mem_iSup.2 ⟨⟨x, hx'⟩, hx _⟩
  obtain ⟨r, hr⟩ := exists_fun_of_cover O hO hcov c fun x y =>
    isRatio_unique hL (hU.mono (inf_le_left.trans (hO x))) ((hc x).res _) ((hc y).res _)
  refine ⟨r, fun V' h t => ?_⟩
  have hc' : V' ≤ ⨆ x, V' ⊓ O x := by rw [← inf_iSup_eq]; exact le_inf le_rfl (h.trans hcov)
  refine sec_ext_of_cover (fun x => V' ⊓ O x) (fun _ => inf_le_left) hc' fun x => ?_
  rw [← app_resM, resM_smul, ← app_resM, resG_resG,
    hc x _ (inf_le_right : V' ⊓ O x ≤ O x), ← hr x, resG_resG]

end GlobalTheory.LineQuot.ExMap

namespace GlobalTheory.LineQuot.ExMap

variable {T : Scheme.{0}} {L Q : T.Modules}

theorem isUnit_resG_basicOpen {V : T.Opens} (c : Γ(T, V)) {W : T.Opens} (h : W ≤ T.basicOpen c) :
    IsUnit (resG T (h.trans (T.basicOpen_le c)) c) := by
  have := (T.toRingedSpace.isUnit_res_basicOpen c).map (resG T h)
  exact (congrArg IsUnit (resG_resG (T.basicOpen_le c) h c)).mp this

variable {N : ℕ} (hL : IsVB L 1) (s : Fin (N + 1) → (L ⟶ Q))

def ratio (i j : Fin (N + 1)) : Γ(T, good (s i)) := (exists_isRatio hL (s j) (hbij_good (s i))).choose

theorem isRatio_ratio (i j : Fin (N + 1)) : IsRatio (s i) (s j) (good (s i)) (ratio hL s i j) :=
  (exists_isRatio hL (s j) (hbij_good (s i))).choose_spec

theorem isCoordFamily (hs : Gen s) : ProjSpace.IsCoordFamily (fun i => good (s i)) (ratio hL s) where
  cover := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨j, W, hx, hW⟩ := hs x
    exact Opens.mem_iSup.2 ⟨j, le_good hW hx⟩
  self i := isRatio_unique hL (hbij_good (s i)) (isRatio_ratio hL s i i)
    fun V' h t => by rw [map_one, one_smul]
  mul i j k := by
    refine isRatio_unique hL ((hbij_good (s i)).mono inf_le_left) ?_ ((isRatio_ratio hL s i k).res _)
    intro V' h t
    rw [(isRatio_ratio hL s j k) V' (h.trans inf_le_right) t,
      (isRatio_ratio hL s i j) V' (h.trans inf_le_left) t, smul_smul, map_mul, resG_resG, resG_resG,
      mul_comm]
  basicOpen_le i j := by
    refine le_good fun V hV => ?_
    have hV' : V ≤ good (s i) := hV.trans (T.basicOpen_le _)
    have e : ⇑((s j).app V) = (fun y => resG T hV' (ratio hL s i j) • y) ∘ ⇑((s i).app V) :=
      funext fun t => isRatio_ratio hL s i j V hV' t
    rw [e]
    exact (isUnit_resG_basicOpen _ hV).smul_bijective.comp (hbij_good (s i) V hV')

end GlobalTheory.LineQuot.ExMap

open GlobalTheory.LineQuot.ExMap in

theorem GlobalTheory.LineQuot.exists_toPSpace : ∀ (k : Type) [CommRing k] (N : ℕ) (T : Scheme.{0}) (f : T ⟶ Sp k)
    (L Q : T.Modules) (s : Fin (N + 1) → (L ⟶ Q)), IsVB L 1 → IsVB Q 1 → Gen s →
    ∃ φ : T ⟶ PSpace k N, φ ≫ PSpace.str k N = f ∧ Rel φ s := by
  intro k _ N T f L Q s hL _ hs
  let H := isCoordFamily hL s hs
  refine ⟨H.toHom f, H.toHom_str f, fun i j W h t => ?_⟩
  have hW : W ≤ good (s i) := h.trans (H.toHom_preimage f i).le
  rw [← ProjSpace.resG_pullRatio (hi := H.le_toHom_preimage f i) hW, H.pullRatio_toHom f i j]
  exact isRatio_ratio hL s i j W hW t
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyConnectedStr
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS

namespace GlobalTheory.CompHS.Modif

theorem geometricallyConnected_str : ∀ (F : Type) [Field F] (Y : Scheme.{0}) (p : Y ⟶ Sp F) (U : Y.Opens) (D : ℕ)
    (M : Modif p U D), SmoothOfRelativeDimension D p → GeometricallyConnected p → Dense (U : Set Y) →
    GeometricallyConnected M.str := by
  intro F _ Y p U D M hs hc hd
  have : Smooth p := SmoothOfRelativeDimension.smooth D p
  have : GeometricallyIntegral p := GlobalTheory.geometricallyIntegral_of_smooth p
  have : Nonempty Y := by
    obtain ⟨x⟩ := (inferInstance : Nonempty (Sp F))
    obtain ⟨y, -⟩ := p.surjective x
    exact ⟨y⟩
  obtain ⟨u, hu⟩ := hd.nonempty
  have : Surjective (U.ι ≫ p) := ⟨fun x => ⟨⟨u, hu⟩, Subsingleton.elim _ _⟩⟩
  have hU : GeometricallyIrreducible (U.ι ≫ p) := inferInstance
  have : IsIso (M.σ ∣_ U) := M.iso
  have e : M.opn.ι ≫ M.str = (M.σ ∣_ U) ≫ (U.ι ≫ p) := by
    show (M.opn.ι ≫ M.σ) ≫ p = _
    rw [← morphismRestrict_ι, Category.assoc]
  have hO : GeometricallyIrreducible (M.opn.ι ≫ M.str) := by
    have sq : IsPullback (M.σ ∣_ U) (M.opn.ι ≫ M.str) (U.ι ≫ p) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [e, Category.comp_id]⟩
    exact MorphismProperty.of_isPullback sq hU
  refine ⟨fun K _ y Z fst snd h => ?_⟩
  have hy : UniversallyOpen y := inferInstance
  have hf : UniversallyOpen fst := MorphismProperty.of_isPullback h.flip hy
  have hdense : Dense ((fst ⁻¹ᵁ M.opn : Z.Opens) : Set Z) := M.dense.preimage fst.isOpenMap
  have hsq : IsPullback (fst ∣_ M.opn) ((fst ⁻¹ᵁ M.opn).ι ≫ snd) (M.opn.ι ≫ M.str) y :=
    (isPullback_morphismRestrict fst M.opn).paste_vert h
  have : IrreducibleSpace (fst ⁻¹ᵁ M.opn) :=
    hO.geometrically_irreducibleSpace y _ _ hsq
  have hirr : IsIrreducible ((fst ⁻¹ᵁ M.opn : Z.Opens) : Set Z) := by
    have := (IrreducibleSpace.isIrreducible_univ (fst ⁻¹ᵁ M.opn)).image _
      (fst ⁻¹ᵁ M.opn).ι.continuous.continuousOn
    rwa [Set.image_univ, Scheme.Opens.range_ι] at this
  have : IrreducibleSpace Z := by
    have hc := hirr.closure
    rw [hdense.closure_eq] at hc
    exact irreducibleSpace_def Z |>.mpr hc
  exact (connectedSpace_iff_univ).mpr (IrreducibleSpace.isIrreducible_univ Z).isConnected

end GlobalTheory.CompHS.Modif
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HTensDiagEqZero
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

namespace GlobalTheory.WeilDiagIso

theorem hTens_diag_eq_zero {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {n m : ℕ}
    (c : A →ₐ[R] A) (JA : Matrix (Fin (n + n)) (Fin (n + n)) A) (JB : Matrix (Fin m) (Fin m) A)
    (x y : Matrix (Fin (n + n)) (Fin m) A)
    (hx : ∀ i j, x (Fin.natAdd n i) j = x (Fin.castAdd n i) j)
    (hy : ∀ i j, y (Fin.natAdd n i) j = y (Fin.castAdd n i) j)
    (h1 : ∀ i k, JA (Fin.castAdd n i) (Fin.natAdd n k) = 0)
    (h2 : ∀ i k, JA (Fin.natAdd n i) (Fin.castAdd n k) = 0)
    (h3 : ∀ i k, JA (Fin.natAdd n i) (Fin.natAdd n k) = - JA (Fin.castAdd n i) (Fin.castAdd n k)) :
    hTens c JA JB x y = 0 := by
  unfold hTens
  simp only [Fin.sum_univ_add, hx, hy, h1, h2, h3, mul_zero, zero_mul, Finset.sum_const_zero,
    add_zero, zero_add, mul_neg, neg_mul, Finset.sum_neg_distrib, add_neg_cancel]

theorem symp_diag_eq_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (nS nT : ℕ) (JT : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E)
    (u u' : Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E)),
    symp (cA σ) ξ (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) (incM F JB)
      (((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) * u)
      (((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) * u') = 0 := by
  intro F E _ _ _ _ _ σ nS nT JT JB ξ u u'
  unfold symp
  rw [hTens_diag_eq_zero]
  · simp
  · intro i j
    simp [Matrix.mul_apply, diagCols, -Fin.natAdd_eq_addNat]
  · intro i j
    simp [Matrix.mul_apply, diagCols, -Fin.natAdd_eq_addNat]
  · intro i k
    simp [incM, GlobalTheory.WeilSchrodinger.DblTargetF.dblG, dbl, -Fin.natAdd_eq_addNat]
  · intro i k
    simp [incM, GlobalTheory.WeilSchrodinger.DblTargetF.dblG, dbl, -Fin.natAdd_eq_addNat]
  · intro i k
    simp [incM, GlobalTheory.WeilSchrodinger.DblTargetF.dblG, dbl, -Fin.natAdd_eq_addNat]

end GlobalTheory.WeilDiagIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorCardKilledByIdealEqAbsNormPowStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_card_killed_by_ideal_eq_absNorm_pow : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : GlobalTheory.UPel.HT.Obj b N s) (𝔟 : Ideal (𝓞 D.F)), 𝔟 ⊔ Ideal.span {(p : 𝓞 D.F)} = ⊤ → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S), Nat.card {y : Over.mk t ⟶ o.A // GlobalTheory.IwLevel.KilledBy (GlobalTheory.IwLevel.htAct o) (𝔟.map (algebraMap (𝓞 D.F) D.O)) y} = Ideal.absNorm 𝔟 ^ (D.m * D.n) := by
  first | (exact @GlobalTheory.HTTorsCount.card_killedBy_eq_absNorm_pow) | (exact GlobalTheory.HTTorsCount.card_killedBy_eq_absNorm_pow) | (intros; apply GlobalTheory.HTTorsCount.card_killedBy_eq_absNorm_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorHeckeMapCompEqForgetLevel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

namespace GlobalTheory.UPel.HT.Hecke

theorem harrisTaylor_heckeMap_comp_forgetLevel_general {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R}
    (g g' : D.La →ₗ[D.O] D.La) (c c' k N : ℕ) (hk : k.Coprime p) (hN3 : 3 ≤ N) (hNp : N.Coprime p)
    (hgg' : ∀ x, g (g' x) = k • x) (hg'g : ∀ x, g' (g x) = k • x) (hcc : c * c' = k ^ 2)
    (hc : (N * k * k).Coprime p)
    {S S₁ S₂ : Scheme.{0}} (s : S ⟶ Sp R) (s₁ : S₁ ⟶ Sp R) (s₂ : S₂ ⟶ Sp R)
    (u : Obj b N s) (u₁ : Obj b (N * k) s₁) (u₂ : Obj b (N * k * k) s₂) (π : S₁ ⟶ S) (π₁ : S₂ ⟶ S₁)
    (h₁ : π₁ ≫ s₁ = s₂)
    (o₂ : Obj b N s₁) (ψ₂ : u₁.A ⟶ o₂.A) (hH₂ : IsHecke g c k N u₁ o₂ ψ₂) (m₂ : ObjMap o₂ u π)
    (o₁ : Obj b (N * k) s₂) (ψ₁ : u₂.A ⟶ o₁.A) (hH₁ : IsHecke g' c' k (N * k) u₂ o₁ ψ₁)
    (m₁ : ObjMap o₁ u₁ π₁) :
    Nonempty (ObjMap (u₂.forget N ⟨k * k, by ring⟩ hc) u (π₁ ≫ π)) := by
  subst h₁
  obtain ⟨o₂', ⟨m⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N S₁ S₂ s₁ π₁ o₂
  obtain ⟨ψ', hψ'⟩ := GlobalTheory.T.isHeckeTranslate_harrisTaylor_pullback_base p D R b g c k N hk hN3 hNp S₁ S₂ s₁ π₁ u₁ o₂ ψ₂ o₁ o₂' hH₂ m₁ m
  obtain ⟨n⟩ := GlobalTheory.T.harrisTaylor_inverse_heckeTranslates_forget_level p D R b g g' c c' k N hk hN3 hNp hgg' hg'g hcc hc S₂ (π₁ ≫ s₁) u₂ o₁ o₂'
    ψ₁ ψ' hH₁ hψ'
  obtain ⟨n₁⟩ := GlobalTheory.UPel.HT.objMap_comp p D R b N _ _ _ _ _ _ _ _ _ _ _ n m
  obtain ⟨n₂⟩ := GlobalTheory.UPel.HT.objMap_comp p D R b N _ _ _ _ _ _ _ _ _ _ _ n₁ m₂
  rw [Category.id_comp] at n₂
  exact ⟨n₂⟩

theorem heckeMap_comp_forget : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (g g' : D.La →ₗ[D.O] D.La) (c c' k N : ℕ), k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x, g (g' x) = k • x) → (∀ x, g' (g x) = k • x) → c * c' = k ^ 2 → ∀ (hc : (N * k * k).Coprime p) (F : RepFam b N) (F₁ : RepFam b (N * k)) (F₂ : RepFam b (N * k * k)) (π : F₁.X ⟶ F.X) (π₁ : F₂.X ⟶ F₁.X), IsHeckeMap g c k N F F₁ π → IsHeckeMap g' c' k (N * k) F₁ F₂ π₁ → Nonempty (ObjMap (F₂.univ.forget N ⟨k * k, by ring⟩ hc) F.univ (π₁ ≫ π)) := by
  intro p _ D R _ b g g' c c' k N hk hN3 hNp hgg' hg'g hcc hc F F₁ F₂ π π₁ hπ hπ₁
  obtain ⟨-, o₂, ψ₂, hH₂, ⟨m₂⟩⟩ := hπ
  obtain ⟨h₁, o₁, ψ₁, hH₁, ⟨m₁⟩⟩ := hπ₁
  exact harrisTaylor_heckeMap_comp_forgetLevel_general g g' c c' k N hk hN3 hNp hgg' hg'g hcc hc F.s F₁.s F₂.s F.univ F₁.univ F₂.univ π π₁ h₁
    o₂ ψ₂ hH₂ m₂ o₁ ψ₁ hH₁ m₁

end GlobalTheory.UPel.HT.Hecke
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorRelDimAndDiagonalIsLineBundleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_relDim_and_diagonal_isLineBundle : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s), SmoothOfRelativeDimension D.g o.A.hom ∧ (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).IsLB := by
  first | exact @GlobalTheory.HTDim.relDim_and_isLB | exact GlobalTheory.HTDim.relDim_and_isLB | (intros; apply GlobalTheory.HTDim.relDim_and_isLB <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasGoodReductionOfUnramifiedAbelianSchemeModel
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GoodDescW
set_option autoImplicit false

section Sq2
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'} {φ : G'.left ⟶ G.left}

noncomputable def sq2 (w : φ ≫ G.hom = G'.hom ≫ f) : (G' ⊗ G').left ⟶ (G ⊗ G).left :=
  (lift (pushPt w (fst G' G')) (pushPt w (snd G' G'))).left

theorem grpSchemeSquareProductMap_comp_fst (w : φ ≫ G.hom = G'.hom ≫ f) : sq2 w ≫ (fst G G).left = (fst G' G').left ≫ φ := by
  rw [sq2, ← Over.comp_left, lift_fst]; rfl

theorem grpSchemeSquareProductMap_comp_snd (w : φ ≫ G.hom = G'.hom ≫ f) : sq2 w ≫ (snd G G).left = (snd G' G').left ≫ φ := by
  rw [sq2, ← Over.comp_left, lift_snd]; rfl

theorem grpSchemeSquareProductMap_eq_tensorHom (w : φ ≫ G.hom = G'.hom ≫ f) {φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} (h : IsSquare φ φ₂) :
    φ₂ = sq2 w :=
  Over.tensorObj_ext _ _ (h.1.trans (grpSchemeSquareProductMap_comp_fst w).symm) (h.2.trans (grpSchemeSquareProductMap_comp_snd w).symm)

theorem isPullback_squareMapOfCompatibleMorphism (w : φ ≫ G.hom = G'.hom ≫ f) (h : IsPullback φ G'.hom G.hom f) :
    IsPullback (sq2 w) (G' ⊗ G').hom (G ⊗ G).hom f :=
  CM.TripleModel.isPullback_tensor h h (grpSchemeSquareProductMap_comp_fst w) (grpSchemeSquareProductMap_comp_snd w)

theorem grpSchemeSquareProductMap_comp {T V : Scheme.{0}} {t : S' ⟶ T} {u : T ⟶ V} {v : S ⟶ V} {H : Over T} {X : Over V}
    {ψ : G'.left ⟶ H.left} {α : H.left ⟶ X.left} {β : G.left ⟶ X.left}
    (w : φ ≫ G.hom = G'.hom ≫ f) (w₁ : ψ ≫ H.hom = G'.hom ≫ t) (w₂ : α ≫ X.hom = H.hom ≫ u)
    (w₃ : β ≫ X.hom = G.hom ≫ v) (h : ψ ≫ α = φ ≫ β) : sq2 w₁ ≫ sq2 w₂ = sq2 w ≫ sq2 w₃ := by
  apply Over.tensorObj_ext
  · change sq2 w₁ ≫ sq2 w₂ ≫ (fst X X).left = sq2 w ≫ sq2 w₃ ≫ (fst X X).left
    rw [grpSchemeSquareProductMap_comp_fst, grpSchemeSquareProductMap_comp_fst, ← Category.assoc, grpSchemeSquareProductMap_comp_fst, ← Category.assoc, grpSchemeSquareProductMap_comp_fst,
      Category.assoc, Category.assoc, h]
  · change sq2 w₁ ≫ sq2 w₂ ≫ (snd X X).left = sq2 w ≫ sq2 w₃ ≫ (snd X X).left
    rw [grpSchemeSquareProductMap_comp_snd, grpSchemeSquareProductMap_comp_snd, ← Category.assoc, grpSchemeSquareProductMap_comp_snd, ← Category.assoc, grpSchemeSquareProductMap_comp_snd,
      Category.assoc, Category.assoc, h]
end Sq2

section Sq
variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

theorem mul_sq (h : IsGrpPullback G' G f φ) (φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left)
    (h₁ : φ₂ ≫ (fst G G).left = (fst G' G').left ≫ φ) (h₂ : φ₂ ≫ (snd G G).left = (snd G' G').left ≫ φ) :
    φ₂ ≫ μ[G].left = μ[G'].left ≫ φ := by
  have e := h.2 _ (fst G' G') (snd G' G') (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G')) rfl rfl
  have e' : (lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))).left = φ₂ :=
    Over.tensorObj_ext _ _
      (by change (lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G')) ≫ fst G G).left = φ₂ ≫ (fst G G).left
          rw [lift_fst]; exact h₁.symm)
      (by change (lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G')) ≫ snd G G).left = φ₂ ≫ (snd G G).left
          rw [lift_snd]; exact h₂.symm)
  rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp, Over.comp_left, e'] at e
  exact e

theorem inv_sq (h : IsGrpPullback G' G f φ) : φ ≫ ι[G].left = ι[G'].left ≫ φ := by
  have e : (pushPt h.1.w ((𝟙 G')⁻¹)).left = ((pushPt h.1.w (𝟙 G'))⁻¹).left :=
    congrArg (fun z => z.left) (map_inv (pushHom h G') (𝟙 G'))
  rw [Hom.inv_def, Hom.inv_def, Over.comp_left] at e
  change (𝟙 G' ≫ ι[G']).left ≫ φ = (𝟙 G'.left ≫ φ) ≫ ι[G].left at e
  simpa using e.symm

theorem one_sq (h : IsGrpPullback G' G f φ) : f ≫ η[G].left = η[G'].left ≫ φ := by
  have e : (pushPt h.1.w (1 : 𝟙_ (Over S') ⟶ G')).left = (1 : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ G).left :=
    congrArg (fun z => z.left) (map_one (pushHom h (𝟙_ (Over S'))))
  rw [Hom.one_def, Hom.one_def, Over.comp_left] at e
  change (toUnit (𝟙_ (Over S')) ≫ η[G']).left ≫ φ = _ at e
  simp only [Over.comp_left, Over.toUnit_left] at e
  simpa using e.symm
end Sq

theorem hasGoodReduction_of_model : ∀ (R K W K' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] [Algebra R W] [Algebra K K'] [Algebra R K'] [IsScalarTower R W K'] [IsScalarTower R K K'], (maximalIdeal R).map (algebraMap R W) = maximalIdeal W → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ e : (Over.pullback (spMap (algebraMap W K'))).obj G ≅ (Over.pullback (spMap (algebraMap K K'))).obj A, IsMonHom e.hom → ∀ (X : Over (Sp R)) (a : A.left ⟶ X.left) (g : G.left ⟶ X.left), IsPullback a A.hom X.hom (spMap (algebraMap R K)) → IsPullback g G.hom X.hom (spMap (algebraMap R W)) → e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K')) ≫ a = pullback.fst G.hom (spMap (algebraMap W K')) ≫ g → HasGoodReduction R K A := by
  intro R K W K' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hmax A _ _ hA G _ hG eI he X a g ha hg hcomp
  have : IsMonHom eI.hom := he
  obtain ⟨hfl, hsu⟩ := GlobalTheory.T.flat_surjective_spMap_of_dvr_alt R K W K' hmax
  have hsq := GlobalTheory.T.spec_fraction_field_isPullback_of_unramified_alt R K W K' hmax
  have : QuasiCompact (spMap (algebraMap R W)) := inferInstance
  have : QuasiCompact (spMap (algebraMap R K)) := inferInstance
  have : IsSchemeTheoreticallyDominant (spMap (algebraMap R K)) := schemeTheoreticallyDominant_fractionField R K
  have := hG.comm
  have := hG.smooth
  have := hG.proper
  have := hG.geomConnected
  have hj : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) (spMap (algebraMap R W)) :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have hXs : Smooth X.hom := MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth) hg.flip hj hG.smooth
  have hXp : IsProper X.hom := GrpFlatDesc.isProper_of_isPullback hg
  have hXc : GeometricallyConnected X.hom := GrpFlatDesc.geometricallyConnected_of_isPullback hg
  have hX2 : Flat (X ⊗ X).hom := inferInstanceAs (Flat (pullback.fst X.hom X.hom ≫ X.hom))

  have hρ : IsGrpPullback ((Over.pullback (spMap (algebraMap W K'))).obj G) G (spMap (algebraMap W K')) (pullback.fst G.hom (spMap (algebraMap W K'))) := isGrpPullback_pullback G (spMap (algebraMap W K'))
  have hψ : IsGrpPullback ((Over.pullback (spMap (algebraMap W K'))).obj G) A (spMap (algebraMap K K')) (eI.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))) :=
    ((isGrpPullback_of_iso eI).comp (isGrpPullback_pullback A (spMap (algebraMap K K')))).congr (Category.id_comp _) rfl
  have hc : (eI.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))) ≫ a = pullback.fst G.hom (spMap (algebraMap W K')) ≫ g := by
    rw [Category.assoc]; exact hcomp

  obtain ⟨hm, hm1, hm2, hm3⟩ := GlobalTheory.T.exists_desc_of_flat_of_schemeTheoreticallyDominant_base (spMap (algebraMap R W)) (spMap (algebraMap R K)) (spMap (algebraMap K K')) (spMap (algebraMap W K')) hsq X.hom (X ⊗ X).hom (G ⊗ G).hom (sq2 hg.w)
    (isPullback_squareMapOfCompatibleMorphism hg.w hg) (A ⊗ A).hom (sq2 ha.w) (isPullback_squareMapOfCompatibleMorphism ha.w ha)
    ((Over.pullback (spMap (algebraMap W K'))).obj G ⊗ (Over.pullback (spMap (algebraMap W K'))).obj G).hom (sq2 hρ.1.w) (sq2 hψ.1.w)
    (isPullback_squareMapOfCompatibleMorphism hρ.1.w hρ.1) (isPullback_squareMapOfCompatibleMorphism hψ.1.w hψ.1)
    (grpSchemeSquareProductMap_comp hρ.1.w hψ.1.w ha.w hg.w hc) (μ[G].left ≫ g) (μ[A].left ≫ a)
    (by rw [Category.assoc, hg.w, ← Category.assoc, Over.w]) (by
      rw [← Category.assoc, mul_sq hρ _ (grpSchemeSquareProductMap_comp_fst _) (grpSchemeSquareProductMap_comp_snd _), Category.assoc, ← hc, ← Category.assoc,
        ← mul_sq hψ _ (grpSchemeSquareProductMap_comp_fst _) (grpSchemeSquareProductMap_comp_snd _), Category.assoc])

  obtain ⟨hi, hi1, hi2, hi3⟩ := GlobalTheory.T.exists_desc_of_flat_of_schemeTheoreticallyDominant_base (spMap (algebraMap R W)) (spMap (algebraMap R K)) (spMap (algebraMap K K')) (spMap (algebraMap W K')) hsq X.hom X.hom G.hom g hg A.hom a ha
    ((Over.pullback (spMap (algebraMap W K'))).obj G).hom (pullback.fst G.hom (spMap (algebraMap W K'))) (eI.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))) hρ.1 hψ.1 hc
    (ι[G].left ≫ g) (ι[A].left ≫ a) (by rw [Category.assoc, hg.w, ← Category.assoc, Over.w]) (by
      rw [← Category.assoc, inv_sq hρ, Category.assoc, ← hc, ← Category.assoc, ← inv_sq hψ, Category.assoc])

  obtain ⟨hu, hu1, hu2, hu3⟩ := GlobalTheory.T.exists_desc_of_flat_of_schemeTheoreticallyDominant_base (spMap (algebraMap R W)) (spMap (algebraMap R K)) (spMap (algebraMap K K')) (spMap (algebraMap W K')) hsq X.hom (𝟙 (Sp R)) (𝟙 (Sp W)) (spMap (algebraMap R W))
    (IsPullback.of_vert_isIso ⟨by simp⟩) (𝟙 (Sp K)) (spMap (algebraMap R K)) (IsPullback.of_vert_isIso ⟨by simp⟩)
    (𝟙 (Sp K')) (spMap (algebraMap W K')) (spMap (algebraMap K K')) (IsPullback.of_vert_isIso ⟨by simp⟩) (IsPullback.of_vert_isIso ⟨by simp⟩) hsq.w.symm
    (η[G].left ≫ g) (η[A].left ≫ a) (by rw [Category.assoc, hg.w, ← Category.assoc, Over.w]; rfl) (by
      rw [← Category.assoc, one_sq hρ, Category.assoc, ← hc, ← Category.assoc, ← one_sq hψ, Category.assoc])

  let m : X ⊗ X ⟶ X := Over.homMk hm hm3
  let i : X ⟶ X := Over.homMk hi hi3
  let e₀ : 𝟙_ (Over (Sp R)) ⟶ X := Over.homMk hu hu3
  obtain ⟨_, hμ, -, -, hcX, -⟩ := GrpFlatDesc.grpObj_of_flat_cover (spMap (algebraMap R W)) X G g hg m i e₀
    (fun φ₂ h₂ => by rw [grpSchemeSquareProductMap_eq_tensorHom hg.w h₂]; exact hm1) hi1 hu1
  have hXab : IsAbelianScheme X := ⟨hcX, hXs, hXp, hXc⟩
  have hAX : IsGrpPullback A X (spMap (algebraMap R K)) a := by
    refine ⟨ha, fun T x y x₀ y₀ hx hy => ?_⟩
    obtain rfl : x₀ = pushPt ha.w x := Over.OverMorphism.ext hx
    obtain rfl : y₀ = pushPt ha.w y := Over.OverMorphism.ext hy
    have := GrpDense.pushPt_mul ha.w (m := μ[X]) (fun φ₂ h₂ => by rw [grpSchemeSquareProductMap_eq_tensorHom ha.w h₂, hμ]; exact hm2) x y
    rw [Hom.mul_def, this]
    rfl
  obtain ⟨e', he', -⟩ := grpPullback_iso (isGrpPullback_pullback X (spMap (algebraMap R K))) hAX
  exact ⟨X, inferInstance, hXab, e', he'⟩

end GlobalTheory.GoodDescW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicDelChernFormOfGramMatrixEqZeroStatement
section
open Set Matrix Filter Topology
open GlobalTheory.HermFrame GlobalTheory.CxForm
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec chernPoly curvPoly)
open scoped ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphicDel_chernFormOfGramMatrix_eq_zero : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (H : V n → Matrix r r ℂ) (s : Set (V n)), IsOpen s → (∀ a b, ContDiffOn ℝ ∞ (fun v => H v a b) s) → (∀ v ∈ s, IsUnit (H v).det) → ∀ (j : ℕ), ∀ v ∈ s, delAt (fun w => (chernAt H w j : Alt n)) v = 0 := by
  first | exact @GlobalTheory.CxForm.ChernDel.delAt_chernAt | exact GlobalTheory.CxForm.ChernDel.delAt_chernAt | (intros; apply GlobalTheory.CxForm.ChernDel.delAt_chernAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperspecialFixesVacuaGoodInertPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperspecial_fixes_vacua_good_inert_place : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → R.toRealDat.ExAt → ∀ t P, Good R.toRealDat t P → conjPl P = P → FixAll R.toRealDat t P := by
  first | exact @GlobalTheory.FixAllGood.fixAll_of_good | exact GlobalTheory.FixAllGood.fixAll_of_good | (intros; apply GlobalTheory.FixAllGood.fixAll_of_good <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaFixedPosValuationDvdUniformiserStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertia_fixed_pos_valuation_dvd_uniformiser : ∀ (R K L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (W : ValuationSubring L), IsAbove R K W.toSubring → ∀ π : R, Irreducible π → ∀ y : L, (∀ τ ∈ inertia K W, τ y = y) → y ∈ W.nonunits → y / algebraMap K L (algebraMap R K π) ∈ W := by
  first | exact @GlobalTheory.InertiaUnram.div_uniformiser_mem | exact GlobalTheory.InertiaUnram.div_uniformiser_mem | (intros; apply GlobalTheory.InertiaUnram.div_uniformiser_mem <;> assumption)
end

