import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalisationLadders.CriterionTruncation
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0176
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0182
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.IsKumCoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0002
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.Bridge
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.PushComparisonBijectiveOfIsClosedEmbedding

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EtaNat
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace GlobalTheory.CompanionTheory.LocBC

variable {R R' : Type} [CommRing R] [CommRing R'] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
  {Φ : PDF R C} {Φ' : PDF R' C'} {σ : R →+* R'} (m : SMor Φ Φ' σ)

section Pts

variable {d : ℕ} (E : Frame Φ d) (E' : Frame Φ' d) (e : E.D ⟶ m.G.obj E'.D)

def Gp : Pt E' ⥤ Pt E where
  obj X := ⟨m.G.obj X.T, e ≫ m.G.map X.s⟩
  map {X Y} f := m.G.map (show X.T ⟶ Y.T from f)
  map_id X := m.G.map_id X.T
  map_comp {X Y Z} f g := m.G.map_comp (show X.T ⟶ Y.T from f) (show Y.T ⟶ Z.T from g)

def mPt (c : R') {a b : IdF Φ.A} {a' b' : IdF Φ'.A} (ha : m.LeC c a a') (hb : m.LeC c b b') :
    CH.Mor (Pt.U E ⋙ sq a b) (Pt.U E' ⋙ sq a' b') σ where
  G := Gp m E E' e
  τ X := (m.sqC c ha hb).τ X.T
  nat {X Y} φ x := (m.sqC c ha hb).nat (show X.T ⟶ Y.T from φ) x

end Pts

section Cuts

variable {d : ℕ} (E : Frame Φ (d + 1)) (E' : Frame Φ' (d + 1)) (e : E.D ⟶ m.G.obj E'.D)
  (he : m.Fr E E' e) (hρ : ∀ T, Function.Injective (m.ρ T))

include he hρ in
theorem cut_mem {X Y : Cut E'} (φ : X ⟶ Y) :
    E.τ 0 ((e ≫ m.G.map X.s) ≫ m.G.map φ.1) (e ≫ m.G.map Y.s) = 0 := by
  apply hρ Y.T
  have h := he 0 (X.s ≫ φ.1) Y.s
  rw [map_zero, Category.assoc, ← m.G.map_comp, h]
  exact φ.2

def G1 : Cut E' ⥤ Cut E where
  obj X := ⟨m.G.obj X.T, e ≫ m.G.map X.s⟩
  map {X Y} φ := ⟨m.G.map φ.1, cut_mem m E E' e he hρ φ⟩
  map_id X := Cut.hom_ext (m.G.map_id X.T)
  map_comp {X Y Z} f g := Cut.hom_ext (m.G.map_comp f.1 g.1)

def m1 : SMor (Cut.Φ1 E) (Cut.Φ1 E') σ where
  G := G1 m E E' e he hρ
  ρ T := m.ρ T.T
  comm T r := m.comm T.T r
  nat {T T'} φ x := m.nat φ.1 x
  mem T x hx := m.mem T.T hx
  dp T k x hx := m.dp T.T k hx

def e1 : (Cut.E1 E).D ⟶ (G1 m E E' e he hρ).obj (Cut.E1 E').D :=
  ⟨e, by
    change E.τ 0 (𝟙 E.D ≫ e) (e ≫ m.G.map (𝟙 E'.D)) = 0
    rw [Category.id_comp, m.G.map_id, Category.comp_id]
    exact E.τ_self 0 e⟩

theorem fr1 : (m1 m E E' e he hρ).Fr (Cut.E1 E) (Cut.E1 E') (e1 m E E' e he hρ) :=
  fun i {T} s s' => he i.succ s.1 s'.1

variable (Q : Poly Φ) (Q' : Poly Φ')

def etaC (X : Pt E') : (Cut.P0 Q).obj ((Gp m E E' e).obj X) ⟶ (G1 m E E' e he hρ).obj ((Cut.P0 Q').obj X) :=
  Cut.adjInv Q _ _ (m.G.map (Q'.j X.T))

theorem j_eta (X : Pt E') : Q.j (m.G.obj X.T) ≫ (etaC m E E' e he hρ Q Q' X).1 = m.G.map (Q'.j X.T) :=
  Cut.adjInv_j Q ((Gp m E E' e).obj X) ((G1 m E E' e he hρ).obj ((Cut.P0 Q').obj X)) (m.G.map (Q'.j X.T))

theorem rho_eta (X : Pt E') :
    m.ρ (Q'.P X.T) ((Φ.A.map (etaC m E E' e he hρ Q Q' X).1).hom (Q.X (m.G.obj X.T))) = Q'.X X.T := by
  have h1 : (Φ.A.map (etaC m E E' e he hρ Q Q' X).1).hom (Q.X (m.G.obj X.T)) =
      E.τ 0 ((e ≫ m.G.map X.s) ≫ m.G.map (Q'.j X.T)) (e ≫ m.G.map (Cut.sec Q' X)) :=
    Q.lift_X (m.G.map (Q'.j X.T)) _ (E.mem 0 _ _)
  rw [h1, Category.assoc, ← m.G.map_comp, he 0 (X.s ≫ Q'.j X.T) (Cut.sec Q' X), Cut.sec_spec, if_pos rfl]

theorem eta_nat {X Y : Pt E'} (φ : X.T ⟶ Y.T) :
    Cut.Pmap (X := (Gp m E E' e).obj X) (Y := (Gp m E E' e).obj Y) Q (m.G.map φ) ≫ (etaC m E E' e he hρ Q Q' Y).1 =
      (etaC m E E' e he hρ Q Q' X).1 ≫ m.G.map (Cut.Pmap (X := X) (Y := Y) Q' φ) := by
  have e1 : Q.j (m.G.obj X.T) ≫ Cut.Pmap (X := (Gp m E E' e).obj X) (Y := (Gp m E E' e).obj Y) Q (m.G.map φ) =
      m.G.map φ ≫ Q.j (m.G.obj Y.T) := Cut.Pmap_j (X := (Gp m E E' e).obj X) (Y := (Gp m E E' e).obj Y) Q (m.G.map φ)
  have e2 : Q'.j X.T ≫ Cut.Pmap (X := X) (Y := Y) Q' φ = φ ≫ Q'.j Y.T := Cut.Pmap_j (X := X) (Y := Y) Q' φ
  have e3 : Q.j (m.G.obj X.T) ≫ Cut.Pmap (X := (Gp m E E' e).obj X) (Y := (Gp m E E' e).obj Y) Q (m.G.map φ) ≫
      (etaC m E E' e he hρ Q Q' Y).1 = Q.j (m.G.obj X.T) ≫ (etaC m E E' e he hρ Q Q' X).1 ≫
        m.G.map (Cut.Pmap (X := X) (Y := Y) Q' φ) := by
    rw [← Category.assoc, e1, Category.assoc, j_eta, ← Category.assoc (Q.j _), j_eta, ← m.G.map_comp, ← m.G.map_comp, e2]
  have e4 := Cut.truncation_hom_ext Q (X := (Gp m E E' e).obj X) (Y := (G1 m E E' e he hρ).obj ((Cut.P0 Q').obj Y))
    (ψ := (Cut.P0 Q).map (show (Gp m E E' e).obj X ⟶ (Gp m E E' e).obj Y from m.G.map φ) ≫ etaC m E E' e he hρ Q Q' Y)
    (ψ' := etaC m E E' e he hρ Q Q' X ≫ (G1 m E E' e he hρ).map ((Cut.P0 Q').map (show X ⟶ Y from φ))) e3
  exact congrArg Subtype.val e4

def eta : Gp m E E' e ⋙ Cut.P0 Q ⟶ Cut.P0 Q' ⋙ G1 m E E' e he hρ where
  app X := etaC m E E' e he hρ Q Q' X
  naturality {X Y} φ := Cut.hom_ext (eta_nat m E E' e he hρ Q Q' (X := X) (Y := Y) φ)

def mP (c : R') {a b : IdF Φ.A} {a' b' : IdF Φ'.A} (ha : m.LeC c a a') (hb : m.LeC c b b') :
    CH.Mor (Cut.P0 Q ⋙ Cut.U E ⋙ sq a b) (Cut.P0 Q' ⋙ Cut.U E' ⋙ sq a' b') σ where
  G := Gp m E E' e
  τ X := ((m.sqC c ha hb).τ (Q'.P X.T)).comp ((sq a b).map (etaC m E E' e he hρ Q Q' X).1).hom
  nat {X Y} φ x := by
    have key : ∀ (φ : X.T ⟶ Y.T) (x : sqM a b (Q.P (m.G.obj X.T))),
        (m.sqC c ha hb).τ (Q'.P Y.T) (((sq a b).map (etaC m E E' e he hρ Q Q' Y).1).hom
          (((sq a b).map (Cut.Pmap (X := (Gp m E E' e).obj X) (Y := (Gp m E E' e).obj Y) Q (m.G.map φ))).hom x)) =
        ((sq a' b').map (Cut.Pmap (X := X) (Y := Y) Q' φ)).hom
          ((m.sqC c ha hb).τ (Q'.P X.T) (((sq a b).map (etaC m E E' e he hρ Q Q' X).1).hom x)) := by
      intro φ x
      rw [← (m.sqC c ha hb).nat]
      congr 1
      have h := eta_nat m E E' e he hρ Q Q' (X := X) (Y := Y) φ
      have h2 := congrArg (fun t => ((sq a b).map t).hom x) h
      simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h2
      exact h2
    exact key φ x

end Cuts

end GlobalTheory.CompanionTheory.LocBC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLineDataTwistingSheaf
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi (LB res)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)
open GlobalTheory.ProjSpace (chart O1 O1_isLB ratioUnit)

noncomputable section

namespace GlobalTheory.CompanionTheory.LineCech

theorem sec_ext {V : Scheme.{0}} {κ : Type} (W : κ → V.Opens) (hW : ⨆ k, W k = ⊤) {s t : Γ(V, ⊤)}
    (h : ∀ k, (V.presheaf.map (homOfLE (le_top : W k ≤ ⊤)).op).hom s =
      (V.presheaf.map (homOfLE (le_top : W k ≤ ⊤)).op).hom t) : s = t :=
  V.sheaf.eq_of_locally_eq' W ⊤ (fun _ => homOfLE le_top) hW.ge s t h

theorem unit_ext {V : Scheme.{0}} {κ : Type} (W : κ → V.Opens) (hW : ⨆ k, W k = ⊤) {s t : Γ(V, ⊤)ˣ}
    (h : ∀ k, res (le_top : W k ≤ ⊤) s = res (le_top : W k ≤ ⊤) t) : s = t :=
  Units.ext (sec_ext W hW fun k => congrArg Units.val (h k))

theorem exists_glue {V : Scheme.{0}} {κ : Type} (W : κ → V.Opens) (hW : ⨆ k, W k = ⊤)
    (hd : ∀ k l, k ≠ l → W k ⊓ W l = ⊥) (t : ∀ k, Γ(V, W k)) :
    ∃ w : Γ(V, ⊤), ∀ k, (V.presheaf.map (homOfLE (le_top : W k ≤ ⊤)).op).hom w = t k := by
  obtain ⟨a, ha, -⟩ := V.sheaf.existsUnique_gluing' W ⊤ (fun _ => homOfLE le_top) hW.ge t (fun k l => by
    by_cases hkl : k = l
    · subst hkl
      rfl
    · have hs : Subsingleton Γ(V, W k ⊓ W l) :=
        CommRingCat.subsingleton_of_isTerminal (V.sheaf.isTerminalOfEqEmpty (hd k l hkl))
      exact @Subsingleton.elim _ hs _ _)
  exact ⟨a, ha⟩

theorem exists_glue_unit {V : Scheme.{0}} {κ : Type} (W : κ → V.Opens) (hW : ⨆ k, W k = ⊤)
    (hd : ∀ k l, k ≠ l → W k ⊓ W l = ⊥) (t : ∀ k, Γ(V, W k)ˣ) :
    ∃ w : Γ(V, ⊤)ˣ, ∀ k, res (le_top : W k ≤ ⊤) w = t k := by
  obtain ⟨a, ha⟩ := exists_glue W hW hd fun k => (t k).val
  obtain ⟨b, hb⟩ := exists_glue W hW hd fun k => (t k).inv
  have hab : a * b = 1 := sec_ext W hW fun k => by
    rw [map_mul, map_one, ha, hb]
    exact (t k).val_inv
  refine ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, fun k => Units.ext (ha k)⟩

def pl {V X : Scheme.{0}} (x : V ⟶ X) {A : X.Opens} {B : V.Opens} (e : B ≤ x ⁻¹ᵁ A) : Γ(X, A)ˣ →* Γ(V, B)ˣ :=
  Units.map (x.appLE A B e).hom.toMonoidHom

theorem pl_congr {V X : Scheme.{0}} {x y : V ⟶ X} (hxy : x = y) {A : X.Opens} {B : V.Opens} (e : B ≤ x ⁻¹ᵁ A)
    (t : Γ(X, A)ˣ) : pl x e t = pl y (hxy ▸ e) t := by
  subst hxy
  rfl

theorem pl_pl {V' V X : Scheme.{0}} (g : V' ⟶ V) (x : V ⟶ X) {A : X.Opens} {B : V.Opens} {B' : V'.Opens}
    (e : B ≤ x ⁻¹ᵁ A) (e' : B' ≤ g ⁻¹ᵁ B) (t : Γ(X, A)ˣ) :
    pl g e' (pl x e t) = pl (g ≫ x) (e'.trans (fun _ hv => e hv)) t := by
  refine Units.ext ?_
  change (g.appLE B B' e').hom ((x.appLE A B e).hom t.val) = ((g ≫ x).appLE A B' _).hom t.val
  rw [← Scheme.Hom.appLE_comp_appLE g x A B B' e e']
  rfl

theorem res_pl {V X : Scheme.{0}} (x : V ⟶ X) {A : X.Opens} {B B' : V.Opens}
    (e : B ≤ x ⁻¹ᵁ A) (h : B' ≤ B) (t : Γ(X, A)ˣ) : res h (pl x e t) = pl x (h.trans e) t := by
  refine Units.ext ?_
  change (V.presheaf.map (homOfLE h).op).hom ((x.appLE A B e).hom t.val) = (x.appLE A B' _).hom t.val
  rw [← Scheme.Hom.appLE_map x e (homOfLE h).op]
  rfl

theorem pl_res {V X : Scheme.{0}} (x : V ⟶ X) {A A' : X.Opens} {B : V.Opens}
    (e : B ≤ x ⁻¹ᵁ A') (h : A' ≤ A) (t : Γ(X, A)ˣ) :
    pl x e (res h t) = pl x (e.trans (fun _ hv => h hv)) t := by
  refine Units.ext ?_
  change (x.appLE A' B e).hom ((X.presheaf.map (homOfLE h).op).hom t.val) = (x.appLE A B _).hom t.val
  rw [← Scheme.Hom.map_appLE x e (homOfLE h).op]
  rfl

theorem res_res {V : Scheme.{0}} {A B C : V.Opens} (h : B ≤ A) (h' : C ≤ B) (t : Γ(V, A)ˣ) :
    res h' (res h t) = res (h'.trans h) t := by
  refine Units.ext ?_
  change (V.presheaf.map (homOfLE h').op).hom ((V.presheaf.map (homOfLE h).op).hom t.val) =
    (V.presheaf.map (homOfLE (h'.trans h)).op).hom t.val
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem res_map_appTop {V' V : Scheme.{0}} (g : V' ⟶ V) {B' : V'.Opens} (t : Γ(V, ⊤)ˣ) :
    res (le_top : B' ≤ ⊤) (Units.map g.appTop.hom.toMonoidHom t) = pl g (A := ⊤) (fun _ _ => trivial) t := by
  refine Units.ext ?_
  rfl

section Cover

variable {X : Scheme.{0}} (L : LB X)

abbrev Yc : Scheme.{0} := ∐ fun i => (L.U i).toScheme

def fc : Yc L ⟶ X := Sigma.desc fun i => (L.U i).ι

theorem ι_fc (i : L.ι) : Sigma.ι (fun i => (L.U i).toScheme) i ≫ fc L = (L.U i).ι := Sigma.ι_desc _ _

variable {L} {V : Scheme.{0}}

def piece (a : V ⟶ Yc L) (i : L.ι) : V.Opens :=
  a ⁻¹ᵁ (Sigma.ι (fun i => (L.U i).toScheme) i).opensRange

theorem piece_le (a : V ⟶ Yc L) (i : L.ι) : piece a i ≤ (a ≫ fc L) ⁻¹ᵁ L.U i := by
  rintro v ⟨y, hy⟩
  change (a ≫ fc L) v ∈ L.U i
  rw [Scheme.Hom.comp_apply, ← hy, ← Scheme.Hom.comp_apply, ι_fc]
  exact y.2

theorem iSup_piece (a : V ⟶ Yc L) : ⨆ i, piece a i = ⊤ := by
  refine top_le_iff.1 fun v _ => ?_
  obtain ⟨i, y, hy⟩ := (sigmaOpenCover fun i => (L.U i).toScheme).exists_eq (a v)
  exact Opens.mem_iSup.2 ⟨i, ⟨y, hy⟩⟩

theorem piece_inf (a : V ⟶ Yc L) {i j : L.ι} (hij : i ≠ j) : piece a i ⊓ piece a j = ⊥ := by
  refine le_bot_iff.1 fun v hv => ?_
  have hd := disjoint_opensRange_sigmaι (fun i => (L.U i).toScheme) i j hij
  exact (Opens.coe_disjoint.2 hd).le_bot ⟨hv.1, hv.2⟩

def W2 (a b : V ⟶ Yc L) (p : L.ι × L.ι) : V.Opens := piece a p.1 ⊓ piece b p.2

theorem iSup_doubleOverlap_eq_top (a b : V ⟶ Yc L) : ⨆ p, W2 a b p = ⊤ := by
  refine top_le_iff.1 fun v _ => ?_
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 ((iSup_piece a).ge (Set.mem_univ v))
  obtain ⟨j, hj⟩ := Opens.mem_iSup.1 ((iSup_piece b).ge (Set.mem_univ v))
  exact Opens.mem_iSup.2 ⟨(i, j), ⟨hi, hj⟩⟩

theorem doubleOverlap_disjoint (a b : V ⟶ Yc L) (p q : L.ι × L.ι) (hpq : p ≠ q) : W2 a b p ⊓ W2 a b q = ⊥ := by
  refine le_bot_iff.1 fun v hv => ?_
  by_cases h1 : p.1 = q.1
  · have h2 : p.2 ≠ q.2 := fun h2 => hpq (Prod.ext h1 h2)
    exact (piece_inf b h2).le ⟨hv.1.2, hv.2.2⟩
  · exact (piece_inf a h1).le ⟨hv.1.1, hv.2.1⟩

theorem doubleOverlap_le_preimage_inter {a b : V ⟶ Yc L} (h : a ≫ fc L = b ≫ fc L) (i j : L.ι) :
    W2 a b (i, j) ≤ (a ≫ fc L) ⁻¹ᵁ (L.U i ⊓ L.U j) := fun v hv =>
  ⟨piece_le a i hv.1, by
    have := piece_le b j hv.2
    rw [← h] at this
    exact this⟩

theorem exists_u {a b : V ⟶ Yc L} (h : a ≫ fc L = b ≫ fc L) :
    ∃ w : Γ(V, ⊤)ˣ, ∀ p : L.ι × L.ι, res (le_top : W2 a b p ≤ ⊤) w =
      pl (a ≫ fc L) (doubleOverlap_le_preimage_inter h p.1 p.2) (L.g p.1 p.2) :=
  exists_glue_unit _ (iSup_doubleOverlap_eq_top a b) (doubleOverlap_disjoint a b) _

def uc {a b : V ⟶ Yc L} (h : a ≫ fc L = b ≫ fc L) : Γ(V, ⊤)ˣ := (exists_u h).choose

theorem uc_spec {a b : V ⟶ Yc L} (h : a ≫ fc L = b ≫ fc L) (i j : L.ι) {B : V.Opens} (hB : B ≤ W2 a b (i, j)) :
    res (le_top : B ≤ ⊤) (uc h) = pl (a ≫ fc L) (hB.trans (doubleOverlap_le_preimage_inter h i j)) (L.g i j) := by
  have e := (exists_u h).choose_spec (i, j)
  rw [← res_res (le_top : W2 a b (i, j) ≤ ⊤) hB]
  change res hB (res le_top (uc h)) = _
  rw [show res (le_top : W2 a b (i, j) ≤ ⊤) (uc h) = _ from e, res_pl]

theorem uc_nat {V' : Scheme.{0}} (g : V' ⟶ V) {a b : V ⟶ Yc L} (h : a ≫ fc L = b ≫ fc L)
    (h' : (g ≫ a) ≫ fc L = (g ≫ b) ≫ fc L) :
    uc h' = Units.map g.appTop.hom.toMonoidHom (uc h) := by
  refine unit_ext _ (iSup_doubleOverlap_eq_top (g ≫ a) (g ≫ b)) fun p => ?_
  obtain ⟨i, j⟩ := p
  have hg : W2 (g ≫ a) (g ≫ b) (i, j) ≤ g ⁻¹ᵁ W2 a b (i, j) := fun v hv => hv
  rw [uc_spec h' i j le_rfl, res_map_appTop, ← pl_res g hg le_top, uc_spec h i j le_rfl, pl_pl,
    pl_congr (Category.assoc g a (fc L))]

theorem uc_coc {a b c : V ⟶ Yc L} (hL : L.IsLB) (h : a ≫ fc L = b ≫ fc L) (h' : b ≫ fc L = c ≫ fc L) :
    uc h * uc h' = uc (h.trans h') := by
  let W3 : L.ι × L.ι × L.ι → V.Opens := fun p => piece a p.1 ⊓ piece b p.2.1 ⊓ piece c p.2.2
  have hW3 : ⨆ p, W3 p = ⊤ := by
    refine top_le_iff.1 fun v _ => ?_
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 ((iSup_piece a).ge (Set.mem_univ v))
    obtain ⟨j, hj⟩ := Opens.mem_iSup.1 ((iSup_piece b).ge (Set.mem_univ v))
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 ((iSup_piece c).ge (Set.mem_univ v))
    exact Opens.mem_iSup.2 ⟨(i, j, k), ⟨⟨hi, hj⟩, hk⟩⟩
  refine unit_ext W3 hW3 fun p => ?_
  obtain ⟨i, j, k⟩ := p
  have h1 : W3 (i, j, k) ≤ W2 a b (i, j) := fun v hv => hv.1
  have h2 : W3 (i, j, k) ≤ W2 b c (j, k) := fun v hv => ⟨hv.1.2, hv.2⟩
  have h3 : W3 (i, j, k) ≤ W2 a c (i, k) := fun v hv => ⟨hv.1.1, hv.2⟩
  have h4 : W3 (i, j, k) ≤ (a ≫ fc L) ⁻¹ᵁ (L.U i ⊓ L.U j ⊓ L.U k) := fun v hv =>
    ⟨doubleOverlap_le_preimage_inter h i j (h1 hv), by
      have := piece_le c k hv.2
      rw [← h', ← h] at this
      exact this⟩
  rw [map_mul, uc_spec h i j h1, uc_spec h' j k h2, uc_spec (h.trans h') i k h3, pl_congr h.symm _ (L.g j k),
    ← pl_res _ h4 (inf_le_left : L.U i ⊓ L.U j ⊓ L.U k ≤ L.U i ⊓ L.U j),
    ← pl_res _ h4 (le_inf (inf_le_left.trans inf_le_right) inf_le_right : L.U i ⊓ L.U j ⊓ L.U k ≤ L.U j ⊓ L.U k),
    ← map_mul, hL.cocycle, pl_res]

end Cover

def toLine {X : Scheme.{0}} (L : LB X) (hL : L.IsLB) : CrystallineSemistableComparison.E.LineData X where
  Y := Yc L
  f := fc L
  sm := IsZariskiLocalAtSource.sigmaDesc (P := @Smooth) fun i => inferInstance
  surj := ⟨fun x => by
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hL.cover.ge (Set.mem_univ x))
    refine ⟨Sigma.ι (fun i => (L.U i).toScheme) i ⟨x, hi⟩, ?_⟩
    rw [← Scheme.Hom.comp_apply, ι_fc]
    rfl⟩
  u _ _ h := uc h
  nat g _ _ h := uc_nat g h _
  coc _ _ _ h h' := uc_coc hL h h'

theorem res_top {V : Scheme.{0}} (t : Γ(V, ⊤)ˣ) : res (le_top : (⊤ : V.Opens) ≤ ⊤) t = t := by
  refine Units.ext ?_
  change (V.presheaf.map (homOfLE le_rfl).op).hom t.val = t.val
  rw [show (homOfLE (le_refl (⊤ : V.Opens))).op = 𝟙 _ from rfl, CategoryTheory.Functor.map_id]
  rfl

theorem uc_of_charts {X V : Scheme.{0}} {L : LB X} {j k : L.ι} (c : V ⟶ (L.U j).toScheme) (d : V ⟶ (L.U k).toScheme)
    (h : (c ≫ Sigma.ι (fun i => (L.U i).toScheme) j) ≫ fc L = (d ≫ Sigma.ι (fun i => (L.U i).toScheme) k) ≫ fc L)
    (e : ⊤ ≤ (c ≫ (L.U j).ι) ⁻¹ᵁ (L.U j ⊓ L.U k)) :
    uc h = pl (c ≫ (L.U j).ι) e (L.g j k) := by
  have hB : (⊤ : V.Opens) ≤ W2 (c ≫ Sigma.ι (fun i => (L.U i).toScheme) j)
      (d ≫ Sigma.ι (fun i => (L.U i).toScheme) k) (j, k) := fun v _ =>
    ⟨⟨c v, rfl⟩, ⟨d v, rfl⟩⟩
  have e1 := uc_spec h j k hB
  rw [res_top] at e1
  rw [e1, pl_congr (show (c ≫ Sigma.ι (fun i => (L.U i).toScheme) j) ≫ fc L = c ≫ (L.U j).ι by
    rw [Category.assoc, ι_fc])]

abbrev pullC {T X : Scheme.{0}} (L : LB X) (i : T ⟶ X) : LB T where
  ι := L.ι
  U j := i ⁻¹ᵁ L.U j
  g j k := pl i (fun _ hv => hv) (L.g j k)

theorem isLB_pullC {T X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (i : T ⟶ X) : (pullC L i).IsLB where
  cover := by
    refine top_le_iff.1 fun v _ => ?_
    obtain ⟨j, hj⟩ := Opens.mem_iSup.1 (hL.cover.ge (Set.mem_univ (i v)))
    exact Opens.mem_iSup.2 ⟨j, hj⟩
  g_self := by
    intro (j : L.ι)
    change res _ (pl i _ (L.g j j)) = 1
    rw [res_pl, ← pl_res i (fun _ hv => hv) (le_inf le_rfl le_rfl : L.U j ≤ L.U j ⊓ L.U j), hL.g_self, map_one]
  cocycle := by
    intro (j : L.ι) (k : L.ι) (l : L.ι)
    change res _ (pl i _ (L.g j k)) * res _ (pl i _ (L.g k l)) = res _ (pl i _ (L.g j l))
    have e : i ⁻¹ᵁ L.U j ⊓ i ⁻¹ᵁ L.U k ⊓ i ⁻¹ᵁ L.U l ≤ i ⁻¹ᵁ (L.U j ⊓ L.U k ⊓ L.U l) := fun _ hv => hv
    rw [res_pl, res_pl, res_pl, ← pl_res i e (inf_le_left : L.U j ⊓ L.U k ⊓ L.U l ≤ L.U j ⊓ L.U k),
      ← pl_res i e (le_inf (inf_le_left.trans inf_le_right) inf_le_right : L.U j ⊓ L.U k ⊓ L.U l ≤ L.U k ⊓ L.U l),
      ← map_mul, hL.cocycle, pl_res]

end GlobalTheory.CompanionTheory.LineCech
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSetOfDetLineEqZero
section
open Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.AdmGL

variable {ι : Type} [Fintype ι] [DecidableEq ι] {a n : ℕ}

theorem isClosed_range_blk (e : Fin a × ι ≃ Fin n) : IsClosed {g | blk e (unblk e g) = g} :=
  isClosed_eq ((continuous_blk e).comp (continuous_unblk e)) continuous_id

theorem blk_unblk_of_mem_closure (e : Fin a × ι ≃ Fin n) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ closure (blkG e)) : blk e (unblk e g) = g :=
  (closure_minimal (fun _ h => ((mem_blkG_iff e).1 h).2) (isClosed_range_blk e)) hg

theorem finite_setOf_det_line_eq_zero {A B : Matrix (Fin n) (Fin n) ℂ} (hA : IsUnit A) :
    {z : ℂ | ((1 - z) • A + z • B).det = 0}.Finite := by
  let P : Polynomial ℂ := Matrix.det ((1 - Polynomial.X : Polynomial ℂ) • A.map Polynomial.C
    + (Polynomial.X : Polynomial ℂ) • B.map Polynomial.C)
  have hev : ∀ z : ℂ, P.eval z = ((1 - z) • A + z • B).det := by
    intro z
    have := RingHom.map_det (Polynomial.evalRingHom z) ((1 - Polynomial.X : Polynomial ℂ) • A.map Polynomial.C
      + (Polynomial.X : Polynomial ℂ) • B.map Polynomial.C)
    simp only [Polynomial.coe_evalRingHom] at this
    rw [this]
    congr 1
    ext i j
    simp
    exact mul_comm _ _
  have hP : P ≠ 0 := by
    intro h
    have := hev 0
    rw [h] at this
    simp only [Polynomial.eval_zero, sub_zero, one_smul, zero_smul, add_zero] at this
    exact ((Matrix.isUnit_iff_isUnit_det A).1 hA).ne_zero this.symm
  refine (P.rootSet_finite ℂ).subset ?_
  intro z hz
  rw [Polynomial.mem_rootSet]
  refine ⟨hP, ?_⟩
  simpa [hev] using hz

theorem isPreconnected_blkG (e : Fin a × ι ≃ Fin n) : IsPreconnected (blkG e) := by
  refine isPreconnected_of_forall_pair ?_
  rintro _ ⟨M, hM, rfl⟩ _ ⟨N, hN, rfl⟩
  have hA : IsUnit (blk e M) := (isUnit_blk_iff e M).2 hM
  have hB : IsUnit (blk e N) := (isUnit_blk_iff e N).2 hN
  set A := blk e M
  set B := blk e N
  let Z : Set ℂ := {z | ((1 - z) • A + z • B).det = 0}
  have hZ : Z.Finite := finite_setOf_det_line_eq_zero hA
  have hconn : IsPathConnected Zᶜ := hZ.countable.isPathConnected_compl_of_one_lt_rank (by
    rw [Complex.rank_real_complex]; norm_num)
  let γ : ℂ → Matrix (Fin n) (Fin n) ℂ := fun z => (1 - z) • A + z • B
  have hγ : Continuous γ := by fun_prop
  refine ⟨γ '' Zᶜ, ?_, ⟨0, ?_, by simp [γ]⟩, ⟨1, ?_, by simp [γ]⟩, hconn.isConnected.isPreconnected.image _ hγ.continuousOn⟩
  · rintro _ ⟨z, hz, rfl⟩
    refine (mem_blkG_iff e).2 ⟨(Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hz), ?_⟩
    have : γ z = blk e ((1 - z) • M + z • N) := by simp [γ, A, B]
    rw [this, unblk_blk]
  · simpa [Z] using ((Matrix.isUnit_iff_isUnit_det A).1 hA).ne_zero
  · simpa [Z] using ((Matrix.isUnit_iff_isUnit_det B).1 hB).ne_zero

theorem blk_inv (e : Fin a × ι ≃ Fin n) {M : Matrix (Fin a) (Fin a) (ι → ℂ)} (hM : IsUnit M) :
    (blk e M)⁻¹ = blk e M⁻¹ := by
  refine Matrix.inv_eq_right_inv ?_
  rw [← blk_mul, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hM), blk_one]

theorem isLinRed_blkG (e : Fin a × ι ≃ Fin n) : GlobalTheory.LinRed.IsLinRed (blkG e) where
  one_mem := ⟨1, isUnit_one, blk_one e⟩
  mul_mem := by
    rintro _ ⟨M, hM, rfl⟩ _ ⟨N, hN, rfl⟩
    exact ⟨M * N, IsUnit.mul hM hN, blk_mul e M N⟩
  isUnit := fun g hg => ((mem_blkG_iff e).1 hg).1
  inv_mem := by
    rintro _ ⟨M, hM, rfl⟩
    refine ⟨M⁻¹, ?_, (blk_inv e hM).symm⟩
    exact (Matrix.isUnit_nonsing_inv_iff).2 hM
  closed := fun g hg hcl => (mem_blkG_iff e).2 ⟨hg, blk_unblk_of_mem_closure e hcl⟩
  connected := isPreconnected_blkG e
  star_mem := by
    rintro _ ⟨M, hM, rfl⟩
    refine ⟨Mᴴ, ?_, blk_conjTranspose e M⟩
    have : IsUnit (star M) := IsUnit.star hM
    exact this

end GlobalTheory.CompanionTheory.AdmGL

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InjectiveResolutionLiftPushforward
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech

namespace GlobalTheory.CompanionTheory.CechLift

theorem exists_injectiveSequence_lift {X Y : TopCat.{0}} (f : X ⟶ Y) {G : AbSheaf Y} {G' : AbSheaf X}
    (φ : G ⟶ (push f).obj G') :
    ∃ α : injectiveSequence G ⟶ (injectiveSequence G').map (push f), α.τ₁ = φ := by
  have hS := injectiveSequence_shortExact G
  have : Mono (injectiveSequence G).f := hS.mono_f
  have : Injective ((push f).obj (injectiveSequence G').X₂) := injective_push f _
  let τ₂ : (injectiveSequence G).X₂ ⟶ (push f).obj (injectiveSequence G').X₂ :=
    Injective.factorThru (φ ≫ (push f).map (injectiveSequence G').f) (injectiveSequence G).f
  have h₁ : (injectiveSequence G).f ≫ τ₂ = φ ≫ (push f).map (injectiveSequence G').f :=
    Injective.comp_factorThru _ _
  have h₀ : (injectiveSequence G).f ≫ τ₂ ≫ (push f).map (injectiveSequence G').g = 0 := by
    rw [← Category.assoc, h₁, Category.assoc, ← Functor.map_comp, (injectiveSequence G').zero,
      Functor.map_zero, comp_zero]
  let τ₃ := hS.gIsCokernel.desc (CokernelCofork.ofπ _ h₀)
  have h₃ : (injectiveSequence G).g ≫ τ₃ = τ₂ ≫ (push f).map (injectiveSequence G').g :=
    Cofork.IsColimit.π_desc hS.gIsCokernel
  exact ⟨{ τ₁ := φ, τ₂ := τ₂, τ₃ := τ₃, comm₁₂ := h₁.symm, comm₂₃ := h₃.symm }, rfl⟩

end GlobalTheory.CompanionTheory.CechLift
end

